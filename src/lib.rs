use std::fmt::Display;
use std::str::Chars;
use std::{collections::HashSet, time::Duration};

pub struct Parser {
    config: Config,
}

impl Parser {
    pub fn new(config: Config) -> Parser {
        Parser { config }
    }

    pub fn parse(&self, s: &str) -> Result<Duration> {
        let parsing_result = self.parse_internal(s)?;

        let mut result = Duration::ZERO;
        for component in &parsing_result.components {
            let magnitude = self.convert_unit(&component.unit)?;
            let value = self.convert_value(&component.value)?;
            result += match Duration::try_from_secs_f64(magnitude.magnitude.as_secs_f64() * value) {
                Ok(v) => v,
                Err(err) => return Err(Error::ErrorCreatingDuration(err.to_string())),
            }
        }
        Ok(result)
    }

    fn convert_unit(&self, name: &str) -> Result<UnitMagnitude> {
        match UnitName::new(name) {
            Ok(name) => match self.find_magnitude(&name) {
                Some(magnitude) => Ok(magnitude),
                None => Err(Error::InputUnknownUnit { name }),
            },
            Err(err) => Err(Error::InputInvalidUnitName {
                name: name.to_string(),
                source: Box::new(err),
            }),
        }
    }

    fn convert_value(&self, value: &str) -> Result<f64> {
        match value.parse::<f64>() {
            Ok(value) => Ok(value),
            Err(_) => Err(Error::InputInvalidValue {
                value: value.to_string(),
            }),
        }
    }

    fn find_magnitude(&self, unit_name: &UnitName) -> Option<UnitMagnitude> {
        for unit in &self.config.units.units {
            if unit.names.contains(unit_name) {
                return Some(unit.magnitude);
            }
        }
        None
    }

    fn parse_internal(&self, s: &str) -> Result<ParsingResult> {
        let mut result: ParsingResult = ParsingResult { components: vec![] };
        let mut input = ParsedInput::new(s);
        let mut state: Box<dyn StateFn> = Box::new(StateStart {});

        loop {
            match state.run(&mut result, &mut input)? {
                Some(state_fn) => state = state_fn,
                None => return Ok(result),
            }
        }
    }
}

trait StateFn {
    fn run(
        &self,
        result: &mut ParsingResult,
        input: &mut ParsedInput,
    ) -> Result<Option<Box<dyn StateFn>>>;
}

struct StateStart {}

impl StateFn for StateStart {
    fn run(
        &self,
        result: &mut ParsingResult,
        _: &mut ParsedInput,
    ) -> Result<Option<Box<dyn StateFn>>> {
        result.components.push(Component::empty());
        return Ok(Some(Box::new(StateValue {})));
    }
}

struct StateValue {}

impl StateFn for StateValue {
    fn run(
        &self,
        result: &mut ParsingResult,
        input: &mut ParsedInput,
    ) -> Result<Option<Box<dyn StateFn>>> {
        match input.peek() {
            Some(ch) => {
                if ch.is_numeric() || ch == '.' {
                    let last = &result.components.len() - 1;
                    result.components[last].value += &input.next().unwrap().to_string();
                } else {
                    return Err(Error::InputMalformed(
                        "expected a number or a dot".to_string(),
                    ));
                }
            }
            None => {
                return Err(Error::InputMalformed(
                    "input ended prematurely while parsing a value".to_string(),
                ))
            }
        }

        loop {
            match input.peek() {
                Some(ch) => {
                    if ch.is_numeric() || ch == '.' {
                        let last = &result.components.len() - 1;
                        result.components[last].value += &input.next().unwrap().to_string();
                        continue;
                    }
                    input.consume_all_spaces();
                    return Ok(Some(Box::new(StateUnit {})));
                }
                None => {
                    return Err(Error::InputMalformed(
                        "input ended prematurely while parsing a value".to_string(),
                    ))
                }
            }
        }
    }
}

struct StateUnit {}

impl StateFn for StateUnit {
    fn run(
        &self,
        result: &mut ParsingResult,
        input: &mut ParsedInput,
    ) -> Result<Option<Box<dyn StateFn>>> {
        input.consume_all_spaces();

        match input.peek() {
            Some(ch) => {
                if ch.is_alphabetic() || ch == '_' {
                    let last = &result.components.len() - 1;
                    result.components[last].unit += &input.next().unwrap().to_string();
                } else {
                    return Err(Error::InputMalformed(
                        "expected a letter or an underscore".to_string(),
                    ));
                }
            }
            None => {
                return Err(Error::InputMalformed(
                    "input ended prematurely while parsing a unit".to_string(),
                ))
            }
        }

        loop {
            match input.peek() {
                Some(ch) => {
                    if ch.is_alphabetic() || ch == '_' {
                        let last = &result.components.len() - 1;
                        result.components[last].unit += &input.next().unwrap().to_string();
                        continue;
                    }

                    result.components.push(Component::empty());
                    input.consume_all_spaces();
                    return Ok(Some(Box::new(StateValue {})));
                }
                None => return Ok(None),
            }
        }
    }
}

struct ParsedInput<'a> {
    chars: Chars<'a>,
}

impl<'a> ParsedInput<'a> {
    fn new(s: &'a str) -> ParsedInput<'a> {
        return Self { chars: s.chars() };
    }

    fn next(&mut self) -> Option<char> {
        self.chars.next()
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.clone().peekable().next()
    }

    fn consume_all_spaces(&mut self) {
        loop {
            match self.peek() {
                Some(ch) => {
                    if ch == ' ' {
                        self.next().unwrap();
                        continue;
                    } else {
                        return;
                    }
                }
                None => return,
            }
        }
    }
}

struct ParsingResult {
    components: Vec<Component>,
}

struct Component {
    value: String,
    unit: String,
}

impl Component {
    fn empty() -> Self {
        Self {
            value: String::new(),
            unit: String::new(),
        }
    }
}

#[derive(Debug)]
pub struct Config {
    units: Units,
}

impl Config {
    pub fn new(units: Units) -> Result<Config> {
        Ok(Config { units })
    }
}

#[derive(Debug)]
pub struct Units {
    units: Vec<Unit>,
}

impl Units {
    pub fn new(units: &[Unit]) -> Result<Units> {
        if units.is_empty() {
            return Err(Error::UnitsAreEmpty);
        }

        for (i, a) in units.iter().enumerate() {
            for (j, b) in units.iter().enumerate() {
                if i == j {
                    continue;
                }

                if a.has_conflicting_magnitude(b) {
                    return Err(Error::UnitsHaveConflictingMagnitudes);
                }

                if a.has_conflicting_names(b) {
                    return Err(Error::UnitsHaveConflictingNames);
                }
            }
        }

        Ok(Units {
            units: units.to_vec(),
        })
    }
}

#[derive(Debug, Clone)]
pub struct Unit {
    magnitude: UnitMagnitude,
    names: HashSet<UnitName>,
}

impl Unit {
    pub fn new(magnitude: UnitMagnitude, names: &[UnitName]) -> Result<Unit> {
        let names_hashset: HashSet<UnitName> = names.iter().map(|v| v.clone()).collect();

        if names_hashset.len() != names.len() {
            return Err(Error::UnitHasDuplicateNames);
        }

        Ok(Unit {
            magnitude,
            names: names_hashset,
        })
    }

    fn has_conflicting_magnitude(&self, other: &Unit) -> bool {
        self.magnitude == other.magnitude
    }

    fn has_conflicting_names(&self, other: &Unit) -> bool {
        !self.names.is_disjoint(&other.names)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct UnitName {
    name: String,
}

impl UnitName {
    pub fn new(name: impl Into<String>) -> Result<UnitName> {
        let name = name.into();
        if name.is_empty() {
            return Err(Error::UnitNameIsEmpty);
        }

        Ok(UnitName { name })
    }
}

impl Display for UnitName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct UnitMagnitude {
    magnitude: Duration,
}

impl UnitMagnitude {
    pub fn new(magnitude: Duration) -> Result<UnitMagnitude> {
        if magnitude.is_zero() {
            return Err(Error::UnitMagnitudeIsZero);
        }

        Ok(UnitMagnitude { magnitude })
    }
}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(thiserror::Error, Debug, PartialEq, Eq)]
pub enum Error {
    #[error("units are empty")]
    UnitsAreEmpty,

    #[error("units have the same name, if this isn't a mistake change them to a single unit")]
    UnitsHaveConflictingNames,

    #[error("units have the same magnitude, if this isn't a mistake change them to a single unit")]
    UnitsHaveConflictingMagnitudes,

    #[error("a unit has duplicate names")]
    UnitHasDuplicateNames,

    #[error("unit name can't be an empty string")]
    UnitNameIsEmpty,

    #[error("unit magnitude can't be zero")]
    UnitMagnitudeIsZero,

    #[error("invalid unit name in input: '{name}'")]
    InputInvalidUnitName {
        name: String,
        #[source]
        source: Box<Error>,
    },

    #[error("unknown unit in input: '{name}'")]
    InputUnknownUnit { name: UnitName },

    #[error("invalid value in input: '{value}'")]
    InputInvalidValue { value: String },

    #[error("malformed input: {0}")]
    InputMalformed(String),

    #[error("the resulting value is incompatibile with std::time::Duration: {0}")]
    ErrorCreatingDuration(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::distributions::{Alphanumeric, DistString};
    use rand::Rng;
    use std::time::Duration;

    #[test]
    fn test_unit_name_new() -> std::result::Result<(), anyhow::Error> {
        struct TestCase<'a> {
            name: &'a str,
            expected_error: Option<Error>,
        }

        let test_cases = &[
            TestCase {
                name: "",
                expected_error: Some(Error::UnitNameIsEmpty),
            },
            TestCase {
                name: "some_name",
                expected_error: None,
            },
        ];

        for test_case in test_cases {
            println!("test case: '{}'", test_case.name);

            let result = UnitName::new(test_case.name);
            assert_error(&test_case.expected_error, &result);
        }

        Ok(())
    }

    #[test]
    fn test_unit_magnitude_new() -> std::result::Result<(), anyhow::Error> {
        struct TestCase {
            magnitude: Duration,
            expected_error: Option<Error>,
        }

        let test_cases = &[
            TestCase {
                magnitude: Duration::from_secs(0),
                expected_error: Some(Error::UnitMagnitudeIsZero),
            },
            TestCase {
                magnitude: Duration::from_secs(123),
                expected_error: None,
            },
        ];

        for test_case in test_cases {
            println!("test case: '{:?}'", test_case.magnitude);

            let result = UnitMagnitude::new(test_case.magnitude);
            assert_error(&test_case.expected_error, &result);
        }

        Ok(())
    }

    #[test]
    fn test_unit_new() -> std::result::Result<(), anyhow::Error> {
        struct TestCase<'a> {
            name: &'a str,

            magnitude: UnitMagnitude,
            names: &'a [UnitName],

            expected_error: Option<Error>,
        }

        let test_cases = &[
            TestCase {
                name: "valid",
                magnitude: some_unit_magnitude(),
                names: &[some_unit_name()],
                expected_error: None,
            },
            TestCase {
                name: "duplicate_names",
                magnitude: some_unit_magnitude(),
                names: &[UnitName::new("unit_name")?, UnitName::new("unit_name")?],
                expected_error: Some(Error::UnitHasDuplicateNames),
            },
        ];

        for test_case in test_cases {
            println!("test case: '{}'", test_case.name);

            let result = Unit::new(test_case.magnitude, test_case.names);
            assert_error(&test_case.expected_error, &result);
        }

        Ok(())
    }

    #[test]
    fn test_units_new() -> std::result::Result<(), anyhow::Error> {
        struct TestCase<'a> {
            name: &'a str,

            units: &'a [Unit],

            expected_error: Option<Error>,
        }

        let test_cases = &[
            TestCase {
                name: "valid",
                units: &[Unit::new(some_unit_magnitude(), &[some_unit_name()])?],
                expected_error: None,
            },
            TestCase {
                name: "conflicting_magnitudes",
                units: &[
                    Unit::new(some_unit_magnitude(), &[UnitName::new("name")?])?,
                    Unit::new(some_unit_magnitude(), &[UnitName::new("name")?])?,
                ],
                expected_error: Some(Error::UnitsHaveConflictingNames),
            },
            TestCase {
                name: "conflicting_names",
                units: &[
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(1))?,
                        &[some_unit_name()],
                    )?,
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(1))?,
                        &[some_unit_name()],
                    )?,
                ],
                expected_error: Some(Error::UnitsHaveConflictingMagnitudes),
            },
            TestCase {
                name: "empty",
                units: &[],
                expected_error: Some(Error::UnitsAreEmpty),
            },
        ];

        for test_case in test_cases {
            println!("test case: '{}'", test_case.name);

            let result = Units::new(test_case.units);
            assert_error(&test_case.expected_error, &result);
        }

        Ok(())
    }

    #[test]
    fn test_parser() -> std::result::Result<(), anyhow::Error> {
        struct TestCase<'a> {
            name: &'a str,

            units: &'a [Unit],
            input: &'a str,

            expected_result: Result<Duration>,
        }

        let test_cases = &[
            TestCase {
                name: "empty",

                units: &[
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(60 * 60))?,
                        &[UnitName::new("hour")?, UnitName::new("hours")?],
                    )?,
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(60))?,
                        &[UnitName::new("minute")?, UnitName::new("minutes")?],
                    )?,
                ],
                input: "",

                expected_result: Err(Error::InputMalformed(
                    "input ended prematurely while parsing a value".to_string(),
                )),
            },
            TestCase {
                name: "valid",

                units: &[
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(60 * 60))?,
                        &[UnitName::new("hour")?, UnitName::new("hours")?],
                    )?,
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(60))?,
                        &[UnitName::new("minute")?, UnitName::new("minutes")?],
                    )?,
                ],
                input: "1 hour 2.5 minutes",

                expected_result: Ok(Duration::from_secs(3600 + 120 + 30)),
            },
            TestCase {
                name: "insane_space_prefix",

                units: &[
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(60 * 60))?,
                        &[UnitName::new("hour")?, UnitName::new("hours")?],
                    )?,
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(60))?,
                        &[UnitName::new("minute")?, UnitName::new("minutes")?],
                    )?,
                ],
                input: " 1 hour 2.5 minutes",

                expected_result: Err(Error::InputMalformed("expected a number or a dot".to_string())),
            },
            TestCase {
                name: "insane_space_suffix",

                units: &[
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(60 * 60))?,
                        &[UnitName::new("hour")?, UnitName::new("hours")?],
                    )?,
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(60))?,
                        &[UnitName::new("minute")?, UnitName::new("minutes")?],
                    )?,
                ],
                input: "1 hour 2.5 minutes ",

                expected_result: Err(Error::InputMalformed(
                    "input ended prematurely while parsing a value".to_string(),
                )),
            },
            TestCase {
                name: "valid_no_spaces",

                units: &[
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(60 * 60))?,
                        &[UnitName::new("hour")?, UnitName::new("hours")?],
                    )?,
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(60))?,
                        &[UnitName::new("minute")?, UnitName::new("minutes")?],
                    )?,
                ],
                input: "1hour2.5minutes",

                expected_result: Ok(Duration::from_secs(3600 + 120 + 30)),
            },
            TestCase {
                name: "missing_unit",

                units: &[
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(60 * 60))?,
                        &[UnitName::new("hour")?, UnitName::new("hours")?],
                    )?,
                    Unit::new(
                        UnitMagnitude::new(Duration::from_secs(60))?,
                        &[UnitName::new("minute")?, UnitName::new("minutes")?],
                    )?,
                ],
                input: "12",

                expected_result: Err(Error::InputMalformed(
                    "input ended prematurely while parsing a value".to_string(),
                )),
            },
        ];

        for test_case in test_cases {
            println!("test case: '{}'", test_case.name);

            let parser = Parser::new(Config::new(Units::new(test_case.units)?)?);
            let result = parser.parse(test_case.input);
            assert_eq!(result, test_case.expected_result);
        }

        Ok(())
    }

    fn some_unit_name() -> UnitName {
        UnitName::new(some_string()).unwrap()
    }

    fn some_unit_magnitude() -> UnitMagnitude {
        UnitMagnitude::new(Duration::from_secs(
            rand::thread_rng().gen_range(1..10000000),
        ))
        .unwrap()
    }

    fn some_string() -> String {
        Alphanumeric.sample_string(&mut rand::thread_rng(), 10)
    }

    fn assert_error<V>(expected_error: &Option<Error>, result: &Result<V>)
    where
        V: std::fmt::Debug,
    {
        match &expected_error {
            Some(expected_err) => match result {
                Ok(value) => {
                    panic!("expected an error but got a value: {:?}", value);
                }
                Err(err) => {
                    assert_eq!(err, expected_err);
                }
            },
            None => match result {
                Ok(_) => {
                    // ok
                }
                Err(err) => {
                    panic!("error was not expected but got {:?}", err);
                }
            },
        };
    }
}
