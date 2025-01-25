//! Parses human-readable duration strings. I wrote this crate because a) I was bored b) the
//! existing ones don't let you configure the units c) I want to be able to enforce if spaces occur
//! in the input string.
//!
//! ```
//!use duration_parser::{Config, Error, Parser, Unit, UnitMagnitude, UnitName, Units};
//!use std::time::Duration;
//!
//!fn main() -> Result<(), Error> {
//!    let config = Config::new(Units::new(&[
//!        Unit::new(
//!            UnitMagnitude::new(Duration::from_secs(1))?,
//!            &[
//!                UnitName::new("second".to_string())?,
//!                UnitName::new("seconds".to_string())?,
//!                UnitName::new("s".to_string())?,
//!            ],
//!        )?,
//!        Unit::new(
//!            UnitMagnitude::new(Duration::from_secs(60))?,
//!            &[
//!                UnitName::new("minute".to_string())?,
//!                UnitName::new("minutes".to_string())?,
//!                UnitName::new("m".to_string())?,
//!            ],
//!        )?,
//!        Unit::new(
//!            UnitMagnitude::new(Duration::from_secs(60 * 60))?,
//!            &[
//!                UnitName::new("hour".to_string())?,
//!                UnitName::new("hours".to_string())?,
//!                UnitName::new("h".to_string())?,
//!            ],
//!        )?,
//!    ])?)?
//!    .with_policy_for_spaces_between_value_and_unit(duration_parser::SpacePolicy::AllowOne)
//!    .with_policy_for_spaces_between_components(duration_parser::SpacePolicy::AllowOne);
//!
//!    let parser = Parser::new(config);
//!
//!    println!("1: {:?}", parser.parse("1 hour 2 minutes 3 seconds")?);
//!    println!("2: {:?}", parser.parse("1hour 2minutes 3seconds")?);
//!    println!("3: {:?}", parser.parse("1h2m3s")?);
//!
//!    Ok(())
//!}
//! ```

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
        let config = ParserConfig {
            spaces_between_value_and_unit: self.config.spaces_between_value_and_unit,
            spaces_between_components: self.config.spaces_between_components,
        };

        loop {
            match state.run(&mut result, &mut input, &config)? {
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
        config: &ParserConfig,
    ) -> Result<Option<Box<dyn StateFn>>>;
}

struct ParserConfig {
    spaces_between_value_and_unit: SpacePolicy,
    spaces_between_components: SpacePolicy,
}

struct StateStart {}

impl StateFn for StateStart {
    fn run(
        &self,
        result: &mut ParsingResult,
        _: &mut ParsedInput,
        _: &ParserConfig,
    ) -> Result<Option<Box<dyn StateFn>>> {
        result.components.push(Component::empty());
        return Ok(Some(Box::new(StateValueBeforeDot {})));
    }
}

struct StateValueBeforeDot {}

impl StateFn for StateValueBeforeDot {
    fn run(
        &self,
        result: &mut ParsingResult,
        input: &mut ParsedInput,
        config: &ParserConfig,
    ) -> Result<Option<Box<dyn StateFn>>> {
        match input.peek() {
            Some(ch) => match ch {
                ch if ch.is_numeric() => {
                    let last = &result.components.len() - 1;
                    result.components[last].value += &input.next().unwrap().to_string();
                }
                _ => {
                    return Err(Error::InputMalformed("expected a digit".to_string()));
                }
            },
            None => {
                return Err(Error::InputMalformed(
                    "input ended prematurely while parsing a value".to_string(),
                ))
            }
        }

        loop {
            match input.peek() {
                Some(ch) => match ch {
                    '.' => {
                        let last = &result.components.len() - 1;
                        result.components[last].value += &input.next().unwrap().to_string();
                        return Ok(Some(Box::new(StateValueAfterDot {})));
                    }
                    ch if ch.is_numeric() => {
                        let last = &result.components.len() - 1;
                        result.components[last].value += &input.next().unwrap().to_string();
                    }
                    _ => {
                        input.consume_spaces(config.spaces_between_value_and_unit)?;
                        return Ok(Some(Box::new(StateUnit {})));
                    }
                },
                None => {
                    return Err(Error::InputMalformed(
                        "input ended prematurely while parsing a value".to_string(),
                    ))
                }
            }
        }
    }
}

struct StateValueAfterDot {}

impl StateFn for StateValueAfterDot {
    fn run(
        &self,
        result: &mut ParsingResult,
        input: &mut ParsedInput,
        config: &ParserConfig,
    ) -> Result<Option<Box<dyn StateFn>>> {
        match input.peek() {
            Some(ch) => match ch {
                ch if ch.is_numeric() => {
                    let last = &result.components.len() - 1;
                    result.components[last].value += &input.next().unwrap().to_string();
                }
                _ => {
                    return Err(Error::InputMalformed("expected a digit".to_string()));
                }
            },
            None => {
                return Err(Error::InputMalformed(
                    "input ended prematurely while parsing a value".to_string(),
                ))
            }
        }

        loop {
            match input.peek() {
                Some(ch) => match ch {
                    ch if ch.is_numeric() => {
                        let last = &result.components.len() - 1;
                        result.components[last].value += &input.next().unwrap().to_string();
                    }
                    _ => {
                        input.consume_spaces(config.spaces_between_value_and_unit)?;
                        return Ok(Some(Box::new(StateUnit {})));
                    }
                },
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
        config: &ParserConfig,
    ) -> Result<Option<Box<dyn StateFn>>> {
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
                    input.consume_spaces(config.spaces_between_components)?;
                    return Ok(Some(Box::new(StateValueBeforeDot {})));
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

    fn consume_spaces(&mut self, policy: SpacePolicy) -> Result<()> {
        match policy {
            SpacePolicy::Forbid => match self.peek() {
                Some(ch) => match ch {
                    ' ' => {
                        return Err(Error::InputMalformed(
                            "spaces are not allowed here".to_string(),
                        ))
                    }
                    _ => {
                        return Ok(());
                    }
                },
                None => return Ok(()),
            },
            SpacePolicy::Allow => {
                self.maybe_consume_many_spaces();
                Ok(())
            }
            SpacePolicy::AllowOne => {
                self.maybe_consume_one_space();
                if self.maybe_consume_one_space() {
                    return Err(Error::InputMalformed(
                        "only one space is allowed here".to_string(),
                    ));
                }
                Ok(())
            }
            SpacePolicy::Require => {
                if !self.maybe_consume_one_space() {
                    return Err(Error::InputMalformed("space is required here".to_string()));
                }
                self.maybe_consume_many_spaces();
                Ok(())
            }
            SpacePolicy::RequireOne => {
                if !self.maybe_consume_one_space() {
                    return Err(Error::InputMalformed("space is required here".to_string()));
                }
                if self.maybe_consume_one_space() {
                    return Err(Error::InputMalformed(
                        "only one space is allowed here".to_string(),
                    ));
                }
                Ok(())
            }
        }
    }

    fn maybe_consume_many_spaces(&mut self) {
        loop {
            if !self.maybe_consume_one_space() {
                break;
            }
        }
    }

    fn maybe_consume_one_space(&mut self) -> bool {
        match self.peek() {
            Some(ch) => {
                if ch == ' ' {
                    self.next().unwrap();
                    return true;
                }
                false
            }
            None => false,
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

#[derive(Debug, Clone)]
pub struct Config {
    units: Units,
    spaces_between_value_and_unit: SpacePolicy,
    spaces_between_components: SpacePolicy,
}

impl Config {
    pub fn new(units: Units) -> Result<Config> {
        Ok(Config {
            units,
            spaces_between_value_and_unit: SpacePolicy::Allow,
            spaces_between_components: SpacePolicy::Allow,
        })
    }

    /// Specify how to treat spaces which occur between a value and its unit. Defaults to
    /// [`Allow`] if not set.
    ///
    /// [`Allow`]: SpacePolicy#variant.Allow
    pub fn with_policy_for_spaces_between_value_and_unit(self, policy: SpacePolicy) -> Self {
        let mut config = self.clone();
        config.spaces_between_value_and_unit = policy;
        config
    }

    /// Specify how to treat spaces which occur between value-unit pairs. Defaults to
    /// [`Allow`] if not set.
    ///
    /// [`Allow`]: SpacePolicy#variant.Allow
    pub fn with_policy_for_spaces_between_components(self, policy: SpacePolicy) -> Self {
        let mut config = self.clone();
        config.spaces_between_components = policy;
        config
    }
}

#[derive(Debug, Clone, Copy)]
pub enum SpacePolicy {
    /// No spaces may occur.
    Forbid,

    /// Any number of spaces may occur.
    Allow,

    /// No spaces or one space may occur.
    AllowOne,

    /// Any number of spaces must occur.
    Require,

    /// One space must occur.
    RequireOne,
}

/// Stores units which have unique magnitues and unique names.
#[derive(Debug, Clone)]
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

/// Defines a name of a unit. Valid characters are: letters, `_`.
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

/// Defines the duration represented by a single instance of a particular unit.
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
    /// A list of units has a length of 0. This is nonsense because in this case using the parser
    /// will always fail for all inputs.
    #[error("units are empty")]
    UnitsAreEmpty,

    /// Two of the defined units have an identical name in common which makes it impossible to
    /// determine which one to use.
    #[error("units have the same name, if this isn't a mistake change them to a single unit")]
    UnitsHaveConflictingNames,

    /// Two of the defined units have the same magnitude which is probably a mistake. Make them a
    /// single unit if this is on purpose.
    #[error("units have the same magnitude, if this isn't a mistake change them to a single unit")]
    UnitsHaveConflictingMagnitudes,

    /// The same name was defined twice for a unit.
    #[error("a unit has duplicate names")]
    UnitHasDuplicateNames,

    /// Unit name is an empty string.
    #[error("unit name can't be an empty string")]
    UnitNameIsEmpty,

    /// Unit name contains invalid characters.
    #[error("unit name contains invalid characters")]
    UnitNameContainsInvalidCharacters,

    /// Magnitude of a unit can't be zero. This is nonsense because then the unit is useless and
    /// contributes nothing to the duration.
    #[error("unit magnitude can't be zero")]
    UnitMagnitudeIsZero,

    /// Input is malformed. One of the unit names has invalid characters in it. See [`UnitName`]
    /// for a list of valid characters.
    #[error("invalid unit name in input: '{name}'")]
    InputInvalidUnitName {
        name: String,
        #[source]
        source: Box<Error>,
    },

    // Input is malformed. One of the unit names wasn't defined in the list of units.
    #[error("unknown unit in input: '{name}'")]
    InputUnknownUnit { name: UnitName },

    /// Input is malformed. One of the unit values is malformed.
    #[error("invalid value in input: '{value}'")]
    InputInvalidValue { value: String },

    /// Input is malformed.
    #[error("malformed input: {0}")]
    InputMalformed(String),

    /// The duration value which was created can't be stored as [`std::time::Duration`].
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

            config: &'a Config,
            input: &'a str,

            expected_result: Result<Duration>,
        }

        let config = Config::new(Units::new(&[
            Unit::new(
                UnitMagnitude::new(Duration::from_secs(60 * 60))?,
                &[UnitName::new("hour")?, UnitName::new("hours")?],
            )?,
            Unit::new(
                UnitMagnitude::new(Duration::from_secs(60))?,
                &[UnitName::new("minute")?, UnitName::new("minutes")?],
            )?,
        ])?)?;

        let test_cases = &[
            TestCase {
                name: "empty",

                config: &config,
                input: "",

                expected_result: Err(Error::InputMalformed(
                    "input ended prematurely while parsing a value".to_string(),
                )),
            },
            TestCase {
                name: "value_starts_with_a_dot",

                config: &config,
                input: ".5 minutes",

                expected_result: Err(Error::InputMalformed("expected a digit".to_string())),
            },
            TestCase {
                name: "value_ends_with_a_dot",

                config: &config,
                input: "5. minutes",

                expected_result: Err(Error::InputMalformed("expected a digit".to_string())),
            },
            TestCase {
                name: "valid",

                config: &config,
                input: "1 hour 2.5 minutes",

                expected_result: Ok(Duration::from_secs(3600 + 120 + 30)),
            },
            TestCase {
                name: "insane_space_prefix",

                config: &config,
                input: " 1 hour 2.5 minutes",

                expected_result: Err(Error::InputMalformed("expected a digit".to_string())),
            },
            TestCase {
                name: "insane_space_suffix",

                config: &config,
                input: "1 hour 2.5 minutes ",

                expected_result: Err(Error::InputMalformed(
                    "input ended prematurely while parsing a value".to_string(),
                )),
            },
            TestCase {
                name: "valid_no_spaces",

                config: &config,
                input: "1hour2.5minutes",

                expected_result: Ok(Duration::from_secs(3600 + 120 + 30)),
            },
            TestCase {
                name: "missing_unit",

                config: &config,
                input: "12",

                expected_result: Err(Error::InputMalformed(
                    "input ended prematurely while parsing a value".to_string(),
                )),
            },
        ];

        for test_case in test_cases {
            println!("test case: '{}'", test_case.name);

            let parser = Parser::new(test_case.config.clone());
            let result = parser.parse(test_case.input);
            assert_eq!(result, test_case.expected_result);
        }

        Ok(())
    }

    #[test]
    fn test_parser_spaces_between_value_and_unit() -> std::result::Result<(), anyhow::Error> {
        struct TestCase<'a> {
            policy: Option<SpacePolicy>,

            expected_result_no_space: &'a Result<Duration>,
            expected_result_one_space: &'a Result<Duration>,
            expected_result_multiple_spaces: &'a Result<Duration>,
        }

        let config = Config::new(Units::new(&[
            Unit::new(
                UnitMagnitude::new(Duration::from_secs(60 * 60))?,
                &[UnitName::new("hour")?, UnitName::new("hours")?],
            )?,
            Unit::new(
                UnitMagnitude::new(Duration::from_secs(60))?,
                &[UnitName::new("minute")?, UnitName::new("minutes")?],
            )?,
        ])?)?;

        let result_ok = Ok(Duration::from_secs(3600));

        let test_cases = &[
            TestCase {
                policy: None,
                expected_result_no_space: &result_ok,
                expected_result_one_space: &result_ok,
                expected_result_multiple_spaces: &result_ok,
            },
            TestCase {
                policy: Some(SpacePolicy::Forbid),
                expected_result_no_space: &result_ok,
                expected_result_one_space: &Err(Error::InputMalformed(
                    "spaces are not allowed here".to_string(),
                )),
                expected_result_multiple_spaces: &Err(Error::InputMalformed(
                    "spaces are not allowed here".to_string(),
                )),
            },
            TestCase {
                policy: Some(SpacePolicy::Allow),
                expected_result_no_space: &result_ok,
                expected_result_one_space: &result_ok,
                expected_result_multiple_spaces: &result_ok,
            },
            TestCase {
                policy: Some(SpacePolicy::AllowOne),
                expected_result_no_space: &result_ok,
                expected_result_one_space: &result_ok,
                expected_result_multiple_spaces: &Err(Error::InputMalformed(
                    "only one space is allowed here".to_string(),
                )),
            },
            TestCase {
                policy: Some(SpacePolicy::Require),
                expected_result_no_space: &Err(Error::InputMalformed(
                    "space is required here".to_string(),
                )),
                expected_result_one_space: &result_ok,
                expected_result_multiple_spaces: &result_ok,
            },
            TestCase {
                policy: Some(SpacePolicy::RequireOne),
                expected_result_no_space: &Err(Error::InputMalformed(
                    "space is required here".to_string(),
                )),
                expected_result_one_space: &result_ok,
                expected_result_multiple_spaces: &Err(Error::InputMalformed(
                    "only one space is allowed here".to_string(),
                )),
            },
        ];

        for test_case in test_cases {
            println!("test case: '{:?}'", test_case.policy);

            let config = match test_case.policy {
                Some(policy) => config
                    .clone()
                    .with_policy_for_spaces_between_value_and_unit(policy),
                None => config.clone(),
            };

            let parser = Parser::new(config);

            println!("no space");
            let result = parser.parse("1hour");
            assert_eq!(&result, test_case.expected_result_no_space);
            let result = parser.parse("1.0hour");
            assert_eq!(&result, test_case.expected_result_no_space);

            println!("one space");
            let result = parser.parse("1 hour");
            assert_eq!(&result, test_case.expected_result_one_space);
            let result = parser.parse("1.0 hour");
            assert_eq!(&result, test_case.expected_result_one_space);

            println!("multiple spaces");
            let result = parser.parse("1  hour");
            assert_eq!(&result, test_case.expected_result_multiple_spaces);
            let result = parser.parse("1.0  hour");
            assert_eq!(&result, test_case.expected_result_multiple_spaces);
        }

        Ok(())
    }

    #[test]
    fn test_parser_spaces_between_components() -> std::result::Result<(), anyhow::Error> {
        struct TestCase<'a> {
            policy: Option<SpacePolicy>,

            expected_result_no_space: &'a Result<Duration>,
            expected_result_one_space: &'a Result<Duration>,
            expected_result_multiple_spaces: &'a Result<Duration>,
        }

        let config = Config::new(Units::new(&[
            Unit::new(
                UnitMagnitude::new(Duration::from_secs(60 * 60))?,
                &[UnitName::new("hour")?, UnitName::new("hours")?],
            )?,
            Unit::new(
                UnitMagnitude::new(Duration::from_secs(60))?,
                &[UnitName::new("minute")?, UnitName::new("minutes")?],
            )?,
        ])?)?;

        let result_ok = Ok(Duration::from_secs(3600) + Duration::from_secs(30 * 60));

        let test_cases = &[
            TestCase {
                policy: None,
                expected_result_no_space: &result_ok,
                expected_result_one_space: &result_ok,
                expected_result_multiple_spaces: &result_ok,
            },
            TestCase {
                policy: Some(SpacePolicy::Forbid),
                expected_result_no_space: &result_ok,
                expected_result_one_space: &Err(Error::InputMalformed(
                    "spaces are not allowed here".to_string(),
                )),
                expected_result_multiple_spaces: &Err(Error::InputMalformed(
                    "spaces are not allowed here".to_string(),
                )),
            },
            TestCase {
                policy: Some(SpacePolicy::Allow),
                expected_result_no_space: &result_ok,
                expected_result_one_space: &result_ok,
                expected_result_multiple_spaces: &result_ok,
            },
            TestCase {
                policy: Some(SpacePolicy::AllowOne),
                expected_result_no_space: &result_ok,
                expected_result_one_space: &result_ok,
                expected_result_multiple_spaces: &Err(Error::InputMalformed(
                    "only one space is allowed here".to_string(),
                )),
            },
            TestCase {
                policy: Some(SpacePolicy::Require),
                expected_result_no_space: &Err(Error::InputMalformed(
                    "space is required here".to_string(),
                )),
                expected_result_one_space: &result_ok,
                expected_result_multiple_spaces: &result_ok,
            },
            TestCase {
                policy: Some(SpacePolicy::RequireOne),
                expected_result_no_space: &Err(Error::InputMalformed(
                    "space is required here".to_string(),
                )),
                expected_result_one_space: &result_ok,
                expected_result_multiple_spaces: &Err(Error::InputMalformed(
                    "only one space is allowed here".to_string(),
                )),
            },
        ];

        for test_case in test_cases {
            println!("test case: '{:?}'", test_case.policy);

            let config = match test_case.policy {
                Some(policy) => config
                    .clone()
                    .with_policy_for_spaces_between_components(policy),
                None => config.clone(),
            };

            let parser = Parser::new(config);

            println!("no space");
            let result = parser.parse("1 hour30 minutes");
            assert_eq!(&result, test_case.expected_result_no_space);

            println!("one space");
            let result = parser.parse("1 hour 30 minutes");
            assert_eq!(&result, test_case.expected_result_one_space);

            println!("multiple spaces");
            let result = parser.parse("1 hour  30 minutes");
            assert_eq!(&result, test_case.expected_result_multiple_spaces);
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
