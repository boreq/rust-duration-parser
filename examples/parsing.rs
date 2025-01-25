use duration_parser::{Config, Error, Parser, Unit, UnitMagnitude, UnitName, Units};
use std::time::Duration;

fn main() -> Result<(), Error> {
    let config = Config::new(Units::new(&[
        Unit::new(
            UnitMagnitude::new(Duration::from_secs(1))?,
            &[
                UnitName::new("second".to_string())?,
                UnitName::new("seconds".to_string())?,
                UnitName::new("s".to_string())?,
            ],
        )?,
        Unit::new(
            UnitMagnitude::new(Duration::from_secs(60))?,
            &[
                UnitName::new("minute".to_string())?,
                UnitName::new("minutes".to_string())?,
                UnitName::new("m".to_string())?,
            ],
        )?,
        Unit::new(
            UnitMagnitude::new(Duration::from_secs(60 * 60))?,
            &[
                UnitName::new("hour".to_string())?,
                UnitName::new("hours".to_string())?,
                UnitName::new("h".to_string())?,
            ],
        )?,
    ])?)?
    .with_policy_for_spaces_between_value_and_unit(duration_parser::SpacePolicy::AllowOne)
    .with_policy_for_spaces_between_components(duration_parser::SpacePolicy::AllowOne);

    let parser = Parser::new(config);

    println!("1: {:?}", parser.parse("1 hour 2 minutes 3 seconds")?);
    println!("2: {:?}", parser.parse("1hour 2minutes 3seconds")?);
    println!("3: {:?}", parser.parse("1h2m3s")?);

    Ok(())
}
