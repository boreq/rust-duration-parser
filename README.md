
# Duration parser 
Parses human-readable duration strings. I wrote this crate because:

1. I was bored,
2. the existing ones don't let you configure the units.

I've no idea how to write rust library code though so the interfaces may be
insane.

## Usage

```
[dependencies]
duration_parser = { git = "https://github.com/boreq/rust-duration-parser", tag="v0.0.2" }
```

## Example

```rust
use duration_parser::{Config, Error, Parser, Unit, UnitMagnitude, UnitName, Units};
use std::time::Duration;

fn main() -> Result<(), Error> {
    let parser = Parser::new(Config::new(Units::new(&[
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
    ])?)?);

    println!("1: {:?}", parser.parse("1 hour 2 minutes 3 seconds")?);
    println!("2: {:?}", parser.parse("1hour 2minutes 3seconds")?);
    println!("3: {:?}", parser.parse("1h2m3s")?);

    Ok(())
}
```
