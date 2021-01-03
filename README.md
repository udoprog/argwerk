# argwerk

[![Documentation](https://docs.rs/argwerk/badge.svg)](https://docs.rs/argwerk)
[![Crates](https://img.shields.io/crates/v/argwerk.svg)](https://crates.io/crates/argwerk)
[![Actions Status](https://github.com/udoprog/argwerk/workflows/Rust/badge.svg)](https://github.com/udoprog/argwerk/actions)

Helper utility for parsing simple commandline arguments.

This is **not** intended to be a complete commandline parser library.
Instead this can be used as an alternative quick-and-dirty approach that can
be cheaply incorporated into a tool.

We provide:
* A dependency-free commandline parsing framework using declarative macros.
  So it's hopefully lightweight and compiles quickly.
* A flexible mechanism for parsing.
* Formatting decent looking help messages.

We specifically do not support:
* As-close-to correct line wrapping with wide unicode characters as possible
  (see [textwrap]).
* Required arguments. If your argument is required, you'll have to
  [ok_or_else] it yourself from an `Option<T>`.
* Complex command structures like subcommands.

For a more complete commandline parsing library, use [clap].

See the documentation for [argwerk::parse!] for how to use.

## Examples

> This is available as a runnable example:
> ```sh
> cargo run --example tour
> ```

```rust
let args = argwerk::parse! {
    /// A command touring the capabilities of argwerk.
    "tour [-h]" {
        help: bool,
        file: Option<String>,
        input: Option<String>,
        limit: usize = 42,
        positional: Option<(String, Option<String>)>,
        rest: Vec<String>,
    }
    /// Prints the help.
    ///
    /// This includes:
    ///    * All the available switches.
    ///    * All the available positional arguments.
    ///    * Whatever else the developer decided to put in here! We even support wrapping comments which are overly long.
    "-h" | "--help" => {
        help = true;
        print_help();
        Ok(())
    }
    /// Limit the number of things by <n>.
    "--limit" | "-l", n => {
        limit = str::parse(&n)?;
        Ok(())
    }
    /// Write to the file specified by <path>.
    "--file", path if !file.is_some() => {
        file = Some(path);
        Ok(())
    }
    /// Read from the specified input.
    "--input", #[option] path => {
        input = path;
        Ok(())
    }
    /// Takes argument at <foo> and <bar>.
    ///
    ///    * This is an indented message. The first alphanumeric character determines the indentation to use.
    [foo, #[option] bar, #[rest] args] if positional.is_none() => {
        positional = Some((foo, bar));
        rest = args;
        Ok(())
    }
}?;

dbg!(args);
```

[ok_or_else]: https://doc.rust-lang.org/std/option/enum.Option.html#method.ok_or_else
[textwrap]: https://docs.rs/textwrap/0.13.2/textwrap/#displayed-width-vs-byte-size
[argwerk::parse!]: https://docs.rs/argwerk/0/argwerk/macro.parse.html
[clap]: https://docs.rs/clap

License: MIT/Apache-2.0
