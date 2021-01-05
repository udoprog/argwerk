# argwerk

[![Documentation](https://docs.rs/argwerk/badge.svg)](https://docs.rs/argwerk)
[![Crates](https://img.shields.io/crates/v/argwerk.svg)](https://crates.io/crates/argwerk)
[![Actions Status](https://github.com/udoprog/argwerk/workflows/Rust/badge.svg)](https://github.com/udoprog/argwerk/actions)

Define a simple command-line parser through a declarative macro.

This is **not** intended to be a complete command-line parser library.
Instead this can be used as an alternative quick-and-dirty approach that can
be cheaply incorporated into a tool.

For a more complete command-line parsing library, use [clap].

We provide:
* A dependency-free command-line parsing framework using declarative macros.
* A flexible mechanism for parsing.
* Formatting of decent looking help messages.

We *do not* provide:
* As-close-to correct line wrapping with wide unicode characters as possible
  (see [textwrap]).
* Complex command structures like subcommands.

For how to use, see the documentation of [argwerk::define] and
[argwerk::args].

## Examples

Initially when you're adding arguments to your program you can use
[argwerk::args]. This allows for easily parsing out a handful of optional
parameters.

> This example is available as `simple`:
> ```sh
> cargo run --example simple -- --limit 20
> ```

```rust
let args = argwerk::args! {
    /// A simple tool.
    "tool [-h]" {
        help: bool,
        limit: usize = 10,
    }
    /// The limit of the operation. (default: 10).
    ["-l" | "--limit", int] => {
        limit = str::parse(&int)?;
    }
    /// Print this help.
    ["-h" | "--help"] => {
        println!("{}", HELP);
        help = true;
    }
}?;

if args.help {
    return Ok(());
}

dbg!(args);
```

After a while you might want to graduate to defining a *named* struct
containing the arguments. This can be useful if you want to pass the
arguments around.

> This example is available as `tour`:
> ```sh
> cargo run --example tour -- --help
> ```

```rust
use std::ffi::OsString;

argwerk::define! {
    /// A command touring the capabilities of argwerk.
    #[usage = "tour [-h]"]
    struct Args {
        help: bool,
        #[required = "--file must be specified"]
        file: String,
        input: Option<String>,
        limit: usize = 10,
        positional: Option<(String, Option<String>)>,
        raw: Option<OsString>,
        rest: Vec<String>,
    }
    /// Prints the help.
    ///
    /// This includes:
    ///    * All the available switches.
    ///    * All the available positional arguments.
    ///    * Whatever else the developer decided to put in here! We even support wrapping comments which are overly long.
    ["-h" | "--help"] => {
        println!("{}", Args::help());
        help = true;
    }
    /// Limit the number of things by <n> (default: 10).
    ["--limit" | "-l", n] => {
        limit = str::parse(&n)?;
    }
    /// Write to the file specified by <path>.
    ["--file", path] if !file.is_some() => {
        file = Some(path);
    }
    /// Read from the specified input.
    ["--input", #[option] path] => {
        input = path;
    }
    /// A really long argument that exceeds usage limit and forces the documentation to wrap around with newlines.
    ["--really-really-really-long-argument", thing] => {
    }
    /// A raw argument that passes whatever was passed in from the operating system.
    ["--raw", #[os] arg] => {
        raw = Some(arg);
    }
    /// Takes argument at <foo> and <bar>.
    ///
    ///    * This is an indented message. The first alphanumeric character determines the indentation to use.
    [foo, #[option] bar, #[rest] args] if positional.is_none() => {
        positional = Some((foo, bar));
        rest = args;
    }
}

// Note: we're using `parse` here instead of `args` since it works better
// with the example.
let args = Args::parse(vec!["--file", "foo.txt", "--input", "-"])?;

dbg!(args);
```

### Time and size compared to other projects

argwerk aims to be a lightweight dependency that is fast to compile. This is
how it stacks up to other projects in that regard.

The following table was generated with:

```sh
cargo run --manifest-path tools/builder/Cargo.toml
```

It builds and measures the [projects found here]. These are the results:

| project    | cold build (release)      | rebuild* (release)      | size (release) |
|------------|---------------------------|-------------------------|----------------|
| argh       | 5.0839426s (4.5671066s)   | 405.1443ms (465.8606ms) | 297k (180k)    |
| argwerk    | 1.2646615s (1.2352931s)   | 388.3651ms (471.8421ms) | 265k (185k)    |
| clap**     | 10.6010515s (12.1861838s) | 522.9817ms (759.0176ms) | 2188k (750k)   |

> *: Rebuild was triggered by adding a single newline to `main.rs`.<br>
> **: Clap includes ~38 dependencies.<br>

[projects found here]: https://github.com/udoprog/argwerk/tree/main/projects
[argwerk::define]: https://docs.rs/argwerk/0/argwerk/macro.define.html
[argwerk::args]: https://docs.rs/argwerk/0/argwerk/macro.args.html
[clap]: https://docs.rs/clap
[ok_or_else]: https://doc.rust-lang.org/std/option/enum.Option.html#method.ok_or_else
[OsString]: https://doc.rust-lang.org/std/ffi/struct.OsString.html
[textwrap]: https://docs.rs/textwrap/0.13.2/textwrap/#displayed-width-vs-byte-size

License: MIT/Apache-2.0
