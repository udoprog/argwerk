//! [![Documentation](https://docs.rs/argwerk/badge.svg)](https://docs.rs/argwerk)
//! [![Crates](https://img.shields.io/crates/v/argwerk.svg)](https://crates.io/crates/argwerk)
//! [![Actions Status](https://github.com/udoprog/argwerk/workflows/Rust/badge.svg)](https://github.com/udoprog/argwerk/actions)
//!
//! Define a simple command-line parser through a declarative macro.
//!
//! This is **not** intended to be a complete command-line parser library.
//! Instead this can be used as an alternative quick-and-dirty approach that can
//! be cheaply incorporated into a tool.
//!
//! For a more complete command-line parsing library, use [clap].
//!
//! We provide:
//! * A dependency-free command-line parsing framework using declarative macros.
//! * A flexible mechanism for parsing.
//! * Formatting of decent looking help messages.
//!
//! We *do not* provide:
//! * As-close-to correct line wrapping with wide unicode characters as possible
//!   (see [textwrap]).
//! * Built-in complex command structures like subcommands (see the
//!   [subcommands] example for how this can be accomplished).
//!
//! For how to use, see the documentation of [argwerk::define] and
//! [argwerk::args].
//!
//! # Examples
//!
//! Initially when you're adding arguments to your program you can use
//! [argwerk::args]. This allows for easily parsing out a handful of optional
//! parameters.
//!
//! > This example is available as `simple`:
//! > ```sh
//! > cargo run --example simple -- --limit 20
//! > ```
//!
//! ```rust
//! # fn main() -> Result<(), argwerk::Error> {
//! let args = argwerk::args! {
//!     /// A simple tool.
//!     "tool [-h]" {
//!         help: bool,
//!         limit: usize = 10,
//!     }
//!     /// The limit of the operation. (default: 10).
//!     ["-l" | "--limit", int] => {
//!         limit = str::parse(&int)?;
//!     }
//!     /// Print this help.
//!     ["-h" | "--help"] => {
//!         println!("{}", HELP);
//!         help = true;
//!     }
//! }?;
//!
//! if args.help {
//!     return Ok(());
//! }
//!
//! dbg!(args);
//! # Ok(()) }
//! ```
//!
//! After a while you might want to graduate to defining a *named* struct
//! containing the arguments. This can be useful if you want to pass the
//! arguments around.
//!
//! > This example is available as `tour`:
//! > ```sh
//! > cargo run --example tour -- --help
//! > ```
//!
//! ```rust
//! use std::ffi::OsString;
//!
//! argwerk::define! {
//!     /// A command touring the capabilities of argwerk.
//!     #[usage = "tour [-h]"]
//!     struct Args {
//!         help: bool,
//!         #[required = "--file must be specified"]
//!         file: String,
//!         input: Option<String>,
//!         limit: usize = 10,
//!         positional: Option<(String, Option<String>)>,
//!         raw: Option<OsString>,
//!         rest: Vec<String>,
//!     }
//!     /// Prints the help.
//!     ///
//!     /// This includes:
//!     ///    * All the available switches.
//!     ///    * All the available positional arguments.
//!     ///    * Whatever else the developer decided to put in here! We even support wrapping comments which are overly long.
//!     ["-h" | "--help"] => {
//!         println!("{}", Args::help());
//!         help = true;
//!     }
//!     /// Limit the number of things by <n> (default: 10).
//!     ["--limit" | "-l", n] => {
//!         limit = str::parse(&n)?;
//!     }
//!     /// Write to the file specified by <path>.
//!     ["--file", path] if !file.is_some() => {
//!         file = Some(path);
//!     }
//!     /// Read from the specified input.
//!     ["--input", #[option] path] => {
//!         input = path;
//!     }
//!     /// A really long argument that exceeds usage limit and forces the documentation to wrap around with newlines.
//!     ["--really-really-really-long-argument", thing] => {
//!     }
//!     /// A raw argument that passes whatever was passed in from the operating system.
//!     ["--raw", #[os] arg] => {
//!         raw = Some(arg);
//!     }
//!     /// Takes argument at <foo> and <bar>.
//!     ///
//!     ///    * This is an indented message. The first alphanumeric character determines the indentation to use.
//!     [foo, #[option] bar, #[rest] args] if positional.is_none() => {
//!         positional = Some((foo, bar));
//!         rest = args;
//!     }
//! }
//!
//! # fn main() -> anyhow::Result<()> {
//! // Note: we're using `parse` here instead of `args` since it works better
//! // with the example.
//! let args = Args::parse(vec!["--file", "foo.txt", "--input", "-"])?;
//!
//! dbg!(args);
//! # Ok(()) }
//! ```
//!
//! ## Time and size compared to other projects
//!
//! argwerk aims to be a lightweight dependency that is fast to compile. This is
//! how it stacks up to other projects in that regard.
//!
//! The following summary was generated from the [projects found here].
//!
//! | project    | cold build (release) | rebuild* (release) | size (release) |
//! |------------|----------------------|--------------------|----------------|
//! | argh** | 5.142723s (4.849361s) | 416.9594ms (468.7003ms) | 297k (180k) |
//! | argwerk | 1.443709s (1.2971457s) | 403.0641ms (514.036ms) | 265k (185k) |
//! | clap*** | 11.9863223s (13.1338799s) | 551.407ms (807.8939ms) | 2188k (750k) |
//! > *: rebuild was triggered by adding a single newline to `main.rs`.<br>
//! > **: argh `0.1.4` including 11 dependencies.<br>
//! > ***: clap `3.0.0-beta.2` including 32 dependencies.<br>
//!
//! You can try and build it yourself with:
//!
//! ```sh
//! cargo run --manifest-path tools/builder/Cargo.toml
//! ```
//!
//! [projects found here]: https://github.com/udoprog/argwerk/tree/main/projects
//! [argwerk::define]: https://docs.rs/argwerk/0/argwerk/macro.define.html
//! [argwerk::args]: https://docs.rs/argwerk/0/argwerk/macro.args.html
//! [clap]: https://docs.rs/clap
//! [ok_or_else]: https://doc.rust-lang.org/std/option/enum.Option.html#method.ok_or_else
//! [OsString]: https://doc.rust-lang.org/std/ffi/struct.OsString.html
//! [textwrap]: https://docs.rs/textwrap/0.13.2/textwrap/#displayed-width-vs-byte-size
//! [subcommands]: https://github.com/udoprog/argwerk/blob/main/examples/subcommands.rs

#![deny(missing_docs)]

use std::fmt;

#[doc(hidden)]
/// Macro helpers. Not intended for public use!
pub mod helpers;

use std::error;

pub use self::helpers::{Help, HelpFormat, InputError, Switch, TryIntoInput};

/// An error raised by argwerk.
#[derive(Debug)]
pub struct Error {
    kind: Box<ErrorKind>,
}

impl Error {
    /// Construct a new error with the given kind.
    pub fn new(kind: ErrorKind) -> Self {
        Self {
            kind: Box::new(kind),
        }
    }

    /// Access the underlying error kind.
    pub fn kind(&self) -> &ErrorKind {
        &self.kind
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind.as_ref() {
            ErrorKind::UnsupportedArgument { argument } => {
                write!(f, "unsupported argument `{}`", argument)
            }
            ErrorKind::UnsupportedSwitch { switch } => {
                write!(f, "unsupported switch `{}`", switch)
            }
            ErrorKind::MissingSwitchArgument { switch, argument } => {
                write!(f, "switch `{}` missing argument `{}`", switch, argument,)
            }
            ErrorKind::MissingPositional { name } => {
                write!(f, "missing argument `{}`", name)
            }
            ErrorKind::MissingRequired { name, reason } => match reason {
                Some(reason) => write!(f, "missing required argument: {}", reason),
                None => write!(f, "missing required argument `{}`", name),
            },
            ErrorKind::InputError { error } => {
                write!(f, "{}", error)
            }
            ErrorKind::Error { name, error } => {
                write!(f, "error in argument `{}`: {}", name, error)
            }
        }
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self.kind.as_ref() {
            ErrorKind::Error { error, .. } => Some(error.as_ref()),
            _ => None,
        }
    }
}

impl From<crate::helpers::InputError> for Error {
    fn from(error: crate::helpers::InputError) -> Self {
        Error::new(ErrorKind::InputError { error })
    }
}

/// The kind of an error.
#[derive(Debug)]
pub enum ErrorKind {
    /// Encountered an argument that was not supported.
    ///
    /// An unsupported argument is triggered when none of the branches in the
    /// parser matches the current agument.
    ///
    /// # Examples
    ///
    /// ```rust
    /// argwerk::define! {
    ///     struct Args { }
    ///     // This errors because `bar` is not a supported switch, nor do we
    ///     // match any positional arguments.
    ///     ["--file", arg] => {}
    /// }
    ///
    /// # fn main() -> Result<(), argwerk::Error> {
    /// let error = Args::parse(vec!["bar"]).unwrap_err();
    ///
    /// assert!(matches!(error.kind(), argwerk::ErrorKind::UnsupportedArgument { .. }));
    /// # Ok(()) }
    /// ```
    UnsupportedArgument {
        /// The name of the unsupported argument.
        argument: Box<str>,
    },
    /// Encountered a switch that was not supported.
    ///
    /// An unsupported switch is caused by the same reason as an unsupported
    /// argument, but it's prefixed with a hyphen `-`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// argwerk::define! {
    ///     #[usage = "command [-h]"]
    ///     struct Args { }
    ///     // This errors because `--path` is not a supported switch. But
    ///     // `"--file"` is.
    ///     ["--file", arg] => {}
    /// }
    ///
    /// # fn main() -> Result<(), argwerk::Error> {
    /// let error = Args::parse(vec!["--path"]).unwrap_err();
    ///
    /// assert!(matches!(error.kind(), argwerk::ErrorKind::UnsupportedSwitch { .. }));
    /// # Ok(()) }
    /// ```
    UnsupportedSwitch {
        /// The name of the unsupported switch.
        switch: Box<str>,
    },
    /// When a parameter to an argument is missing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// argwerk::define! {
    ///     struct Args { }
    ///     // This errors because `--file` requires an argument `path`, but
    ///     // that is not provided.
    ///     ["--file", path] => {}
    /// }
    ///
    /// # fn main() -> Result<(), argwerk::Error> {
    /// let error = Args::parse(vec!["--file"]).unwrap_err();
    ///
    /// assert!(matches!(error.kind(), argwerk::ErrorKind::MissingSwitchArgument { .. }));
    /// # Ok(()) }
    /// ```
    MissingSwitchArgument {
        /// The switch where the argument was missing, like `--file` in `--file
        /// <path>`.
        switch: Box<str>,
        /// The argument that was missing, like `path` in `--file <path>`.
        argument: &'static str,
    },
    /// When a positional argument is missing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// argwerk::define! {
    ///     struct Args { }
    ///     // This errors because `b` is a required argument, but we only have
    ///     // one which matches `a`.
    ///     [a, b] => {}
    /// }
    ///
    /// # fn main() -> Result<(), argwerk::Error> {
    /// let error = Args::parse(vec!["foo"]).unwrap_err();
    ///
    /// assert!(matches!(error.kind(), argwerk::ErrorKind::MissingPositional { .. }));
    /// # Ok(()) }
    /// ```
    MissingPositional {
        /// The name of the argument missing like `path` in `<path>`.
        name: &'static str,
    },
    /// When a positional argument is missing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// argwerk::define! {
    ///     struct Args {
    ///         #[required = "--name must be used"]
    ///         name: String,
    ///     }
    ///     ["--name", n] => {
    ///         name = Some(n);
    ///     }
    ///     [rest] => {}
    /// }
    ///
    /// # fn main() -> Result<(), argwerk::Error> {
    /// let error = Args::parse(vec!["foo"]).unwrap_err();
    ///
    /// assert!(matches!(error.kind(), argwerk::ErrorKind::MissingRequired { name: "name", .. }));
    /// # Ok(()) }
    /// ```
    MissingRequired {
        /// The name of the required variable that is missing.
        name: &'static str,
        /// The reason that the required argument was missing.
        reason: Option<&'static str>,
    },
    /// Failed to parse input as unicode string.
    ///
    /// This is raised in case argwerk needs to treat an input as a string, but
    /// that is not possible.
    ///
    /// This is required if the string needs to be used in a [switch
    /// branch][define#parsing-switches-likes---help].
    InputError {
        /// The underlying error.
        error: crate::helpers::InputError,
    },
    /// When an error has been raised while processing an argument, typically
    /// when something is being parsed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// argwerk::define! {
    ///     #[usage = "command [-h]"]
    ///     struct Args { }
    ///     // This errors because we raise an error in the branch body.
    ///     ["foo"] => {
    ///         Err("something went wrong")
    ///     }
    /// }
    ///
    /// # fn main() -> Result<(), argwerk::Error> {
    /// let error = Args::parse(vec!["foo"]).unwrap_err();
    ///
    /// assert!(matches!(error.kind(), argwerk::ErrorKind::Error { .. }));
    /// # Ok(()) }
    /// ```
    Error {
        /// The name of the switch or positional that couldn't be processed.
        name: Box<str>,
        /// The error that caused the parsing error.
        error: Box<dyn error::Error + Send + Sync + 'static>,
    },
}

/// Parse command-line arguments.
///
/// This will generate an anonymous structure containing the arguments defined
/// which is returned by the macro.
///
/// Each branch is executed when an incoming argument matches and must return a
/// [Result], like `Ok(())`. Error raised in the branch will cause a
/// [ErrorKind::Error] error to be raised associated with that argument
/// with the relevant error attached.
///
/// ## The generated arguments structure
///
/// The first part of the macro defines the state available to the parser. These
/// are field-like declarations which can specify a default initialization
/// value. Fields which do not specify a value will be initialized using
/// [Default::default]. This is the only required component of the macro.
///
/// The macro produces an arguments struct with fields matching this
/// declaration. This can be used to conveniently group and access data
/// populated during argument parsing.
///
/// ```rust
/// argwerk::define! {
///     /// A simple test command.
///     #[usage = "command [-h]"]
///     struct Args {
///         help: bool,
///         limit: usize = 10,
///     }
///     /// Print this help.
///     ["-h" | "--help"] => {
///         help = true;
///     }
///     /// Specify a limit (default: 10).
///     ["--limit", n] => {
///         limit = str::parse(&n)?;
///     }
/// }
///
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = Args::parse(["--limit", "20"].iter().copied())?;
///
/// if args.help {
///     println!("{}", Args::help());
/// }
///
/// assert_eq!(args.help, false);
/// assert_eq!(args.limit, 20);
/// # Ok(()) }
/// ```
///
/// This structure also has two associated functions which can be used to parse
/// input:
///
/// * `args` - Which parses OS arguments using [std::env::args_os].
/// * `parse` - Which can be provided with a custom iterator. This is what's
///   used in almost all the examples.
///
/// When using the custom parse function each item produced by the passed in
/// iterator must implement [TryIntoInput]. This is implemented by types such
/// as: `&str`, `String`, `OsString` and `&OsStr`.
///
/// ```rust
/// argwerk::define! {
///     /// A simple test command.
///     #[usage = "command [-h]"]
///     struct Args {
///         help: bool,
///         limit: usize = 10,
///         positional: Option<(String, String, String)>,
///     }
///     /// Print this help.
///     ["-h" | "--help"] => {
///         help = true;
///     }
///     [a, b, c] => {
///         positional = Some((a, b, c));
///     }
/// }
///
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = Args::args()?;
///
/// if args.help {
///     println!("{}", Args::help());
/// }
///
/// let args = Args::parse(vec!["foo", "bar", "baz"])?;
///
/// assert_eq!(args.positional, Some((String::from("foo"), String::from("bar"), String::from("baz"))));
/// # Ok(()) }
/// ```
///
/// ## Parsing switches likes `--help`
///
/// The basic form of an argument branch one which matches on a string literal.
/// The string literal (e.g. `"--help"`) will then be treated as the switch for
/// the branch. You can specify multiple matches for each branch by separating
/// them with a pipe (`|`).
///
/// It's not necessary that switches start with `-`, but this is assumed for
/// convenience. In particular, argwerk will treat any arguments starting with a
/// hyphen as "switch-like". This is used to determine whether an argument is
/// present if its optional (see later section).
///
/// ```rust
/// argwerk::define! {
///     #[usage = "command [-h]"]
///     struct Args {
///         help: bool
///     }
///     ["-h" | "--help"] => {
///         help = true;
///     }
/// }
///
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = Args::parse(vec!["-h"])?;
///
/// if args.help {
///     println!("{}", Args::help());
/// }
///
/// assert_eq!(args.help, true);
/// # Ok(()) }
/// ```
///
/// ## Parsing positional arguments
///
/// Positional arguments are parsed by specifying a vector of bindings in a
/// branch. Like `[foo, bar]`.
///
/// The following is a basic example. Two arguments `foo` and `bar` are required
/// if the branch matches. If there is no such input an
/// [ErrorKind::MissingPositional] error will be raised.
///
/// ```rust
/// argwerk::define! {
///     #[usage = "command [-h]"]
///     struct Args {
///         positional: Option<(String, String)>,
///     }
///     [foo, bar] if positional.is_none() => {
///         positional = Some((foo, bar));
///     }
/// }
///
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = Args::parse(["a", "b"].iter().copied())?;
///
/// assert_eq!(args.positional, Some((String::from("a"), String::from("b"))));
/// # Ok(()) }
/// ```
///
/// ## Help documentation
///
/// You specify documentation for switches and arguments using doc comments
/// (e.g. `/// Hello World`). These are automatically wrapped to 80 characters.
///
/// Documentation can be formatted with the `help` associated function, which
/// returns a static instance of [Help]. This is also available as the `HELP`
/// static variable inside of match branches. Help formatting can be further
/// customized using [Help::format].
///
/// ```rust
/// argwerk::define! {
///     /// A simple test command.
///     #[usage = "command [-h]"]
///     struct Args {
///         help2: bool,
///     }
///     /// Prints the help.
///     ///
///     /// This includes:
///     ///    * All the available switches.
///     ///    * All the available positional arguments.
///     ///    * Whatever else the developer decided to put in here! We even support wrapping comments which are overly long.
///     ["-h" | "--help"] => {
///         println!("{}", HELP.format().width(120));
///     }
///     ["--help2"] => {
///         help2 = true;
///     }
/// }
///
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = Args::args()?;
///
/// // Another way to access and format help documentation.
/// if args.help2 {
///     println!("{}", Args::help().format().width(120));
/// }
///
/// # Ok(()) }
/// ```
///
/// Invoking this with `-h` would print:
///
/// ```text
/// Usage: command [-h]
/// A simple test command.
///
/// This is nice!
///
/// Options:
///   -h, --help  Prints the help.
///
///               This includes:
///                  * All the available switches.
///                  * All the available positional arguments.
///                  * Whatever else the developer decided to put in here! We even
///                    support wrapping comments which are overly long.
/// ```
///
/// We determine the initial indentation level from the first doc comment.
/// Looking at the code above, this would be the line containing `Prints the
/// help.`. We then wrap additional lines relative to this level of indentation.
///
/// We also determine the individual indentation level of a line by looking at
/// all the non-alphanumerical character that prefixes that line. That's why the
/// "overly long" markdown list bullet above wraps correctly. Instead of
/// wrapping at the `*`, it wraps to the first alphanumeric character after it.
///
/// ## Required arguments using `#[required]`
///
/// You can specify required arguments using the `#[required]` attribute in the
/// field specification. Fields which are marked as `#[required]` have the type
/// [Option\<T\>][Option]. If the field is left as uninitialized (`None`) once
/// all arguments have been parsed will cause an error to be raised. See
/// [ErrorKind::MissingRequired].
///
/// A reason that the argument is required can be optionally provided by doing
/// `#[required = "--name is required"]`.
///
/// # Examples
///
/// ```rust
/// argwerk::define! {
///     struct Args {
///         #[required = "--name must be used"]
///         name: String,
///     }
///     ["--name", n] => {
///         name = Some(n);
///     }
/// }
///
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = Args::parse(vec!["--name", "John"])?;
/// assert_eq!(args.name, "John");
/// # Ok(()) }
/// ```
///
/// ## Raw os arguments with `#[os]`
///
/// In argwerk you can specify that a branch takes a raw argument using the
/// `#[os]` attribute. This value will then be an
/// [OsString][::std::ffi::OsString] and represents exactly what was fed to your
/// program from the operating system.
///
/// ```rust
/// use std::ffi::OsString;
///
/// argwerk::define! {
///     /// A simple test command.
///     #[usage = "command [-h]"]
///     struct Args {
///         raw: Option<OsString>,
///     }
///     ["--raw", #[os] arg] => {
///         raw = Some(arg);
///     }
/// }
///
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = Args::parse(vec![OsString::from("--raw"), OsString::from("baz")])?;
///
/// assert!(args.raw.is_some());
/// # Ok(()) }
/// ```
///
/// ## Capture all available arguments using `#[rest]`
///
/// You can write a branch that receives all available arguments using the
/// `#[rest]` attribute. This can be done both with arguments to switches, and
/// positional arguments.
///
/// You can get the rest of the arguments in their raw form using `#[rest(os)]`.
///
/// The following showcases capturing using a positional argument:
///
/// ```rust
/// argwerk::define! {
///     /// A simple test command.
///     #[usage = "command [-h]"]
///     struct Args {
///         rest: Vec<String>,
///     }
///     [#[rest] args] => {
///         rest = args;
///     }
/// }
///
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = Args::parse(["foo", "bar", "baz"].iter().copied())?;
///
/// assert_eq!(args.rest, &["foo", "bar", "baz"]);
/// # Ok(()) }
/// ```
///
/// And the following through a switch:
///
/// ```rust
/// argwerk::define! {
///     #[usage = "command [-h]"]
///     struct Args {
///         rest: Vec<String>,
///     }
///     ["--test", #[rest] args] => {
///         rest = args;
///     }
/// }
///
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = Args::parse(["--test", "foo", "bar", "baz"].iter().copied())?;
///
/// assert_eq!(args.rest, &["foo", "bar", "baz"]);
/// # Ok(()) }
/// ```
///
/// This showcases getting raw os arguments using `#[rest(os)]`:
///
/// ```rust
/// use std::ffi::{OsString, OsStr};
///
/// argwerk::define! {
///     /// A simple test command.
///     #[usage = "command [-h]"]
///     struct Args {
///         rest: Vec<OsString>,
///     }
///     [#[rest(os)] args] => {
///         rest = args;
///     }
/// }
///
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = Args::parse(["foo", "bar", "baz"].iter().copied())?;
///
/// assert_eq!(args.rest, &[OsStr::new("foo"), OsStr::new("bar"), OsStr::new("baz")]);
/// # Ok(()) }
/// ```
///
/// ## Parsing optional arguments with `#[option]`
///
/// Switches and positional arguments can be marked with the `#[option]`
/// attribute. This will cause the argument to take a value of type
/// `Option<I::Item>` where `I` represents the iterator that is being parsed.
///
/// You can get an optional argument in its raw form using `#[option(os)]`.
///
/// An optional argument parses to `None` if:
/// * There are no more arguments to parse.
/// * The argument is "switch-like" (starts with `-`).
///
/// ```rust
/// use std::ffi::{OsString, OsStr};
///
/// argwerk::define! {
///     /// A simple test command.
///     #[usage = "command [-h]"]
///     struct Args {
///         foo: Option<String>,
///         bar: bool,
///         baz: Option<OsString>,
///     }
///     /// A switch taking an optional argument.
///     ["--foo", #[option] arg] => {
///         foo = arg;
///     }
///     ["--bar"] => {
///         bar = true;
///     }
///     /// A switch taking an optional raw argument.
///     ["--baz", #[option(os)] arg] => {
///         baz = arg;
///     }
/// }
///
/// # fn main() -> Result<(), argwerk::Error> {
/// // Argument exists, but looks like a switch.
/// let args = Args::parse(["--foo", "--bar"].iter().copied())?;
/// assert_eq!(args.foo.as_deref(), None);
/// assert!(args.bar);
///
/// // Argument does not exist.
/// let args = Args::parse(["--foo"].iter().copied())?;
/// assert_eq!(args.foo.as_deref(), None);
/// assert!(!args.bar);
///
/// let args = Args::parse(["--foo", "bar"].iter().copied())?;
/// assert_eq!(args.foo.as_deref(), Some("bar"));
/// assert!(!args.bar);
///
/// let args = Args::parse(["--baz"].iter().copied())?;
/// assert_eq!(args.baz.as_deref(), None);
/// assert!(!args.bar);
///
/// let args = Args::parse(["--baz", "bar"].iter().copied())?;
/// assert_eq!(args.baz.as_deref(), Some(OsStr::new("bar")));
/// assert!(!args.bar);
/// # Ok(()) }
/// ```
#[macro_export]
macro_rules! define {
    (
        $(#[doc = $doc:literal])*
        $(#[usage = $usage:literal])*
        $vis:vis struct $name:ident { $($body:tt)* }
        $($config:tt)*
    ) => {
        $crate::__impl! {
            $(#[doc = $doc])*
            $(#[usage = $usage])*
            $vis struct $name { $($body)* }
            $($config)*
        }

        impl $name {
            /// Return a formatter that formats to the help string at 80
            /// characters witdth of this argument structure.
            $vis fn help() -> &'static $crate::Help {
                &Self::HELP
            }
        }
    };
}

/// Works the same as [define], but immediately parses arguments from
/// [std::env::args] in place.
///
/// # Examples
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::args! {
///     /// A simple test command.
///     "command [-h]" {
///         help: bool,
///         limit: usize = 10,
///     }
///     /// Print this help.
///     ["-h" | "--help"] => {
///         help = true;
///     }
/// }?;
///
/// if args.help {
///     println!("{}", args.help());
/// }
/// # Ok(()) }
/// ```
#[macro_export]
macro_rules! args {
    (
        $(#[doc = $doc:literal])*
        $usage:literal { $($body:tt)* }
        $($config:tt)*
    ) => {{
        $crate::__impl! {
            $(#[doc = $doc])*
            #[usage = $usage]
            struct Args { $($body)* }
            $($config)*
        };

        impl Args {
            /// Return a formatter that formats to the help string at 80
            /// characters witdth of this argument structure.
            fn help(&self) -> &'static $crate::Help {
                &Self::HELP
            }
        }

        Args::args()
    }};
}

/// Internal implementation details of the [args] macro.
#[doc(hidden)]
#[macro_export]
macro_rules! __impl {
    // The guts of the parser.
    (
        $(#[doc = $doc:literal])*
        $(#[usage = $usage:literal])*
        $vis:vis struct $name:ident {
            $( $(#$field_m:tt)* $fvis:vis $field:ident: $ty:ty $(= $expr:expr)? ),* $(,)?
        }
        $($config:tt)*
    ) => {
        #[derive(Debug)]
        $vis struct $name { $($fvis $field: $ty,)* }

        impl $name {
            pub const HELP: $crate::Help = $crate::Help {
                usage: $crate::__impl!(@usage $name, $($usage)*),
                docs: &[$($doc,)*],
                switches: $crate::__impl!(@switches $($config)*)
            };

            /// Parse [std::env::args_os].
            // XXX Clippy gets unaccountably worked up here.
            #[allow(clippy::self_named_constructors)]
            $vis fn args() -> Result<Self, $crate::Error> {
                let mut it = std::env::args_os();
                it.next();
                Self::parse(it)
            }

            /// Parse a custom iterator.
            $vis fn parse<I>(it: I) -> Result<Self, $crate::Error>
            where
                I: IntoIterator,
                I::Item: $crate::TryIntoInput,
            {
                static HELP: &$crate::Help = &$name::HELP;

                let mut it = $crate::helpers::Input::new(it.into_iter());
                $($crate::__impl!(@init $(#$field_m)* $field, $ty $(, $expr)*);)*

                while let Some(__argwerk_item) = it.next()? {
                    $crate::__impl!(@branches __argwerk_item, it, $($config)*);
                }

                Ok(Self {
                    $($field: $crate::__impl!(@assign $(#$field_m)* $field)),*
                })
            }
        }
    };

    // Usage string.
    (@usage $name:ident,) => { stringify!($name) };
    (@usage $name:ident, $usage:literal) => { $usage };

    // Argument formatting.
    (@doc #[rest $($tt:tt)*] $argument:ident) => { concat!("<", stringify!($argument), "..>") };
    (@doc #[option $($tt:tt)*] $argument:ident) => { concat!("[", stringify!($argument), "]") };
    (@doc #[os] $argument:ident) => { concat!("<", stringify!($argument), ">") };
    (@doc $argument:ident) => { concat!("<", stringify!($argument), ">") };

    (@init $field:ident, $ty:ty) => {
        let mut $field: $ty = Default::default();
    };

    (@init #[required $(= $reason:literal)?] $field:ident, $ty:ty) => {
        let mut $field: Option<$ty> = None;
    };

    (@init $field:ident, $ty:ty, $expr:expr) => {
        let mut $field: $ty = $expr;
    };

    (@assign $field:ident) => {
        $field
    };

    (@assign #[required $(= $reason:literal)?] $field:ident) => {
        match $field {
            Some($field) => $field,
            None => return Err($crate::Error::new($crate::ErrorKind::MissingRequired {
                name: stringify!($field),
                reason: $crate::__impl!(@required $($reason)*),
            })),
        }
    };

    // The missing required argument.
    (@required) => { None };
    (@required $reason:literal) => { Some($reason) };

    // Generate help for positional branches.
    (@switch-help
        $($doc:literal)*
        [ $(#$first_m:tt)* $first:ident $(, $(#$rest_m:tt)* $rest:ident)* ]
    ) => {
        $crate::Switch {
            usage: concat!(
                $crate::__impl!(@doc $(#$first_m)* $first),
                $(" ", $crate::__impl!(@doc $(#$rest_m)* $rest),)*
            ),
            docs: &[$($doc,)*]
        }
    };

    // Generate help for matching branches.
    (@switch-help
        $($doc:literal)*
        [$first:literal $(| $rest:literal)* $(, $(#$arg_m:tt)* $arg:ident)*]
    ) => {
        $crate::Switch {
            usage: concat!(
                $first, $(", ", $rest,)*
                $(" ", $crate::__impl!(@doc $(#$arg_m)* $arg),)*
            ),
            docs: &[$($doc,)*]
        }
    };

    // Generate switches help.
    (@switches $( $(#[doc = $doc:literal])* [$($branch:tt)*] $(if $cond:expr)? => $block:block)*) => {
        &[$($crate::__impl!(@switch-help $($doc)* [$($branch)*])),*]
    };

    // Expansion for all branches.
    (@branches
        $switch:ident, $it:ident,
        $(#$_pfx_meta:tt)*
        $(
            [$sw_first_pat:literal $(| $sw_rest_pat:literal)* $(, $(#$sw_arg_m:tt)? $sw_arg:ident)*]
            $(if $sw_cond:expr)?
            => $sw_block:block
            $(#$_sw_meta:tt)*
        )*
        $(
            [$(#$pos_first_m:tt)? $pos_first:ident $(, $(#$pos_rest_m:tt)? $pos_rest:ident)*]
            $(if $pos_cond:expr)?
            => $pos_block:block
            $(#$_pos_meta:tt)*
        )*
    ) => {
        let __argwerk_name = $switch.as_str();

        match __argwerk_name {
            $($sw_first_pat $(| $sw_rest_pat)* $(if $sw_cond)* => {
                $(let $sw_arg = $crate::__var!(switch $switch, $it, $(#$sw_arg_m)* $sw_arg);)*

                if let Err(error) = (|| $crate::helpers::into_result($sw_block))() {
                    return Err(::argwerk::Error::new(::argwerk::ErrorKind::Error {
                        name: __argwerk_name.into(),
                        error
                    }));
                }

                continue;
            })*
            _ => {
                $(if true $(&& $pos_cond)* {
                    let __argwerk_name: Box<str> = __argwerk_name.into();

                    let $pos_first = $crate::__var!(first $it, $(#$pos_first_m)* $switch);
                    $(let $pos_rest = $crate::__var!(pos $it, $(#$pos_rest_m)* $pos_rest);)*

                    if let Err(error) = (|| $crate::helpers::into_result($pos_block))() {
                        return Err(::argwerk::Error::new(::argwerk::ErrorKind::Error {
                            name: __argwerk_name,
                            error
                        }));
                    }

                    continue;
                })*
            },
        }

        if __argwerk_name.starts_with('-') {
            return Err(::argwerk::Error::new(::argwerk::ErrorKind::UnsupportedSwitch {
                switch: __argwerk_name.into()
            }));
        } else {
            return Err(::argwerk::Error::new(::argwerk::ErrorKind::UnsupportedArgument {
                argument: __argwerk_name.into()
            }));
        }
    };
}

/// Helper to decode a variable.
#[doc(hidden)]
#[macro_export]
macro_rules! __var {
    (var $var:ident) => { $var };
    (var (os) $var:ident) => { ::std::ffi::OsString::from($var) };

    (rest $it:ident) => { $it.rest()? };
    (rest (os) $it:ident) => { $it.rest_os() };

    (next_unless_switch $it:ident) => { $it.next_unless_switch()? };
    (next_unless_switch (os) $it:ident) => { $it.next_unless_switch_os() };

    // Various ways of parsing the first argument.
    (first $it:ident, #[rest $($tt:tt)*] $var:ident) => {
        Some($crate::__var!(var $($tt)* $var))
            .into_iter()
            .chain($crate::__var!(rest $($tt)* $it))
            .collect::<Vec<_>>();
    };
    (first $it:ident, #[option $($tt:tt)*] $var:ident) => {
        Some($crate::__var!(var $($tt)* $var))
    };
    (first $it:ident, #[os] $var:ident) => {
        Some(::std::ffi::OsString::from($var))
    };
    (first $it:ident, $var:ident) => {
        $var
    };

    // Parse the rest of the available arguments.
    (pos $it:ident, #[rest $($tt:tt)*] $_:ident) => {
        $crate::__var!(rest $($tt)* $it)
    };
    // Parse an optional argument.
    (pos $it:ident, #[option $($tt:tt)*] $_:ident) => {
        $crate::__var!(next_unless_switch $($tt)* $it)
    };
    // Parse an os string argument.
    (pos $it:ident, #[os] $_:ident) => {
        match $it.next_os() {
            Some($var) => $var,
            None => {
                return Err(::argwerk::Error::new(
                    ::argwerk::ErrorKind::MissingPositional {
                        name: stringify!($var),
                    },
                ))
            }
        }
    };

    // Parse the rest of the arguments.
    (pos $it:ident, $var:ident) => {
        match $it.next()? {
            Some($var) => $var,
            None => {
                return Err(::argwerk::Error::new(
                    ::argwerk::ErrorKind::MissingPositional {
                        name: stringify!($var),
                    },
                ))
            }
        }
    };

    // Parse the rest of the available arguments.
    (switch $switch:ident, $it:ident, #[rest $($tt:tt)*] $arg:ident) => {
        $crate::__var!(rest $($tt)* $it)
    };
    // Parse an optional argument.
    (switch $switch:ident, $it:ident, #[option $($tt:tt)*] $arg:ident) => {
        $crate::__var!(next_unless_switch $($tt)* $it)
    };

    // Parse next #[os] string argument.
    (switch $switch:ident, $it:ident, #[os] $var:ident) => {
        match $it.next_os() {
            Some($var) => $var,
            None => {
                return Err(::argwerk::Error::new(
                    ::argwerk::ErrorKind::MissingSwitchArgument {
                        switch: $switch.into(),
                        argument: stringify!($var),
                    },
                ))
            }
        }
    };

    // Parse next argument.
    (switch $switch:ident, $it:ident, $var:ident) => {
        match $it.next()? {
            Some($var) => $var,
            None => {
                return Err(::argwerk::Error::new(
                    ::argwerk::ErrorKind::MissingSwitchArgument {
                        switch: $switch.into(),
                        argument: stringify!($var),
                    },
                ))
            }
        }
    };
}
