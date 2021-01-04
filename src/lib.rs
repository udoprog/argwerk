//! [![Documentation](https://docs.rs/argwerk/badge.svg)](https://docs.rs/argwerk)
//! [![Crates](https://img.shields.io/crates/v/argwerk.svg)](https://crates.io/crates/argwerk)
//! [![Actions Status](https://github.com/udoprog/argwerk/workflows/Rust/badge.svg)](https://github.com/udoprog/argwerk/actions)
//!
//! Simple command-line parser through a declarative macro.
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
//! * Required switches and arguments. If your switch is required, you'll have
//!   to [ok_or_else] it yourself from an `Option<T>`.
//! * Complex command structures like subcommands.
//! * Parsing into [OsString]s. The default parser will panic in case not valid
//!   unicode is passed into it in accordance with [std::env::args].
//!
//! For how to use, see the documentation of [argwerk::parse!].
//!
//! # Examples
//!
//! > This is available as a runnable example:
//! > ```sh
//! > cargo run --example tour
//! > ```
//!
//! ```rust
//! # fn main() -> Result<(), argwerk::Error> {
//! let args = argwerk::parse! {
//!     /// A command touring the capabilities of argwerk.
//!     "tour [-h]" {
//!         help: bool,
//!         file: Option<String>,
//!         input: Option<String>,
//!         limit: usize = 10,
//!         positional: Option<(String, Option<String>)>,
//!         rest: Vec<String>,
//!     }
//!     /// Prints the help.
//!     ///
//!     /// This includes:
//!     ///    * All the available switches.
//!     ///    * All the available positional arguments.
//!     ///    * Whatever else the developer decided to put in here! We even support wrapping comments which are overly long.
//!     ["-h" | "--help"] => {
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
//!     /// Takes argument at <foo> and <bar>.
//!     ///
//!     ///    * This is an indented message. The first alphanumeric character determines the indentation to use.
//!     [foo, #[option] bar, #[rest] args] if positional.is_none() => {
//!         positional = Some((foo, bar));
//!         rest = args;
//!     }
//! }?;
//!
//! if args.help {
//!     println!("{}", args.help());
//! }
//!
//! dbg!(args);
//! # Ok(()) }
//! ```
//!
//! [argwerk::parse!]: https://docs.rs/argwerk/0/argwerk/macro.parse.html
//! [clap]: https://docs.rs/clap
//! [ok_or_else]: https://doc.rust-lang.org/std/option/enum.Option.html#method.ok_or_else
//! [OsString]: https://doc.rust-lang.org/std/ffi/struct.OsString.html
//! [textwrap]: https://docs.rs/textwrap/0.13.2/textwrap/#displayed-width-vs-byte-size

#![deny(missing_docs)]

use std::fmt;

#[doc(hidden)]
/// Macro helpers. Not intended for public use!
pub mod helpers;

use std::error;

pub use self::helpers::{Help, HelpFormat, Switch};

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
    /// # fn main() -> Result<(), argwerk::Error> {
    /// let error = argwerk::parse! {
    ///     vec!["bar"] => "command [-h]" { }
    ///     // This errors because `bar` is not a supported switch, nor do we
    ///     // match any positional arguments.
    ///     ["--file", arg] => {}
    /// }.unwrap_err();
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
    /// # fn main() -> Result<(), argwerk::Error> {
    /// let error = argwerk::parse! {
    ///     vec!["--path"] => "command [-h]" { }
    ///     // This errors because `--path` is not a supported switch. But
    ///     // `"--file"` is.
    ///     ["--file", arg] => {}
    /// }.unwrap_err();
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
    /// # fn main() -> Result<(), argwerk::Error> {
    /// let error = argwerk::parse! {
    ///     vec!["--file"] => "command [-h]" { }
    ///     // This errors because `--file` requires an argument `path`, but
    ///     // that is not provided.
    ///     ["--file", path] => {}
    /// }.unwrap_err();
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
    /// # fn main() -> Result<(), argwerk::Error> {
    /// let error = argwerk::parse! {
    ///     vec!["foo"] => "command [-h]" { }
    ///     // This errors because `b` is a required argument, but we only have
    ///     // one which matches `a`.
    ///     [a, b] => {}
    /// }.unwrap_err();
    ///
    /// assert!(matches!(error.kind(), argwerk::ErrorKind::MissingPositional { .. }));
    /// # Ok(()) }
    /// ```
    MissingPositional {
        /// The name of the argument missing like `path` in `<path>`.
        name: &'static str,
    },
    /// When an error has been raised while processing an argument, typically
    /// when something is being parsed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # fn main() -> Result<(), argwerk::Error> {
    /// let error = argwerk::parse! {
    ///     vec!["foo"] => "command [-h]" { }
    ///     // This errors because we raise an error in the branch body.
    ///     ["foo"] => {
    ///         Err("something went wrong")
    ///     }
    /// }.unwrap_err();
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
/// The [parse] macro can be invoked in two ways.
///
/// Using `std::env::args()` to get arguments from the environment:
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
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
///
/// Or explicitly specifying an iterator to use with `<into_iter> => <config>`.
/// This works with anything that can be converted into an iterator using
/// [IntoIterator] where its items implements [AsRef\<str\>][AsRef].
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     vec!["foo", "bar", "baz"] =>
///     /// A simple test command.
///     "command [-h]" {
///         help: bool,
///         positional: Option<(&'static str, &'static str, &'static str)>,
///     }
///     [a, b, c] => {
///         positional = Some((a, b, c));
///     }
/// }?;
///
/// assert_eq!(args.positional, Some(("foo", "bar", "baz")));
/// # Ok(()) }
/// ```
///
/// ## Args structure
///
/// The first part of the [parse] macro defines the state available to the
/// parser. These are field-like declarations which can specify a default value.
/// Fields which do not specify an initialization value will be initialized
/// through [Default::default]. This is the only required component of the
/// macro.
///
/// The macro returns an anonymous `Args` struct with fields matching this
/// declaration. This can be used to conveniently group and access data
/// populated during argument parsing.
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     ["--limit", "20"].iter().copied() =>
///     /// A simple test command.
///     "command [-h]" {
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
/// }?;
///
/// if args.help {
///     println!("{}", args.help());
/// }
///
/// assert_eq!(args.help, false);
/// assert_eq!(args.limit, 20);
/// # Ok(()) }
/// ```
///
/// ## Parsing switches
///
/// The basic form of an argument branch parsing a switch is one which matches
/// on a string literal. The string literal (e.g. `"--help"`) will then be
/// treated as the switch for the branch. You can specify multiple matches for
/// each branch by separating them with a pipe (`|`).
///
/// > Note: it's not necessary that switches start with `-`, but this is assumed
/// > for convenience.
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     vec!["-h"] =>
///     "command [-h]" { help: bool }
///     ["-h" | "--help"] => {
///         help = true;
///     }
/// }?;
///
/// if args.help {
///     println!("{}", args.help());
/// }
///
/// assert_eq!(args.help, true);
/// # Ok(()) }
/// ```
///
/// ## Parsing positional arguments
///
/// Positional arguments are parsed by specifying a vector of bindings in a
/// branch. Like `[foo, bar, baz]`.
///
/// The following is a basic example. Both `foo` and `bar` are required if the
/// branch matches.
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     ["a", "b"].iter().copied().map(String::from) =>
///     "command [-h]" { positional: Option<(String, String)>, }
///     [foo, bar] if positional.is_none() => {
///         positional = Some((foo, bar));
///     }
/// }?;
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
/// returns a static instance of [Help]. This can be further customized using
/// [Help::format].
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     /// A simple test command.
///     "command [-h]" {
///         help: bool,
///     }
///     /// Prints the help.
///     ///
///     /// This includes:
///     ///    * All the available switches.
///     ///    * All the available positional arguments.
///     ///    * Whatever else the developer decided to put in here! We even support wrapping comments which are overly long.
///     ["-h" | "--help"] => {
///         help = true;
///     }
/// }?;
///
/// if args.help {
///     println!("{}", args.help().format().width(120));
/// }
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
/// ## Capture all available arguments using `#[rest]`
///
/// You can write a branch that receives all available arguments using the
/// `#[rest]` attribute. This can be done both with arguments to switches, and
/// positional arguments.
///
/// The following showcases capturing using a positional argument:
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     vec!["foo", "bar", "baz"].into_iter().map(String::from) =>
///     /// A simple test command.
///     "command [-h]" {
///         rest: Vec<String>,
///     }
///     [#[rest] args] => {
///         rest = args;
///     }
/// }?;
///
/// assert_eq!(args.rest, &["foo", "bar", "baz"]);
/// # Ok(()) }
/// ```
///
/// And the following through a switch:
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     vec!["--test", "foo", "bar", "baz"].into_iter().map(String::from) =>
///     "command [-h]" { rest: Vec<String>, }
///     ["--test", #[rest] args] => {
///         rest = args;
///     }
/// }?;
///
/// assert_eq!(args.rest, &["foo", "bar", "baz"]);
/// # Ok(()) }
/// ```
///
/// ## Parsing optional arguments with `#[option]`
///
/// Switches and positional arguments can be marked with the `#[option]`
/// attribute. This will cause the argument to take a value of type
/// `Option<I::Item>` where `I` represents the iterator that is being parsed.
///
/// An optional argument parses to `None` if:
/// * There are no more arguments to parse.
/// * The argument is a switch (starts with `-`).
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let parser = |iter: &[&str]| argwerk::parse! {
///     iter.iter().copied().map(String::from) =>
///     /// A simple test command.
///     "command [-h]" {
///         foo: Option<String>,
///         bar: bool,
///     }
///     /// A switch taking an optional argument.
///     ["--foo", #[option] arg] => {
///         foo = arg;
///     }
///     ["--bar"] => {
///         bar = true;
///     }
/// };
///
/// // Argument exists, but looks like a switch.
/// let args = parser(&["--foo", "--bar"])?;
/// assert_eq!(args.foo.as_deref(), None);
/// assert!(args.bar);
///
/// // Argument does not exist.
/// let args = parser(&["--foo"])?;
/// assert_eq!(args.foo.as_deref(), None);
/// assert!(!args.bar);
///
/// let args = parser(&["--foo", "bar"])?;
/// assert_eq!(args.foo.as_deref(), Some("bar"));
/// assert!(!args.bar);
/// # Ok(()) }
/// ```
#[macro_export]
macro_rules! parse {
    // Parse from a custom iterator.
    (
        $it:expr => $($config:tt)*
    ) => {{
        let mut __argwerk_it = ::std::iter::IntoIterator::into_iter($it);
        $crate::__internal!(__argwerk_it, $($config)*)
    }};

    // Parse from `std::env::args()`.
    (
        $($config:tt)*
    ) => {{
        let mut __argwerk_it = ::std::env::args();
        __argwerk_it.next();
        $crate::__internal!(__argwerk_it, $($config)*)
    }};
}

/// Internal implementation details of the [parse] macro.
#[doc(hidden)]
#[macro_export]
macro_rules! __internal {
    // The guts of the parser.
    (
        $it:ident,
        $(#[doc = $doc:literal])*
        $usage:literal {
            $($field:ident : $ty:ty $(= $expr:expr)?),* $(,)?
        }
        $($config:tt)*
    ) => {{
        let mut $it = $it.peekable();

        let mut parser = || {
            $($crate::__internal!(@field $field, $ty $(= $expr)*);)*

            while let Some(__argwerk_arg) = $it.next() {
                $crate::__internal!(@branches __argwerk_arg, $it, $($config)*);

                if $crate::__internal!(@is-switch &__argwerk_arg) {
                    return Err(::argwerk::Error::new(::argwerk::ErrorKind::UnsupportedSwitch {
                        switch: __argwerk_arg.into()
                    }));
                } else {
                    return Err(::argwerk::Error::new(::argwerk::ErrorKind::UnsupportedArgument {
                        argument: __argwerk_arg.into()
                    }));
                }
            }

            #[derive(Debug)]
            struct Args { $($field: $ty,)* }

            impl Args {
                /// Return a formatter that formats to the help string at 80
                /// characters witdth of this argument structure.
                pub fn help(&self) -> &'static $crate::Help {
                    &$crate::Help {
                        usage: $usage,
                        docs: &[$($doc,)*],
                        switches: $crate::__internal!(@switch-help $($config)*)
                    }
                }
            }

            Ok(Args { $($field,)* })
        };

        parser()
    }};

    // Parse the rest of the available arguments.
    (@doc #[rest] $argument:ident) => {
        concat!("<", stringify!($argument), "..>");
    };

    // Parse an optional argument.
    (@doc #[option] $argument:ident) => {
        concat!("[", stringify!($argument), "]");
    };

    // Parse as its argument.
    (@doc $argument:ident) => {
        concat!("<", stringify!($argument), ">");
    };

    // Parse the rest of the available arguments.
    (@positional #[rest] $it:ident, $arg:ident) => {
        (&mut $it).map(String::from).collect::<Vec<String>>();
    };

    // Parse an optional argument.
    (@positional #[option] $it:ident, $arg:ident) => {
        match $it.peek() {
            Some(n) => if !$crate::__internal!(@is-switch n) {
                $it.next()
            } else {
                None
            }
            None => None,
        }
    };

    // Parse the rest of the arguments.
    (@positional $it:ident, $arg:ident) => {
        match $it.next() {
            Some($arg) => $arg,
            None => return Err(
                ::argwerk::Error::new(
                    ::argwerk::ErrorKind::MissingPositional {
                        name: stringify!($arg),
                    }
                )
            )
        }
    };

    // Parse the rest of the available arguments.
    (@first-positional #[rest] $argument:ident, $it:ident) => {
        Some($argument).into_iter().chain(&mut $it).collect::<Vec<_>>();
    };

    // Parse an optional argument.
    (@first-positional #[option] $argument:ident, $it:ident) => {
        Some($argument)
    };

    // Parse as its argument.
    (@first-positional $argument:ident, $it:ident) => {
        $argument
    };

    // Test if `$n` is switch or not.
    (@is-switch $n:expr) => {
        std::convert::AsRef::<str>::as_ref($n).starts_with('-')
    };

    // Try to parse an argument to a parameter.
    (@switch-argument $switch:ident, $it:ident, $argument:ident) => {
        match $it.next() {
            Some($argument) => $argument,
            None => return Err(
                ::argwerk::Error::new(
                    ::argwerk::ErrorKind::MissingSwitchArgument {
                        switch: std::convert::AsRef::<str>::as_ref(&$switch).into(),
                        argument: stringify!($argument),
                    }
                )
            ),
        }
    };

    // Parse the rest of the available arguments.
    (@switch-argument #[rest] $switch:ident, $it:ident, $arg:ident) => {
        (&mut $it).map(String::from).collect::<Vec<_>>()
    };

    // Parse an optional argument.
    (@switch-argument #[option] $switch:ident, $it:ident, $arg:ident) => {
        match $it.peek() {
            Some(n) => if !$crate::__internal!(@is-switch n) {
                $it.next()
            } else {
                None
            }
            None => None,
        }
    };

    (@field $field:ident, $ty:ty) => {
        let mut $field: $ty = Default::default();
    };

    (@field $field:ident, $ty:ty = $expr:expr) => {
        let mut $field: $ty = $expr;
    };

    // Generate help for positional parameters.
    (@switch-help
        $($doc:literal)*
        [ $(#[$($first_meta:tt)*])* $first:ident $(, $(#[$($rest_meta:tt)*])* $rest:ident)* ]
    ) => {
        $crate::Switch {
            usage: concat!(
                $crate::__internal!(@doc $(#[$($first_meta)*])* $first),
                $(" ", $crate::__internal!(@doc $(#[$($rest_meta)*])* $rest),)*
            ),
            docs: &[$($doc,)*]
        }
    };

    // A branch in a help generator.
    (@switch-help
        $($doc:literal)*
        [$first:literal $(| $rest:literal)* $(, $(#[$($arg_meta:tt)*])* $arg:ident)*]
    ) => {
        $crate::Switch {
            usage: concat!(
                $first, $(", ", $rest,)*
                $(" ", $crate::__internal!(@doc $(#[$($arg_meta)*])* $arg),)*
            ),
            docs: &[$($doc,)*]
        }
    };

    // A branch in a help generator.
    (@switch-help $( $(#[doc = $doc:literal])* [$($branch:tt)*] $(if $cond:expr)? => $block:block)*) => {
        &[$($crate::__internal!(@switch-help $($doc)* [$($branch)*])),*]
    };

    // The empty condition.
    (@cond) => { true };

    // An expression condition.
    (@cond $expr:expr) => { $expr };

    // Expansion for all branches.
    (@branches $switch:ident, $it:ident,
        $(
            $(#[doc = $doc:literal])*
            [$($config:tt)*]
            $(if $cond:expr)? => $block:block
        )*
    ) => {{
        $($crate::__internal!(@branch $switch, $it, [ $($config)* ] $(if $cond)* => $block);)*
    }};

    // Match positional arguments.
    (@branch
        $switch:ident, $it:ident,
        [ $(#[$($first_meta:tt)*])* $first:ident $(, $(#[$($rest_meta:tt)*])* $rest:ident)* ]
        $(if $cond:expr)? => $block:block
    ) => {
        if $crate::__internal!(@cond $($cond)*) {
            let __argwerk_name = std::convert::AsRef::<str>::as_ref(&$switch).into();

            let $first = $crate::__internal!(@first-positional $(#[$($first_meta)*])* $switch, $it);
            $(let $rest = $crate::__internal!(@positional $(#[$($rest_meta)*])* $it, $rest);)*

            let mut __argwerk_handle = || -> Result<(), Box<dyn ::std::error::Error + Send + Sync + 'static>> {
                $crate::helpers::into_result($block)
            };

            if let Err(error) = __argwerk_handle() {
                return Err(::argwerk::Error::new(::argwerk::ErrorKind::Error {
                    name: __argwerk_name,
                    error
                }));
            }

            continue;
        }
    };

    // A single branch expansion.
    (@branch
        $switch:ident, $it:ident,
        [$first:literal $(| $rest:literal)* $(, $(#[$($arg_meta:tt)*])* $arg:ident)*] $(if $cond:expr)? => $block:block
    ) => {
        match std::convert::AsRef::<str>::as_ref(&$switch) {
            $first $( | $rest)* $(if $cond)* => {
                $(let $arg = $crate::__internal!(@switch-argument $(#[$($arg_meta)*])* $switch, $it, $arg);)*

                let mut __argwerk_handle = || -> Result<(), Box<dyn ::std::error::Error + Send + Sync + 'static>> {
                    $crate::helpers::into_result($block)
                };

                if let Err(error) = __argwerk_handle() {
                    return Err(::argwerk::Error::new(::argwerk::ErrorKind::Error {
                        name: std::convert::AsRef::<str>::as_ref(&$switch).into(),
                        error
                    }));
                }

                continue;
            }
            _ => (),
        }
    };
}
