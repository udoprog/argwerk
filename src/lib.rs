//! [![Documentation](https://docs.rs/argwerk/badge.svg)](https://docs.rs/argwerk)
//! [![Crates](https://img.shields.io/crates/v/argwerk.svg)](https://crates.io/crates/argwerk)
//! [![Actions Status](https://github.com/udoprog/argwerk/workflows/Rust/badge.svg)](https://github.com/udoprog/argwerk/actions)
//!
//! Helper utility for parsing simple commandline arguments.
//!
//! This is **not** intended to be a complete commandline parser library.
//! Instead this can be used as an alternative quick-and-dirty approach that can
//! be cheaply incorporated into a tool.
//!
//! For a more complete commandline parsing library, use [clap].
//!
//! See the documentation for [argwerk::parse!] for how to use.
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
//!     /// A simple test command.
//!     ///
//!     /// This is nice!
//!     "testcommand [-h]" {
//!         help: bool,
//!         file: Option<String>,
//!         limit: usize = 42,
//!         positional: Option<(String, Option<String>)>,
//!         rest: Vec<String>,
//!     }
//!     /// Print this help.
//!     "-h" | "--help" => {
//!         help = true;
//!         print_help();
//!         Ok(())
//!     }
//!     /// Limit the number of things by <n>.
//!     "--limit" | "-l", n => {
//!         limit = str::parse(&n)?;
//!         Ok(())
//!     }
//!     /// Write to the file specified by <path>.
//!     "--file", path if !file.is_some() => {
//!         file = Some(path);
//!         Ok(())
//!     }
//!     /// Takes argument at <foo> and <bar>.
//!     (foo, #[option] bar, #[rest] args) if positional.is_none() => {
//!         positional = Some((foo, bar));
//!         rest = args;
//!         Ok(())
//!     }
//! }?;
//!
//! dbg!(args);
//! # Ok(()) }
//! ```
//!
//! [argwerk::parse!]: https://docs.rs/argwerk/0/argwerk/macro.parse.html
//! [clap]: https://docs.rs/clap

#![deny(missing_docs)]

use std::error;
use std::fmt;

/// Helper utility for building documentation.
pub fn doc<'a>(initial: &'a str, docs: &'a [&'static str]) -> impl fmt::Display + 'a {
    Doc { initial, docs }
}

struct Doc<'a> {
    initial: &'a str,
    docs: &'a [&'static str],
}

impl fmt::Display for Doc<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        textwrap(f, self.docs, 80, &self.initial)?;
        Ok(())
    }
}

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
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind.as_ref() {
            ErrorKind::MissingParameter { argument, name } => {
                write!(
                    f,
                    "missing parameter to argument `{}`: <{}>",
                    argument, name
                )
            }
            ErrorKind::MissingPositional { name } => {
                write!(f, "missing positional parameter <{}>", name)
            }
            ErrorKind::Unsupported { argument } => {
                write!(f, "unsupported argument `{}`", argument)
            }
            ErrorKind::Error { argument, error } => {
                write!(f, "bad argument `{}`: {}", argument, error)
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
    /// An argument that is unsupported.
    Unsupported {
        /// An unsupported argument.
        argument: Box<str>,
    },
    /// When a parameter to an argument is missing.
    MissingParameter {
        /// The argument where the named argument was missing, like `--file` in
        /// `--file <path>`.
        argument: Box<str>,
        /// The parameter that was missing, like `path` in `--file <path>`.
        name: &'static str,
    },
    /// When a positional parameter is missing.
    MissingPositional {
        /// The parameter that was missing, like `path` in `<path>`.
        name: &'static str,
    },
    /// When an error has been raised while processing an argument, typically
    /// when something is being parsed.
    Error {
        /// The argument that could not be parsed.
        argument: Box<str>,
        /// The error that caused the parsing error.
        error: Box<dyn error::Error + Send + Sync + 'static>,
    },
}

/// Parse commandline arguments.
///
/// This will generate an anonymous structure containing the arguments defined
/// which is returned by the macro.
///
/// Each branch is executed when an incoming argument matches and must return a
/// [Result], like `Ok(())`. Error raised in the branch will cause a
/// [ErrorKind::Error] error to be raised associated with that argument
/// with the relevant error attached.
///
/// This also generated two helper functions available in the parse branches:
/// * `write_help` - Which can write help to something implementing
///   [std::io::Write].
/// * `print_help` - Which will write the help string to [std::io::stdout].
///
/// The [parse] macro can be invoked in two ways.
///
/// Using `std::env::args()` to get arguments from the environment:
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     /// A simple test command.
///     "testcommand [-h]" {
///         help: bool,
///         limit: usize = 10,
///     }
/// }?;
/// # Ok(()) }
/// ```
///
/// Or explicitly specifying an iterator to use with `<iter> => <config>`. This
/// works with anything that implements `AsRef<str>`:
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     vec!["foo", "bar", "baz"] =>
///     /// A simple test command.
///     "testcommand [-h]" {
///         help: bool,
///         limit: usize = 10,
///         positional: Option<(&'static str, &'static str, &'static str)>,
///     }
///     (a, b, c) => {
///         positional = Some((a, b, c));
///         Ok(())
///     }
/// }?;
///
/// assert_eq!(args.positional, Some(("foo", "bar", "baz")));
/// # Ok(()) }
/// ```
///
/// # Arguments
///
/// The first part of the [parse] macro defines the state available to the
/// parser. These are field-like declarations which can specify a default value.
///
/// This is the only required component of the macro.
///
/// Fields which do not specify an initialization value will be initialized
/// through [Default::default].
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     /// A simple test command.
///     "testcommand [-h]" {
///         help: bool,
///         limit: usize = 10,
///     }
/// }?;
///
/// assert_eq!(args.help, false);
/// assert_eq!(args.limit, 10);
/// # Ok(()) }
/// ```
///
/// ## Argument branches
///
/// The basic form of an argument branch is:
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     vec![String::from("-h")] =>
///     /// A simple test command.
///     "testcommand [-h]" {
///         help: bool,
///     }
///     /// Print the help.
///     "-h" | "--help" => {
///         help = true;
///         print_help();
///         Ok(())
///     }
/// }?;
///
/// assert_eq!(args.help, true);
/// # Ok(()) }
/// ```
///
/// ## Parse all available arguments with `#[rest]`
///
/// You can write a branch that receives the rest of the arguments using the
/// `#[rest]` attribute.
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     vec![String::from("foo"), String::from("bar"), String::from("baz")] =>
///     /// A simple test command.
///     "testcommand [-h]" {
///         rest: Vec<String>,
///     }
///     #[rest] args => {
///         rest = args;
///         Ok(())
///     }
/// }?;
///
/// assert_eq!(args.rest, &["foo", "bar", "baz"]);
/// # Ok(()) }
/// ```
///
/// ## Parse positional arguments
///
/// Positional arguments are parsed by specifying a tuple in the match branch.
///
/// Positional arguments support the following attributes:
/// * `#[option]` - which will cause the argument to be optionally parsed into
///   an `Option<I::Item>`.
/// * `#[rest]` - which will parse the rest of the arguments.
///
/// The following is a basic example without attributes. Both `foo` and `bar`
/// are required if the branch matches.
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     ["a", "b"].iter().copied().map(String::from) =>
///     /// A simple test command.
///     "testcommand [-h]" {
///         positional: Option<(String, String)>,
///     }
///     /// Takes argument at <foo> and <bar>.
///     (foo, bar) if positional.is_none() => {
///         positional = Some((foo, bar));
///         Ok(())
///     }
/// }?;
///
/// assert_eq!(args.positional, Some((String::from("a"), String::from("b"))));
/// # Ok(()) }
/// ```
///
/// The following showcases positional parameters using `#[option]` and
/// `#[rest]`.
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     ["foo", "bar", "baz"].iter().copied().map(String::from) =>
///     /// A simple test command.
///     "testcommand [-h]" {
///         first: String,
///         second: Option<String>,
///         rest: Vec<String>,
///     }
///     (a, #[option] b, #[rest] c) => {
///         first = a;
///         second = b;
///         rest = c;
///         Ok(())
///     }
/// }?;
///
/// assert_eq!(args.first, "foo");
/// assert_eq!(args.second.as_deref(), Some("bar"));
/// assert_eq!(args.rest, &["baz"]);
/// # Ok(()) }
/// ```
#[macro_export]
macro_rules! parse {
    // Parse with a custom iterator.
    (
        $it:expr => $($rest:tt)*
    ) => {{
        let mut __argwerk_it = ::std::iter::IntoIterator::into_iter($it);
        $crate::__parse_inner!(__argwerk_it, $($rest)*)
    }};

    // Parse with `std::env::args()`.
    (
        $($rest:tt)*
    ) => {{
        let mut __argwerk_it = ::std::env::args();
        __argwerk_it.next();
        $crate::__parse_inner!(__argwerk_it, $($rest)*)
    }};
}

/// Internal implementation details of the [parse] macro.
#[doc(hidden)]
#[macro_export]
macro_rules! __parse_inner {
    // The guts of the parser.
    (
        $it:ident,
        $(#[doc = $doc:literal])*
        $usage:literal {
            $($field:ident : $ty:ty $(= $expr:expr)?),* $(,)?
        }
        $($tt:tt)*
    ) => {{
        let mut parser = || {
            fn write_help(mut w: impl ::std::io::Write) -> ::std::io::Result<()> {
                use std::fmt::Write as _;

                writeln!(w, "Usage: {name}", name = $usage)?;

                let docs = vec![$($doc,)*];

                if !docs.is_empty() {
                    writeln!(w, "{}", $crate::doc("", &docs))?;
                }

                writeln!(w)?;
                let mut prefix = String::new();
                $crate::__parse_inner!(@help w, prefix, $($tt)*);
                Ok(())
            }

            fn print_help() {
                let out = ::std::io::stdout();
                let mut out = out.lock();
                write_help(out).expect("writing to stdout failed");
            }

            $($crate::__parse_inner!(@field $field, $ty $(= $expr)*);)*

            while let Some(__argwerk_arg) = $it.next() {
                $crate::__parse_inner!(@branch __argwerk_arg, $it, $($tt)*);

                return Err(::argwerk::Error::new(::argwerk::ErrorKind::Unsupported {
                    argument: __argwerk_arg.into()
                }));
            }

            #[derive(Debug)]
            struct Args { $($field: $ty,)* }

            Ok(Args {
                $($field,)*
            })
        };

        parser()
    }};

    // Parse the rest of the available arguments.
    (@positional #[rest] $it:ident, $arg:ident) => {
        (&mut $it).map(String::from).collect::<Vec<String>>();
    };

    // Parse an optional argument.
    (@positional #[option] $it:ident, $arg:ident) => {
        $it.next()
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

    // Try to parse an argument to a parameter.
    (@argument $argument:ident, $it:ident, $arg:ident) => {
        match $it.next() {
            Some($arg) => $arg,
            None => return Err(
                ::argwerk::Error::new(
                    ::argwerk::ErrorKind::MissingParameter {
                        argument: std::convert::AsRef::<str>::as_ref(&$argument).into(),
                        name: stringify!($arg),
                    }
                )
            ),
        }
    };

    (@field $field:ident, $ty:ty) => {
        let mut $field: $ty = Default::default();
    };

    (@field $field:ident, $ty:ty = $expr:expr) => {
        let mut $field: $ty = $expr;
    };

    // Empty help generator.
    (@help $w:ident, $prefix:ident,) => {};

    // Generate help for positional parameters.
    (@help
        $w:ident,
        $prefix:ident,
        $(#[doc = $doc:literal])*
        ($first:ident $(, $(#[$($rest_meta:tt)*])* $rest:ident)*)
        $(if $cond:expr)? => $block:block
        $($tail:tt)*
    ) => {{
        $prefix.clear();

        $prefix.push_str("  <");
        $prefix.push_str(stringify!($first));
        $prefix.push_str(">");

        $(
            $prefix.push_str(" <");
            $prefix.push_str(stringify!($rest));
            $prefix.push_str(">");
        )*

        let docs = vec![$($doc,)*];

        if !docs.is_empty() {
            $prefix.push_str(" - ");
            writeln!($w, "{}", $crate::doc(&$prefix, &docs))?;
        } else {
            writeln!($w, "{}", $prefix)?;
        }

        $crate::__parse_inner!(@help $w, $prefix, $($tail)*);
    }};

    // Generate help for #[rest] bindings.
    (@help
        $w:ident,
        $prefix:ident,
        $(#[doc = $doc:literal])*
        #[rest] $binding:ident $(if $cond:expr)? => $block:block
        $($tail:tt)*
    ) => {{
        $prefix.clear();
        $prefix.push_str("  <");
        $prefix.push_str(stringify!($binding));
        $prefix.push_str("..>");

        let docs = vec![$($doc,)*];

        if !docs.is_empty() {
            $prefix.push_str(" - ");
            writeln!($w, "{}", $crate::doc(&$prefix, &docs))?;
        } else {
            writeln!($w, "{}", $prefix)?;
        }

        $crate::__parse_inner!(@help $w, $prefix, $($tail)*);
    }};

    // A branch in a help generator.
    (@help
        $w:ident,
        $prefix:ident,
        $(#[doc = $doc:literal])*
        $first:literal $(| $rest:literal)* $(, $arg:ident)* $(if $cond:expr)? => $block:block
        $($tail:tt)*
    ) => {{
        $prefix.clear();
        $prefix.push_str("  ");
        $prefix.push_str($first);

        $(
            $prefix.push_str(", ");
            $prefix.push_str($rest);
        )*

        $(
            $prefix.push_str(" <");
            $prefix.push_str(stringify!($arg));
            $prefix.push('>');
        )*

        let docs = vec![$($doc,)*];

        if !docs.is_empty() {
            $prefix.push_str(" - ");
            writeln!($w, "{}", $crate::doc(&$prefix, &docs))?;
        } else {
            writeln!($w, "{}", $prefix)?;
        }

        $crate::__parse_inner!(@help $w, $prefix, $($tail)*);
    }};

    // The empty condition.
    (@cond) => { true };

    // An expression condition.
    (@cond $expr:expr) => { $expr };

    // Empty branch expansion.
    (@branch $arg:ident, $it:ident,) => {};

    // Match positional arguments.
    (@branch
        $argument:ident, $it:ident,
        $(#[doc = $doc:literal])*
        ($first:ident $(, $(#[$($rest_meta:tt)*])* $rest:ident)*)
        $(if $cond:expr)? => $block:block
        $($tail:tt)*
    ) => {
        if argwerk::__parse_inner!(@cond $($cond)*) {
            let __argwerk_error_argument = std::convert::AsRef::<str>::as_ref(&$argument).into();

            let $first = $argument;
            $(let $rest = $crate::__parse_inner!(@positional $(#[$($rest_meta)*])* $it, $rest);)*

            let mut __argwerk_handle = || -> Result<(), Box<dyn ::std::error::Error + Send + Sync + 'static>> {
                $block
            };

            if let Err(error) = __argwerk_handle() {
                return Err(::argwerk::Error::new(::argwerk::ErrorKind::Error {
                    argument: __argwerk_error_argument,
                    error
                }));
            }

            continue;
        }

        $crate::__parse_inner!(@branch $argument, $it, $($tail)*);
    };

    // Match the rest of the arguments
    (@branch
        $argument:ident, $it:ident,
        $(#[doc = $doc:literal])*
        #[rest] $binding:ident $(if $cond:expr)? => $block:block
        $($tail:tt)*
    ) => {
        if argwerk::__parse_inner!(@cond $($cond)*) {
            let __argwerk_error_argument = std::convert::AsRef::<str>::as_ref(&$argument).into();

            let $binding = Some($argument).into_iter().chain((&mut $it)).collect::<Vec<_>>();

            let mut __argwerk_handle = || -> Result<(), Box<dyn ::std::error::Error + Send + Sync + 'static>> {
                $block
            };

            if let Err(error) = __argwerk_handle() {
                return Err(::argwerk::Error::new(::argwerk::ErrorKind::Error {
                    argument: __argwerk_error_argument,
                    error
                }));
            }

            continue;
        }

        $crate::__parse_inner!(@branch $argument, $it, $($tail)*);
    };

    // A single branch expansion.
    (@branch
        $argument:ident, $it:ident,
        $(#[$($meta:tt)*])*
        $first:literal $(| $rest:literal)* $(, $arg:ident)* $(if $cond:expr)? => $block:block
        $($tail:tt)*
    ) => {
        match std::convert::AsRef::<str>::as_ref(&$argument) {
            $first $( | $rest)* $(if $cond)* => {
                $(let $arg = $crate::__parse_inner!(@argument $argument, $it, $arg);)*

                let mut __argwerk_handle = || -> Result<(), Box<dyn ::std::error::Error + Send + Sync + 'static>> {
                    $block
                };

                if let Err(error) = __argwerk_handle() {
                    return Err(::argwerk::Error::new(::argwerk::ErrorKind::Error {
                        argument: std::convert::AsRef::<str>::as_ref(&$argument).into(),
                        error
                    }));
                }

                continue;
            }
            _ => (),
        }

        $crate::__parse_inner!(@branch $argument, $it, $($tail)*);
    };
}

/// Utility for the bytewise wrapping of text.
fn textwrap<I>(f: &mut fmt::Formatter<'_>, lines: I, width: usize, initial: &str) -> fmt::Result
where
    I: IntoIterator,
    I::Item: AsRef<str>,
{
    let mut first = true;
    let mut it = lines.into_iter().peekable();

    while let Some(line) = it.next() {
        let mut line = line.as_ref().trim();

        loop {
            let mut col = 0;

            while !line.is_empty() {
                let new = match line[col..].find(' ') {
                    Some(i) => col + i + 1,
                    None => {
                        col = 0;
                        break;
                    }
                };

                if new + initial.len() > width {
                    break;
                }

                col = new;
            }

            if std::mem::take(&mut first) {
                f.write_str(initial)?;
            } else {
                for c in std::iter::repeat(' ').take(initial.len()) {
                    write!(f, "{}", c)?;
                }
            };

            if col > 0 {
                f.write_str(&line[..(col - 1)])?;
                f.write_str("\n")?;
                line = &line[col..];
                continue;
            }

            f.write_str(line)?;
            break;
        }

        if it.peek().is_some() {
            f.write_str("\n")?;
        }
    }

    Ok(())
}
