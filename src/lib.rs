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
//!         positional: Option<(String, String)>,
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
//!     (foo, bar, #[rest] args) if positional.is_none() => {
//!         positional = Some((foo.into(), bar.into()));
//!         rest = args;
//!         Ok(())
//!     }
//! }?;
//!
//! dbg!(args);
//! Ok(())
//! # }
//! ```
//!
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
/// This also generated two helper functions available in the branches:
/// * `write_help` - Which can write help to something implementing
///   [std::io::Write].
/// * `print_help` - Which will write the help string to [io::stdout].
///
/// These are only available in the scope of the matching branches.
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
/// # Argument branches
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
/// # Parse the rest of available arguments
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
/// It's also possible to annotate a positional argument with `#[rest]`.
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     vec![String::from("foo"), String::from("bar"), String::from("baz")] =>
///     /// A simple test command.
///     "testcommand [-h]" {
///         first: Option<String>,
///         rest: Vec<String>,
///     }
///     (a, #[rest] args) => {
///         first = Some(a);
///         rest = args;
///         Ok(())
///     }
/// }?;
///
/// assert_eq!(args.first.as_deref(), Some("foo"));
/// assert_eq!(args.rest, &["bar", "baz"]);
/// # Ok(()) }
/// ```
///
/// # Parse position arguments.
///
/// You can write a branch that receives the rest of the arguments using the
/// `#[rest]` attribute.
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     ["a", "b"].iter().copied() =>
///     /// A simple test command.
///     "testcommand [-h]" {
///         positional: Option<(String, String)>,
///     }
///     /// Takes argument at <foo> and <bar>.
///     (foo, bar) if positional.is_none() => {
///         positional = Some((foo.into(), bar.into()));
///         Ok(())
///     }
/// }?;
///
/// assert_eq!(args.positional, Some((String::from("a"), String::from("b"))));
/// # Ok(()) }
/// ```
///
/// This will consume the rest of the arguments.
///
/// # Examples
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::parse! {
///     /// A simple test command.
///     ///
///     /// This is nice!
///     "testcommand [-h]" {
///         help: bool,
///         file: Option<String>,
///         limit: usize = 42,
///     }
///     /// Print the help.
///     "-h" | "--help" => {
///         help = true;
///         print_help();
///         Ok(())
///     }
///     /// Hello World.
///     "--limit" | "-l", n => {
///         limit = str::parse(&n)?;
///         Ok(())
///     }
/// }?;
///
/// if args.help {
///     return Ok(());
/// }
///
/// Ok(())
/// # }
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
        ($first:ident $(, $rest:ident)* $(, #[rest] $last:ident)?)
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
        ($first:ident $(, $rest:ident)* $(, #[rest] $last:ident)?)
        $(if $cond:expr)? => $block:block
        $($tail:tt)*
    ) => {
        if argwerk::__parse_inner!(@cond $($cond)*) {
            let __argwerk_error_argument = std::convert::AsRef::<str>::as_ref(&$argument).into();

            let $first = $argument;
            $(let $rest = $crate::__parse_inner!(@positional $it, $rest);)*
            $(let $last = (&mut $it).map(String::from).collect::<Vec<String>>();)*

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
