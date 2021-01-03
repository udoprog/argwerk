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
//! > cargo run --example basic
//! > ```
//!
//! ```rust
//! # fn main() -> Result<(), argwerk::Error> {
//! let args = argwerk::argwerk! {
//!     /// A simple test command.
//!     ///
//!     /// This is nice!
//!     "testcommand [-h]" {
//!         help: bool,
//!         file: Option<String>,
//!         limit: usize = 42,
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
//! }?;
//!
//! if args.help {
//!     return Ok(());
//! }
//!
//! Ok(())
//! # }
//! ```
//!
//! [clap]: https://docs.rs/clap

#![deny(missing_docs)]

use std::error;
use std::fmt;

/// Helper utility for building documentation.
pub struct Doc<'a> {
    initial: &'a str,
    subsequent: &'a str,
    docs: Vec<&'static str>,
}

impl<'a> Doc<'a> {
    /// Construct a new doc builder.
    pub fn new(initial: &'a str, subsequent: &'a str) -> Self {
        Self {
            initial: initial.into(),
            subsequent: subsequent.into(),
            docs: Vec::new(),
        }
    }

    /// Test if documentation helper is empty.
    pub fn is_empty(&self) -> bool {
        self.docs.is_empty()
    }

    /// Push a line of documentation.
    pub fn push(&mut self, s: &'static str) {
        self.docs.push(s);
    }
}

impl fmt::Display for Doc<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        textwrap(f, &self.docs, 80, &self.initial, &self.subsequent)?;
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
/// # Examples
///
/// ```rust
/// # fn main() -> Result<(), argwerk::Error> {
/// let args = argwerk::argwerk! {
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
macro_rules! argwerk {
    (
        $(#[$($usage_meta:tt)*])*
        $usage:literal $({
            $($field:ident : $ty:ty $(= $expr:expr)?),* $(,)?
        })? $(
            $(#[$($meta:tt)*])*
            $first:literal $(| $rest:literal)* $(, $arg:ident)* $(if $cond:expr)? => $block:block
        )*
    ) => {{
        let mut parser = || {
            fn write_help(mut w: impl ::std::io::Write) -> ::std::io::Result<()> {
                use std::fmt::Write as _;

                writeln!(w, "Usage: {name}", name = $usage)?;

                let mut doc = $crate::Doc::new("", "");
                $($crate::argwerk!(@doc #[$($usage_meta)*] doc);)*

                if !doc.is_empty() {
                    writeln!(w, "{}", doc)?;
                }

                writeln!(w)?;

                let mut prefix = String::new();

                $(
                prefix.clear();
                prefix.push_str("  ");
                prefix.push_str($first);

                $(
                    prefix.push_str(", ");
                    prefix.push_str($rest);
                )*

                $(
                    prefix.push_str(" <");
                    prefix.push_str(stringify!($arg));
                    prefix.push('>');
                )*

                prefix.push_str(" - ");

                let subsequent = ::std::iter::repeat(' ').take(prefix.len()).collect::<String>();

                let mut doc = $crate::Doc::new(&prefix, &subsequent);
                $($crate::argwerk!(@doc #[$($meta)*] doc);)*
                writeln!(w, "{}", doc)?;
                )*

                Ok(())
            }

            fn print_help() {
                let out = ::std::io::stdout();
                let mut out = out.lock();
                write_help(out).expect("writing to stdout failed");
            }

            struct Args {
                $($($field: $ty,)*)*
            }

            $(
                $($crate::argwerk!(@decl $field, $ty $(, $expr)*);)*
            )*

            let mut __argwerk__it = ::std::env::args();
            __argwerk__it.next();

            while let Some(arg) = __argwerk__it.next() {
                match arg.as_str() {
                    $($first $( | $rest)* $(if $cond)* => {
                        $(
                            let $arg = match __argwerk__it.next() {
                                Some($arg) => $arg,
                                None => return Err(
                                    ::argwerk::Error::new(
                                        ::argwerk::ErrorKind::MissingParameter {
                                            argument: arg.into(),
                                            name: stringify!($arg),
                                        }
                                    )
                                ),
                            };
                        )*

                        let mut __argwerk_handle = || -> Result<(), Box<dyn ::std::error::Error + Send + Sync + 'static>> {
                            $block
                        };

                        if let Err(error) = __argwerk_handle() {
                            return Err(::argwerk::Error::new(::argwerk::ErrorKind::Error {
                                argument: arg.into(),
                                error
                            }));
                        }
                    })*
                    other => {
                        return Err(::argwerk::Error::new(::argwerk::ErrorKind::Unsupported {
                            argument: other.into()
                        }));
                    }
                }
            }

            Ok(Args {
                $($($field,)*)*
            })
        };

        parser()
    }};

    // Matching doc comments to add to the document formatter.
    (@doc #[doc = $doc:literal] $out:ident) => {
        $out.push($doc);
    };

    // Catch-all for filtering out non-relevant doc additions.
    (@doc #[$meta:meta] $out:ident) => {
    };

    (@decl $field:ident, $ty:ty) => {
        let mut $field: $ty = Default::default();
    };

    (@decl $field:ident, $ty:ty, $expr:expr) => {
        let mut $field: $ty = $expr;
    };
}

/// Utility for the bytewise wrapping of text.
fn textwrap<I>(
    f: &mut fmt::Formatter<'_>,
    lines: I,
    width: usize,
    initial: &str,
    subsequent: &str,
) -> fmt::Result
where
    I: IntoIterator,
    I::Item: AsRef<str>,
{
    let mut first = true;
    let mut it = lines.into_iter().peekable();

    while let Some(line) = it.next() {
        let mut line = line.as_ref().trim();

        loop {
            let pfx = if std::mem::take(&mut first) {
                initial
            } else {
                subsequent
            };

            let mut col = 0;

            while !line.is_empty() {
                let new = match line[col..].find(' ') {
                    Some(i) => col + i + 1,
                    None => {
                        col = 0;
                        break;
                    }
                };

                if new + pfx.len() > width {
                    break;
                }

                col = new;
            }

            f.write_str(pfx)?;

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
