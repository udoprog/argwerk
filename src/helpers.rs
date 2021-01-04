//! Helper module for the macros.
//!
//! Unless something is specifically re-exported, all implementation details are
//! expected to be private and might change between minor releases.

use std::error;
use std::fmt;

/// Default width to use when wrapping lines.
const WIDTH: usize = 80;

/// Default padding to use between switch summary and help text.
const PADDING: usize = 2;

/// A boxed error type.
type BoxError = Box<dyn error::Error + Send + Sync + 'static>;

/// Helper for converting a value into a result.
///
/// This is used to convert the value of a branch into a result.
#[doc(hidden)]
#[inline]
pub fn into_result<T>(value: T) -> Result<(), BoxError>
where
    T: IntoResult,
{
    value.into_result()
}

#[doc(hidden)]
pub trait IntoResult {
    fn into_result(self) -> Result<(), BoxError>;
}

impl IntoResult for () {
    #[inline]
    fn into_result(self) -> Result<(), BoxError> {
        Ok(())
    }
}

impl<E> IntoResult for Result<(), E>
where
    BoxError: From<E>,
{
    #[inline]
    fn into_result(self) -> Result<(), BoxError> {
        Ok(self?)
    }
}

/// Documentation over a single switch.
pub struct Switch {
    /// The usage summary of the switch.
    ///
    /// Like `--file, -f <path>`.
    pub usage: &'static str,
    /// Documentation comments associated with the switch.
    pub docs: &'static [&'static str],
}

/// Helper that can be formatted into documentation text.
pub struct Help {
    /// The verbatim usage summary specified when invoking the macro.
    pub usage: &'static str,
    /// Documentation comments associated with the command.
    pub docs: &'static [&'static str],
    /// Switches associated with the command.
    pub switches: &'static [Switch],
}

impl Help {
    /// Format the help with the given config.
    ///
    /// # Examples
    ///
    /// ```rust
    /// argwerk::define! {
    ///     /// A simple test command.
    ///     #[usage = "command [-h]"]
    ///     struct Args {
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
    /// }
    ///
    /// # fn main() -> Result<(), argwerk::Error> {
    /// let formatted = format!("{}", Args::help().format().width(120));
    ///
    /// assert!(formatted.split('\n').any(|line| line.len() > 80));
    /// assert!(formatted.split('\n').all(|line| line.len() < 120));
    /// # Ok(()) }
    /// ```
    pub fn format(&self) -> HelpFormat {
        HelpFormat {
            help: self,
            width: WIDTH,
            padding: PADDING,
        }
    }
}

impl fmt::Display for Help {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format().fmt(f)
    }
}

/// A wrapper to format the help message with custom parameters.
///
/// Constructed through [Help::format].
pub struct HelpFormat<'a> {
    help: &'a Help,
    width: usize,
    padding: usize,
}

impl HelpFormat<'_> {
    /// Configure the width to use for help text.
    pub fn width(self, width: usize) -> Self {
        Self { width, ..self }
    }

    /// Configure the padding to use when formatting help.
    ///
    /// This determines the indentation of options and the distances between
    /// options and help text.
    pub fn padding(self, padding: usize) -> Self {
        Self { padding, ..self }
    }
}

impl<'a> fmt::Display for HelpFormat<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Usage: {name}", name = self.help.usage)?;

        if !self.help.docs.is_empty() {
            writeln!(f, "{}", TextWrap::new("", &self.help.docs, self.width, 0))?;
        }

        writeln!(f)?;

        let usage_len = self
            .help
            .switches
            .iter()
            .map(|s| {
                if s.docs.is_empty() {
                    s.usage.len()
                } else {
                    s.usage.len() + self.padding
                }
            })
            .max()
            .unwrap_or_default();

        if !self.help.switches.is_empty() {
            writeln!(f, "Options:")?;

            for d in self.help.switches {
                writeln!(
                    f,
                    "{}",
                    TextWrap::switch(&d.usage, &d.docs, self.width, self.padding, usage_len)
                )?;
            }
        }

        Ok(())
    }
}

/// Helper to wrap documentation text.
struct TextWrap<'a> {
    init: &'a str,
    docs: &'a [&'static str],
    width: usize,
    padding: usize,
    init_len: Option<usize>,
}

impl<'a> TextWrap<'a> {
    fn new(init: &'a str, docs: &'a [&'static str], width: usize, padding: usize) -> Self {
        Self {
            init,
            docs,
            width,
            padding,
            init_len: None,
        }
    }

    fn switch(
        init: &'a str,
        docs: &'a [&'static str],
        width: usize,
        padding: usize,
        init_len: usize,
    ) -> Self {
        TextWrap {
            init,
            docs,
            width,
            padding,
            init_len: Some(init_len),
        }
    }
}

impl fmt::Display for TextWrap<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.docs.is_empty() {
            textwrap(
                f,
                self.docs,
                self.width,
                self.padding,
                &self.init,
                self.init_len,
            )?;
        } else {
            write!(f, "{}", self.init)?;
        }

        Ok(())
    }
}

/// Utility for the bytewise wrapping of text.
fn textwrap<I>(
    f: &mut fmt::Formatter<'_>,
    lines: I,
    width: usize,
    padding: usize,
    init: &str,
    init_len: Option<usize>,
) -> fmt::Result
where
    I: IntoIterator,
    I::Item: AsRef<str>,
{
    let mut it = lines.into_iter().peekable();

    let fill = init_len.unwrap_or(init.len()) + padding;
    let mut init = Some(init);

    let trim = match it.peek() {
        Some(line) => Some(chars_count(line.as_ref(), |c| c == ' ')),
        None => None,
    };

    while let Some(line) = it.next() {
        let mut line = line.as_ref();

        // Trim the line by skipping the whitespace common to all lines..
        if let Some(trim) = trim {
            line = skip_chars(line, trim);

            // Whole line was trimmed.
            if line.is_empty() {
                writeln!(f)?;
                continue;
            }
        }

        // Whitespace prefix currently in use.
        let ws_fill = next_index(line, char::is_alphanumeric).unwrap_or_default();
        let mut line_first = true;

        loop {
            let fill = if !std::mem::take(&mut line_first) {
                fill + ws_fill
            } else {
                fill
            };

            let mut space_span = None;

            loop {
                let c = space_span.map(|(_, e)| e).unwrap_or_default();

                let (start, leap) = match line[c..].find(' ') {
                    Some(i) => {
                        let leap = next_index(&line[c + i..], |c| c != ' ').unwrap_or(1);
                        (c + i, leap)
                    }
                    None => {
                        // if the line fits within the current target fill,
                        // include all of it.
                        if line.len() + fill <= width {
                            space_span = None;
                        }

                        break;
                    }
                };

                if start + fill > width {
                    break;
                }

                space_span = Some((start, start + leap));
            }

            let init_len = if let Some(init) = init.take() {
                fill_spaces(f, padding)?;
                f.write_str(init)?;
                padding + init.len()
            } else {
                0
            };

            fill_spaces(f, fill.saturating_sub(init_len))?;

            if let Some((start, end)) = space_span {
                writeln!(f, "{}", &line[..start])?;
                line = &line[end..];
                continue;
            }

            f.write_str(line)?;
            break;
        }

        if it.peek().is_some() {
            writeln!(f)?;
        }
    }

    return Ok(());

    /// Get the next index that is alphanumeric.
    fn next_index(s: &str, p: fn(char) -> bool) -> Option<usize> {
        Some(s.char_indices().skip_while(|(_, c)| !p(*c)).next()?.0)
    }

    /// Count the number of spaces in the string, and return the first index that is not a space.
    fn chars_count(s: &str, p: fn(char) -> bool) -> usize {
        s.chars().take_while(|c| p(*c)).count()
    }

    /// Skip the given number of characters.
    fn skip_chars(s: &str, count: usize) -> &str {
        let e = s
            .char_indices()
            .skip(count)
            .map(|(i, _)| i)
            .next()
            .unwrap_or(s.len());

        &s[e..]
    }

    fn fill_spaces(f: &mut fmt::Formatter<'_>, mut count: usize) -> fmt::Result {
        // Static buffer for quicker whitespace filling.
        static BUF: &str = "                                                                ";

        while count > 0 {
            f.write_str(&BUF[..usize::min(count, BUF.len())])?;
            count = count.saturating_sub(BUF.len());
        }

        Ok(())
    }
}
