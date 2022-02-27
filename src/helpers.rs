//! Helper module for the macros.
//!
//! Unless something is specifically re-exported, all implementation details are
//! expected to be private and might change between minor releases.

use std::error;
use std::ffi::{OsStr, OsString};
use std::fmt;

/// Default width to use when wrapping lines.
///
/// See [HelpFormat::width].
const WIDTH: usize = 80;

/// Default padding to use between switch summary and help text.
///
/// See [HelpFormat::padding].
const PADDING: usize = 2;

/// Default max usage width to use for switches and arguments.
///
/// See [HelpFormat::max_usage].
const MAX_USAGE: usize = 24;

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
            max_usage: MAX_USAGE,
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
    max_usage: usize,
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

    /// Configure the max usage width to use when formatting help.
    ///
    /// This determines how wide a usage help is allowed to be before it forces
    /// the associated documentation to flow to the next line.
    ///
    /// Usage help is the `--file, -f <path>` part of each switch and argument.
    pub fn max_usage(self, max_usage: usize) -> Self {
        Self { max_usage, ..self }
    }
}

impl<'a> fmt::Display for HelpFormat<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Usage: {name}", name = self.help.usage)?;

        if !self.help.docs.is_empty() {
            writeln!(f, "{}", TextWrap::new("", self.help.docs, self.width, 0))?;
        }

        writeln!(f)?;

        let usage_len = self
            .help
            .switches
            .iter()
            .map(|s| {
                usize::min(
                    self.max_usage,
                    if s.docs.is_empty() {
                        s.usage.len()
                    } else {
                        s.usage.len() + self.padding
                    },
                )
            })
            .max()
            .unwrap_or(self.max_usage);

        if !self.help.switches.is_empty() {
            writeln!(f, "Options:")?;
            let mut first = true;

            let mut it = self.help.switches.iter().peekable();

            while let Some(d) = it.next() {
                let first = std::mem::take(&mut first);
                let more = it.peek().is_some();

                let wrap = TextWrap {
                    init: d.usage,
                    docs: d.docs,
                    width: self.width,
                    padding: self.padding,
                    init_len: Some(usage_len),
                    first,
                    more,
                };

                writeln!(f, "{}", wrap)?;
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
    /// The maximum init length permitted.
    init_len: Option<usize>,
    /// If this is the first element.
    first: bool,
    /// If there are more elements coming after this.
    more: bool,
}

impl<'a> TextWrap<'a> {
    fn new(init: &'a str, docs: &'a [&'static str], width: usize, padding: usize) -> Self {
        Self {
            init,
            docs,
            width,
            padding,
            init_len: None,
            first: true,
            more: false,
        }
    }

    fn wrap(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut it = self.docs.iter().peekable();

        // No documentation lines.
        if it.peek().is_none() {
            fill_spaces(f, self.padding)?;
            f.write_str(self.init)?;
            return Ok(());
        }

        let init_len = self.init_len.unwrap_or(self.init.len());

        let (long, mut init) = if self.init.len() + self.padding > init_len {
            (true, None)
        } else {
            (false, Some(&self.init))
        };

        // NB: init line is broader than maximum permitted init length.
        if long {
            // If we're not the first line, add a newline to visually separate
            // the line with the long usage.
            if !self.first {
                writeln!(f)?;
            }

            fill_spaces(f, self.padding)?;
            writeln!(f, "{}", self.init)?;
        }

        let fill = init_len + self.padding;

        let trim = it.peek().map(|line| {
            chars_count(line, |c| c == ' ')
        });

        while let Some(line) = it.next() {
            let mut line = *line;

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
                            if line.len() + fill <= self.width {
                                space_span = None;
                            }

                            break;
                        }
                    };

                    if start + fill > self.width {
                        break;
                    }

                    space_span = Some((start, start + leap));
                }

                let init_len = if let Some(init) = init.take() {
                    fill_spaces(f, self.padding)?;
                    f.write_str(init)?;
                    self.padding + init.len()
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

        // If we're not the first line, add a newline to visually separate the
        // line with the long usage.
        if long && !self.first && self.more {
            writeln!(f)?;
        }

        return Ok(());

        /// Get the next index that is alphanumeric.
        fn next_index(s: &str, p: fn(char) -> bool) -> Option<usize> {
            Some(s.char_indices().find(|&(_, c)| p(c))?.0)
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
}

impl fmt::Display for TextWrap<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.wrap(f)
    }
}

/// Helpers around an iterator.
pub struct Input<I>
where
    I: Iterator,
{
    it: I,
    buf: Option<I::Item>,
}

impl<I> Input<I>
where
    I: Iterator,
{
    /// Construct a new input wrapper.
    pub fn new(it: I) -> Self {
        Self { it, buf: None }
    }
}

impl<I> Input<I>
where
    I: Iterator,
    I::Item: TryIntoInput,
{
    /// Get the next item in the parser.
    // XXX For now, shut up Clippy. Eventually,
    // change the public interface or impl
    // iterator.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Result<Option<String>, InputError> {
        if let Some(item) = self.buf.take() {
            return Ok(Some(item.try_into_string()?));
        }

        let item = match self.it.next() {
            Some(item) => item,
            None => return Ok(None),
        };

        Ok(Some(item.try_into_string()?))
    }

    /// Get the next os string from the input.
    pub fn next_os(&mut self) -> Option<OsString> {
        if let Some(item) = self.buf.take() {
            return Some(item.into_os_string());
        }

        let item = match self.it.next() {
            Some(item) => item,
            None => return None,
        };

        Some(item.into_os_string())
    }

    /// Take the next argument unless it looks like a switch.
    pub fn next_unless_switch(&mut self) -> Result<Option<String>, InputError> {
        match self.peek() {
            Some(s) if s.starts_with('-') => Ok(None),
            _ => self.next(),
        }
    }

    /// Take the next argument unless it looks like a switch.
    pub fn next_unless_switch_os(&mut self) -> Option<OsString> {
        match self.peek() {
            Some(s) if s.starts_with('-') => None,
            _ => self.next_os(),
        }
    }

    /// Get the rest of available items.
    pub fn rest(&mut self) -> Result<Vec<String>, InputError> {
        let mut buf = Vec::new();

        if let Some(item) = self.buf.take() {
            buf.push(item.try_into_string()?);
        }

        for item in &mut self.it {
            buf.push(item.try_into_string()?);
        }

        Ok(buf)
    }

    /// Get the rest of available items as raw strings.
    pub fn rest_os(&mut self) -> Vec<OsString> {
        let mut buf = Vec::new();

        if let Some(item) = self.buf.take() {
            buf.push(item.into_os_string());
        }

        for item in &mut self.it {
            buf.push(item.into_os_string());
        }

        buf
    }

    fn peek(&mut self) -> Option<&str> {
        if self.buf.is_none() {
            self.buf = self.it.next();
        }

        let item = match self.buf.as_ref() {
            Some(item) => item,
            None => return None,
        };

        item.try_as_str().ok()
    }
}

#[derive(Debug)]
pub struct InputError(());

impl fmt::Display for InputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "encounted non-valid unicode in input")
    }
}

impl error::Error for InputError {}

/// Trait implemented by types that can be parsed to the `parse` function of an
/// arguments structure.
///
/// This trait is sealed, so that it cannot be implemented outside of the
/// argwerk crate.
///
/// See [define][crate::define] for how its used.
pub trait TryIntoInput: self::internal::Sealed {
    #[doc(hidden)]
    fn try_as_str(&self) -> Result<&str, InputError>;

    #[doc(hidden)]
    fn try_into_string(self) -> Result<String, InputError>;

    #[doc(hidden)]
    fn into_os_string(self) -> OsString;
}

impl TryIntoInput for String {
    #[inline]
    fn try_as_str(&self) -> Result<&str, InputError> {
        Ok(self.as_str())
    }

    #[inline]
    fn try_into_string(self) -> Result<String, InputError> {
        Ok(self)
    }

    #[inline]
    fn into_os_string(self) -> OsString {
        OsString::from(self)
    }
}

impl TryIntoInput for &str {
    #[inline]
    fn try_as_str(&self) -> Result<&str, InputError> {
        Ok(*self)
    }

    #[inline]
    fn try_into_string(self) -> Result<String, InputError> {
        Ok(self.to_owned())
    }

    #[inline]
    fn into_os_string(self) -> OsString {
        OsString::from(self)
    }
}

impl TryIntoInput for OsString {
    #[inline]
    fn try_as_str(&self) -> Result<&str, InputError> {
        self.to_str().ok_or(InputError(()))
    }

    #[inline]
    fn try_into_string(self) -> Result<String, InputError> {
        self.into_string().map_err(|_| InputError(()))
    }

    #[inline]
    fn into_os_string(self) -> OsString {
        self
    }
}

impl TryIntoInput for &OsStr {
    #[inline]
    fn try_as_str(&self) -> Result<&str, InputError> {
        self.to_str().ok_or(InputError(()))
    }

    #[inline]
    fn try_into_string(self) -> Result<String, InputError> {
        Ok(self.to_str().ok_or(InputError(()))?.to_owned())
    }

    #[inline]
    fn into_os_string(self) -> OsString {
        self.to_owned()
    }
}

mod internal {
    pub trait Sealed {}

    impl<T> Sealed for T where T: super::TryIntoInput {}
}
