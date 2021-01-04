use std::fmt;

pub struct Switch {
    #[doc(hidden)]
    pub init: &'static str,
    /// The documentation comments that were associated with the switch.
    pub docs: &'static [&'static str],
}

/// Helper to format a documentation snippet.
struct DocFmt<'a> {
    init: &'a str,
    docs: &'a [&'static str],
    width: usize,
    init_len: Option<usize>,
}

impl<'a> DocFmt<'a> {
    fn new(init: &'a str, docs: &'a [&'static str], width: usize) -> Self {
        Self {
            init,
            docs,
            width,
            init_len: None,
        }
    }

    fn switch(init: &'a str, docs: &'a [&'static str], width: usize, init_len: usize) -> Self {
        DocFmt {
            init,
            docs,
            width,
            init_len: Some(init_len),
        }
    }
}

impl fmt::Display for DocFmt<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.docs.is_empty() {
            textwrap(f, self.docs, self.width, &self.init, self.init_len)?;
        } else {
            write!(f, "{}", self.init)?;
        }

        Ok(())
    }
}

/// Helper that can be formatted into documentation text.
pub struct Help {
    /// The usage specifier used.
    pub usage: &'static str,
    /// The documentation strings.
    pub docs: &'static [&'static str],
    /// Switches associated with the current command.
    pub switches: &'static [Switch],
}

impl Help {
    /// Format the help with the given config.
    pub fn with_config(&self, width: usize) -> impl fmt::Display + '_ {
        WithConfig { help: self, width }
    }

    /// Internal helper to format the help with the default config.
    fn with_default(&self) -> impl fmt::Display + '_ {
        self.with_config(80)
    }
}

impl fmt::Display for Help {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.with_default().fmt(f)
    }
}

struct WithConfig<'a> {
    help: &'a Help,
    width: usize,
}

impl<'a> fmt::Display for WithConfig<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Usage: {name}", name = self.help.usage)?;

        if !self.help.docs.is_empty() {
            writeln!(f, "{}", DocFmt::new("", &self.help.docs, self.width))?;
        }

        writeln!(f)?;

        let init_len = self
            .help
            .switches
            .iter()
            .map(|d| d.init.len())
            .max()
            .unwrap_or_default();

        if !self.help.switches.is_empty() {
            writeln!(f, "Options:")?;

            for d in self.help.switches {
                writeln!(
                    f,
                    "{}",
                    DocFmt::switch(&d.init, &d.docs, self.width, init_len)
                )?;
            }
        }

        Ok(())
    }
}

/// Utility for the bytewise wrapping of text.
fn textwrap<I>(
    f: &mut fmt::Formatter<'_>,
    lines: I,
    width: usize,
    init: &str,
    init_len: Option<usize>,
) -> fmt::Result
where
    I: IntoIterator,
    I::Item: AsRef<str>,
{
    let mut it = lines.into_iter().peekable();

    let fill = init_len.unwrap_or(init.len());
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

            let init = init.take().unwrap_or_default();
            f.write_str(init)?;
            fill_spaces(f, fill.saturating_sub(init.len()))?;

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
            .take(count)
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
