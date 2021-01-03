use std::fmt;

struct Doc {
    initial: Box<str>,
    docs: Vec<&'static str>,
}

impl Doc {
    fn format(&self, max_initial: usize) -> impl fmt::Display + '_ {
        DocFormat::with_max_initial(&self.initial, &self.docs, max_initial)
    }
}

/// Helper to format a documentation snippet.
struct DocFormat<'a> {
    initial: &'a str,
    docs: &'a [&'static str],
    max_initial: Option<usize>,
}

impl<'a> DocFormat<'a> {
    fn new(initial: &'a str, docs: &'a [&'static str]) -> Self {
        Self {
            initial,
            docs,
            max_initial: None,
        }
    }

    fn with_max_initial(
        initial: &'a str,
        docs: &'a [&'static str],
        max_initial: usize,
    ) -> impl fmt::Display + 'a {
        DocFormat {
            initial,
            docs,
            max_initial: Some(max_initial),
        }
    }
}

impl fmt::Display for DocFormat<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.docs.is_empty() {
            textwrap(f, self.docs, 80, &self.initial, self.max_initial)?;
        } else {
            write!(f, "{}", self.initial)?;
        }

        Ok(())
    }
}

/// Helper for constructing documentation text.
pub struct Help<'a> {
    usage: &'a str,
    docs: &'a [&'static str],
    field_docs: Vec<Doc>,
    field_initial: String,
    max_initial: usize,
}

impl<'a> Help<'a> {
    /// Construct a new help generator.
    pub fn new(usage: &'a str, docs: &'a [&'static str]) -> Self {
        Self {
            usage,
            docs,
            field_docs: Vec::new(),
            field_initial: String::new(),
            max_initial: 0,
        }
    }

    /// Get a mutable work buffer for the prefix.
    pub fn field_initial_mut(&mut self) -> &mut String {
        self.field_initial.clear();
        &mut self.field_initial
    }

    /// Add the documentation for a single fields.
    pub fn field_doc(&mut self, docs: Vec<&'static str>) {
        if !docs.is_empty() {
            self.field_initial.push_str("  ");
        }

        self.max_initial = usize::max(self.max_initial, self.field_initial.len());
        let initial = self.field_initial.clone().into();
        self.field_docs.push(Doc { initial, docs })
    }
}

impl fmt::Display for Help<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Usage: {name}", name = self.usage)?;

        if !self.docs.is_empty() {
            writeln!(f, "{}", DocFormat::new("", &self.docs))?;
        }

        writeln!(f)?;

        if !self.field_docs.is_empty() {
            writeln!(f, "Options:")?;

            for doc in &self.field_docs {
                writeln!(f, "{}", doc.format(self.max_initial))?;
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
    initial: &str,
    max_initial: Option<usize>,
) -> fmt::Result
where
    I: IntoIterator,
    I::Item: AsRef<str>,
{
    let mut it = lines.into_iter().peekable();

    let fill = max_initial.unwrap_or(initial.len());
    let mut initial = Some(initial);

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

            let initial = initial.take().unwrap_or_default();
            f.write_str(initial)?;
            fill_spaces(f, fill.saturating_sub(initial.len()))?;

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
