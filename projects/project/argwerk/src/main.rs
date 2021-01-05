fn main() -> anyhow::Result<()> {
    let args = argwerk::args! {
        "chat [--word <word>] [--count] [--dist] [--limit <n>]" {
            words: Vec<String>,
            count: bool = false,
            dist: bool = false,
            limit: usize = 20,
            any_word: bool = false,
            help: bool,
        }
        /// Add a word to the list to search for. This will cause `words.png` to
        /// be written and print word usage statistics to console.
        ["--word", word] => {
            words.push(word.to_lowercase());
        }
        /// Like `--word <word>`, but matches any words.
        ["--any"] => {
            any_word = true;
        }
        /// Perform overall aggregation over total word count use.
        ["--count"] => {
            count = true;
        }
        /// Write a `contributions.png` which contains the distribution of the percentage of users contributing to chat.
        ["--dist"] => {
            dist = true;
        }
        /// Limit the number of users to show (default: 20).
        ["--limit", n] => {
            limit = str::parse::<usize>(&n)?;
        }
        ["-h" | "--help"] => {
            help = true;
        }
    }?;

    dbg!(args);
    Ok(())
}
