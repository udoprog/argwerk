use clap::Clap;

/// A basic example
#[derive(Clap, Debug)]
#[clap(name = "basic")]
struct Args {
    /// Add a word to the list to search for. This will cause `words.png` to
    /// be written and print word usage statistics to console.
    #[clap(long = "word")]
    words: Vec<String>,
    /// Perform overall aggregation over total word count use.
    #[clap(long = "count")]
    count: bool,
    /// Write a `contributions.png` which contains the distribution of the percentage of users contributing to chat.
    #[clap(long = "dist")]
    dist: bool,
    /// Limit the number of users to show (default: 20).
    #[clap(long = "limit")]
    limit: usize,
    /// Like `--word <word>`, but matches any words.
    #[clap(long = "any")]
    any_word: bool,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    dbg!(args);
    Ok(())
}
