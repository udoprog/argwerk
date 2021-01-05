use argh::FromArgs;

/// A basic example
#[derive(FromArgs, Debug)]
struct Args {
    /// add a word to the list to search for. This will cause `words.png` to
    /// be written and print word usage statistics to console.
    #[argh(option, long = "word")]
    words: Vec<String>,
    /// perform overall aggregation over total word count use.
    #[argh(option, long = "count")]
    count: bool,
    /// write a `contributions.png` which contains the distribution of the percentage of users contributing to chat.
    #[argh(switch, long = "dist")]
    dist: bool,
    /// limit the number of users to show (default: 20).
    #[argh(option, long = "limit")]
    limit: usize,
    /// like `--word <word>`, but matches any words.
    #[argh(switch, long = "any")]
    any_word: bool,
}

fn main() -> anyhow::Result<()> {
    let args: Args = argh::from_env();

    dbg!(args);
    Ok(())
}
