argwerk::define! {
    /// A command touring the capabilities of argwerk.
    #[usage = "tour [-h]"]
    struct Args {
        help: bool,
        #[required = "--file must be specified"]
        file: String,
        input: Option<String>,
        limit: usize = 10,
        positional: Option<(String, Option<String>)>,
        rest: Vec<String>,
    }
    /// Prints the help.
    ///
    /// This includes:
    ///    * All the available switches.
    ///    * All the available positional arguments.
    ///    * Whatever else the developer decided to put in here! We even support wrapping comments which are overly long.
    ["-h" | "--help"] => {
        println!("{}", Args::help());
        help = true;
    }
    /// Limit the number of things by <n> (default: 10).
    ["--limit" | "-l", n] => {
        limit = str::parse(&n)?;
    }
    /// Write to the file specified by <path>.
    ["--file", path] if !file.is_some() => {
        file = Some(path);
    }
    /// Read from the specified input.
    ["--input", #[option] path] => {
        input = path;
    }
    /// Takes argument at <foo> and <bar>.
    ///
    ///    * This is an indented message. The first alphanumeric character determines the indentation to use.
    [foo, #[option] bar, #[rest] args] if positional.is_none() => {
        positional = Some((foo, bar));
        rest = args;
    }
}

fn main() -> anyhow::Result<()> {
    let args = Args::args()?;
    dbg!(args);
    Ok(())
}
