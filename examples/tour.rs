use std::ffi::OsString;

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
        raw: Option<OsString>,
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
    ["--file", path] if file.is_none() => {
        file = Some(path);
    }
    /// Read from the specified input.
    ["--input", #[option] path] => {
        input = path;
    }
    /// A raw argument that passes whatever was passed in from the operating system.
    ["--raw", #[os] arg] => {
        raw = Some(arg);
    }
    /// A really long argument that exceeds usage limit and forces the documentation to wrap around with newlines.
    ["--really-really-really-long-argument", _thing] => {
    }
    /// Takes argument at <foo> and <bar>.
    ///
    ///    * This is an indented message. The first alphanumeric character determines the indentation to use.
    [first, #[option] second, #[rest] args] if positional.is_none() => {
        positional = Some((first, second));
        rest = args;
    }
}

fn main() -> anyhow::Result<()> {
    let args = Args::args()?;

    dbg!(args);
    Ok(())
}
