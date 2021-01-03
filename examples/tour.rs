fn main() -> Result<(), argwerk::Error> {
    let args = argwerk::parse! {
        /// A command touring the capabilities of argwerk.
        "tour [-h]" {
            help: bool,
            file: Option<String>,
            input: Option<String>,
            limit: usize = 42,
            positional: Option<(String, Option<String>)>,
            rest: Vec<String>,
        }
        /// Prints the help.
        ///
        /// This includes:
        ///    * All the available switches.
        ///    * All the available positional arguments.
        ///    * Whatever else the developer decided to put in here! We even support wrapping comments which are overly long.
        "-h" | "--help" => {
            help = true;
            print_help();
            Ok(())
        }
        /// Limit the number of things by <n>.
        "--limit" | "-l", n => {
            limit = str::parse(&n)?;
            Ok(())
        }
        /// Write to the file specified by <path>.
        "--file", path if !file.is_some() => {
            file = Some(path);
            Ok(())
        }
        /// Read from the specified input.
        "--input", #[option] path => {
            input = path;
            Ok(())
        }
        /// Takes argument at <foo> and <bar>.
        ///
        ///    * This is an indented message. The first alphanumeric character determines the indentation to use.
        [foo, #[option] bar, #[rest] args] if positional.is_none() => {
            positional = Some((foo, bar));
            rest = args;
            Ok(())
        }
    }?;

    dbg!(args);
    Ok(())
}
