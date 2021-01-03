fn main() -> Result<(), argwerk::Error> {
    let args = argwerk::argwerk! {
        /// A simple test command.
        ///
        /// This is nice!
        "testcommand [-h]" {
            help: bool,
            file: Option<String>,
            limit: usize = 42,
        }
        /// Print this help.
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
    }?;

    if args.help {
        return Ok(());
    }

    Ok(())
}
