use colored::Colorize;


pub fn error(lvl: &str, msg: &str) {
    println![ "{}{}{}{}", "error:".red().bold(), lvl.red().bold(), ": ".red().bold(), msg.red() ];
}
