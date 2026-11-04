mod bridge;
use serde_json::json;
use std::io::{self, BufRead, Write};

fn main() -> Result<(), String> {
    if std::env::args().len() != 1 {
        return Err("timing authorization is supplied per JSON request".into());
    }
    let mut bridge = bridge::Bridge::new(false);
    let mut stdout = io::stdout().lock();
    for line in io::stdin().lock().lines() {
        let line = line.map_err(|e| e.to_string())?;
        let result = serde_json::from_str(&line)
            .map_err(|e| e.to_string())
            .and_then(|r| bridge.command(r));
        let response = match result {
            Ok(value) => json!({"ok":true,"result":value}),
            Err(error) => json!({"ok":false,"error":error}),
        };
        writeln!(stdout, "{response}").map_err(|e| e.to_string())?;
        stdout.flush().map_err(|e| e.to_string())?;
    }
    Ok(())
}
