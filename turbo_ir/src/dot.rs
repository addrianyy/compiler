use std::io::Write;
use std::process::{Command, Stdio};

pub fn save_graph(graph: &str, output_path: &str) {
    let dot_position = output_path.rfind('.').expect("`output_path` doesn't have an extension.");
    let format       = &output_path[dot_position + 1..];

    assert!(!format.is_empty(), "Invalid file format.");

    let process = Command::new("dot")
        .args(&[&format!("-T{}", format), "-o", output_path])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn();

    if let Ok(mut process) = process {
        {
            let stdin = process.stdin.as_mut()
                .expect("Getting `dot` stdin failed.");

            stdin.write_all(graph.as_bytes())
                .expect("Writing to `dot` stdin failed.");
        }

        let output = process.wait_with_output()
            .expect("Waiting for `dot` failed.");

        let no_output = output.stderr.is_empty() && output.stdout.is_empty();
        if !no_output {
            println!("{}", String::from_utf8_lossy(&output.stdout));
            println!("{}", String::from_utf8_lossy(&output.stderr));
        }

        assert!(output.status.success() && no_output,
                "`dot` failed to generate graph.");
    } else {
        println!("WARNING: Failed to run `dot`, it's probably not installed.");
    }
}
