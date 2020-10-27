use std::io::Write;

pub fn save_svg_graph(graph_desc: &str, output_path: &str) {
    use std::process::{Command, Stdio};

    let mut process = Command::new("dot")
        .args(&["-Tsvg", "-o", output_path])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to run `dot`.");

    {
        let stdin = process.stdin.as_mut()
            .expect("Getting `dot` stdin failed.");

        stdin.write_all(graph_desc.as_bytes())
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
}

