pub fn runtime_function(name: &str) -> Option<usize> {
    Some(match name {
        "print" => print as usize,
        _       => return None,
    })
}

unsafe extern "win64" fn print(buffer: *const u8) {
    let mut size = 0;

    loop {
        if *buffer.add(size) == 0 {
            break;
        }

        size += 1;
    }

    let slice = std::slice::from_raw_parts(buffer, size);

    if let Ok(string) = std::str::from_utf8(slice) {
        println!("{}", string);
    }
}
