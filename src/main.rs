use asm_6502 as crt;

fn main() {
    println!("6502_asm by EmulationOnline");
    let argv :Vec<String> = std::env::args().collect();

    if argv.len() != 3 {
        println!(
            "Usage: {} filename.asm output.bin",
            argv[0]);
        std::process::exit(1);
    }
    let in_filename = &argv[1];
    let out_filename = &argv[2];

    let input = std::fs::read_to_string(&in_filename)
        .expect("Failed to read input");

    let output = crt::assemble(&input).expect(
        "Assembly failed:");

    println!("Output size: 0x{:X}({} bytes)",
        output.len(), output.len());

    std::fs::write(out_filename, output);
}
