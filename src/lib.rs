// 6502 assembler.
// Should eventually be a two pass assembler to support labels and
// org.
//
// Note: This is assumed to run client side, so little effort has been
// made to deal with DoS from inputs.

// TODO: tricky remaining issues:
// - jumps. relative vs abs?
// - org. locate here vs placefill upto
// - variable namespace?
use regex::Regex;

pub type Binary = Vec<u8>;

fn read_val(v: &str) -> Result<u16, String> {
    // read a single numeric value, either hex or decimal
    if v.len() == 0 {
        return Err("no input.".to_string());
    }
    let (base, rest) = if &v[0..1] == "$" {
        (16, &v[1..])
    } else {
        (10, v)
    };
    match u16::from_str_radix(rest, base) {
        Ok(v) => Ok(v),
        Err(e) => Err(format!("failed to parse '{rest}' as value")),
    }
}

// Holds opcode bytes for instructions in each
// supported mode.
// Using a struct-like enum helps avoid missing
// cases.
enum Opcodes {
    Group1 {
        imm: u8,  // adc #oper
        zp: u8,   // adc oper,  < 256
        zpx: u8,  // adc oper,x < 256
        abs: u8,  // adc oper
        absx: u8, // adc oper,x
        absy: u8, // adc oper,y
        indx: u8, // adc (oper,x)
        indy: u8, // adc (oper), y
    }
}

impl Opcodes {
    pub fn all(&self) -> Vec<u8> {
        match *self {
            Opcodes::Group1 {imm, zp, zpx, abs, absx, absy, indx, indy}
                => vec![imm, zp, zpx, abs, absx, absy, indx, indy],
        }
    }
}

fn u8s(v: u16) -> Result<u8, String> {
    // safe u16->u8
    if v < 256 {
        Ok(v as u8)
    } else {
        Err(format!("{v} too large for byte."))
    }
}

fn u8b(v: u16) -> Vec<u8> {
    assert!(v <= 256);
    vec![v as u8]
}

fn u16b(v: u16) -> Vec<u8> {
    // byte order for argument (little endian)
    vec![(v & 0xFF) as u8, (v>>8) as u8]
}

fn encode(name: &str, op: Operand) -> Result<Binary, String> {
    // Order matters, as index is also the instruction bits.
    // ora -> 000, and = 001 etc
    const GRP1 : &[&str] = &[
        "ora", "and", "eor", "adc", 
        "sta", "lda", "cmp", "sbc",
    ];
    const GRP2 : &[&str] = &[
        "asl", "rol", "lsr", "ror",
        "stx", "ldx", "dec", "inc",
    ];
    const GRP3 : &[&str] = &[ 
        "bit", "jmp", "jmp", /*jmp abs*/ "sty",
        "ldy", "cpy", "cpx",
    ];
    const REST : &[(&str, u8)] = &[
        ("brk", 0x00),
    // // Single byte instructions
    // // Branches
    // BranchPlus, // BPL,
    // BranchMinus, // BMI,
    // BranchOverflowClear, // BVC,
    // BranchOverflowSet,// BVS,
    // BranchCarryClear, // BCC,
    // BranchCarrySet, // BCS,
    // BranchNE, // BNE,
    // BranchEQ, // BEQ,
    // // Interrupts etc
    // Break,               // BRK
    // JumpSubroutine,      // JSR
    // ReturnFromInterrupt, // RTI
    // ReturnFromSubroutine,

    // // Rest
    // PushStatus,
    // PullStatus,
    // PushAcc,
    // PullAcc,
    // DecY,
    // TransferAccY,
    // IncY,
    // IncX,

    // CarryClear,
    // CarrySet,
    // IntDisableClear,
    // IntDisableSet,
    // TransferYAcc,
    // OverflowClear,
    // DecimalClear,
    // DecimalSet,

    // TransferXAcc,
    // TransferXStack,
    // TransferAccX,
    // TransferStackX,
    // DecX,
    // Nop,
    // let
    ];

    let (group, opbits) = if let Some(p) = GRP1.iter().position(|&n| n == name) {
        (1, p)
    } else if let Some(p) = GRP2.iter().position(|&n| n == name) {
        (2, p)
    } else if let Some(p) = GRP3.iter().position(|&n| n == name) {
        // group "3" encodes with group bits 00
        (0, p)
    } else {
        let g = REST.iter().find(|x| x.0 == name);
        match g {
            Some((_, byte)) => { 
                return Ok(vec![*byte]);
            },
            _ => {
                return Err(format!("Unknown instruction: {name}"));
            }
        }
    };

    // TODO: handle jump exceptions. add tests.

    // TODO: check addressing mode compatibility, determine address mode bits.
    let (mode, mut arg) = match (group, op) {
        // Group 1
        (1, Operand::IndirectX(x)) => (0, vec![x]),
        (1, Operand::Absolute(x)) => if x < 256 {
            (1, u8b(x))  // ZPG
        } else {
            (3, u16b(x))  // Absolute
        },
        (1, Operand::Immediate(x)) => (2, vec![x]),
        (1, Operand::IndirectY(x)) => (4, vec![x]),
        (1, Operand::AbsX(x)) => if x < 256 {
            (5, u8b(x)) // ZPX
        } else {
            (7, u16b(x)) // AbsX
        },
        (1, Operand::AbsY(x)) => (6, u16b(x)),

        // Group 2
        // Group 3 aka bit 0
        _ => {
            return Err(format!("Unsupported (op, arg) pair ({name}, {op:?})"));
        },
    };
    assert!(opbits <= 7);
    assert!(mode <= 7);
    assert!(group <= 3);
    // AAA is the opcode
    // BBB is the addressing mode
    // CC is the instr group
    let opcode : u8 = ((opbits << 5) | (mode << 2) | group) as u8;
    
    let mut result = vec![opcode];
    result.append(&mut arg);
    Ok(result)



}

#[derive(Debug, PartialEq, Clone, Copy)]
enum Operand {
    None,
    Immediate(u8), // #val
    Absolute(u16),  // val. can be zp if small
    AbsX(u16),      // val, X, can be zp if small
    AbsY(u16),      // val, Y
    IndirectX(u8), // (oper,X)
    IndirectY(u8), // (oper), Y
}

impl Operand {
    fn maybe_re(pattern: &str) -> Result<regex::Regex, String> {
        match Regex::new(pattern) {
            Ok(p) => Ok(p),
            Err(_) => Err(format!("invalid regex: '{pattern}'")),
        }
    }
    // Input is expected to have whitespace and comments removed
    pub fn read(arg: &str) -> Result<Operand, String> {
        if arg.len() == 0 {
            return Ok(Operand::None);
        }
        // Indirects
        if let Some(v) = Self::maybe_re("\\((.*),x\\)")?.captures(arg) {
            let arg = v.get(1).unwrap().as_str();
            let arg = read_val(arg)?;
            return Ok(Operand::IndirectX(u8s(arg)?));
        }
        if let Some(v) = Self::maybe_re("\\((.*)\\),y")?.captures(arg) {
            let arg = v.get(1).unwrap().as_str();
            println!("indy arg: {arg}");
            let arg = read_val(arg)?;
            return Ok(Operand::IndirectY(u8s(arg)?));
        }
        // ABS X,Y
        if let Some(v) = Self::maybe_re("(.*),x")?.captures(arg) {
            let arg = v.get(1).unwrap().as_str();
            let arg = read_val(arg)?;
            return Ok(Operand::AbsX(arg));
        }
        if let Some(v) = Self::maybe_re("(.*),y")?.captures(arg) {
            let arg = v.get(1).unwrap().as_str();
            let arg = read_val(arg)?;
            return Ok(Operand::AbsY(arg));
        }
        Ok(match arg.strip_prefix("#") {
            Some(v) => {
                let v = read_val(v)?;
                if v >= 256 {
                    return Err(format!("{arg} is too large for immediate (1byte)"));
                }
                let v = v as u8;
                Operand::Immediate(v)
            }
            _ => Operand::Absolute(read_val(arg)?),
        })
    }
}

// Handles the result of parsing, not necessarily valid yet.
enum Line {
    // Labels start with a dot, and are followed by a colon
    Label(String),
    Variable(String, u16),
    Opcode(String, Operand),
    Db(Vec<u8>),
    None,
}

impl Line {
    // This function performs the opcode + operand validation and lookup. 
    pub fn asm(&self) -> Result<Vec<u8>, String> {
        match self {
            Line::None |
            Line::Label(_) => Ok(Vec::new()),
            Line::Variable(_, _) => panic!("unimplemented"),
            Line::Opcode(op, v) => {
                encode(op, *v)
            }
            Line::Db(v) => Ok(v.clone()),
        }
    }
}

// inputs are expected to be small enough to fit in memory
// tokenizer handles only canonicalized (lower case) inputs.
fn tokenize(input: &str) -> Result<Vec<Line>, String> {
    let mut result = Vec::new();

    fn strip_comment(line: &str) -> &str {
        let c = line.find(';');
        match c {
            Some(i) => &line[0..i],
            None => line,
        }
    }
    fn tok(line: &str) -> Result<Line, String> {
        let line = line.trim();
        let line = strip_comment(&line);
        let parts :Vec<_> = line.split(" ").collect();
        match parts[0] {
            "db" => {
                let mut vals : Vec<u8> = Vec::with_capacity(parts.len());
                for i in 1 .. parts.len() {
                    let v = read_val(parts[i])?;
                    if v > 0xff {
                        return Err(format!(
                                "{} is beyond the size of byte.", v));
                    } else {
                        vals.push((v & 0xff) as u8);
                    }
                };
                Ok(Line::Db(vals))
            }
            name => {
                // opcode handler.
                let arg = parts[1..].join("");
                let operand = Operand::read(&arg)?;
                Ok(Line::Opcode(name.to_string(), operand))
            }
            _ => Err(format!("unknown token: {}", parts[0])),
        }
    }

    for (i, v) in input.lines().enumerate() {
        let v = match tok(v) {
            Err(v) => {
                return Err(format!("line {i}: {v}"));
            }
            Ok(v) => v,
        };
        result.push(v);
    }

    Ok(result)
}

pub fn assemble(input: &str) -> Result<Binary, String> {
    let input = input.to_lowercase();
    let tokens = tokenize(&input)?;

    // Simple 1 pass.
    let mut output = Vec::new();
    for line in tokens {
        let mut bytes = line.asm()?;
        output.append(&mut bytes);
    }

    Ok(output)
}

#[cfg(test)]
mod test_operand {
    use super::*;

    #[test]
    fn test_imm() {
        assert_eq!(
            Ok(Operand::Immediate(10)),
            Operand::read("#10"));
        assert_eq!(
            Ok(Operand::Immediate(0x20)),
            Operand::read("#$20"));
    }

    #[test]
    fn test_abs() {
        assert_eq!(
            Ok(Operand::Absolute(0xdead)),
            Operand::read("$dead"));
    }
}

#[cfg(test)]
mod test_tok {
}

#[cfg(test)]
mod test_asm {
    use super::*;

    #[test]
    fn test_db() {
        let cases = &[
            (vec![10], "db 10"),
            (vec![16], "db $10"),
            (vec![5, 2, 10], "db 5 2 $A"),
        ];
        for (want, input) in cases {
            let res = assemble(input).expect("asm failed");
            assert_eq!(*want, res);
        }
    }

    #[test]
    fn test_implied_brk() {
        // break is a simple opcode, no inputs and assembles to 00.
        assert_eq!(
            Ok(vec![0]),
            assemble("BRK"));
    }

    #[test]
    fn test_comment() {
        assert_eq!(
            Ok(vec![10]),
            assemble("db 10; this is a comment"));
    }

    // all group 1 modes(8) for adc
    #[test]
    fn test_mode_adc_imm() {
        assert_eq!(  // immediate
            Ok(vec![0x69, 0xED]),
            assemble("adc #$ED"));
    }
    #[test]
    fn test_adc_zpg() {
        assert_eq!(  // zpg
            Ok(vec![0x65, 0xFF]),
            assemble("adc $FF"));
    }
    #[test]
    fn test_adc_zpgx() {
        assert_eq!(  // zpg, x
            Ok(vec![0x75, 0xFF]),
            assemble("adc $FF,x"));
    }
    #[test]
    fn test_adc_abs() {
        assert_eq!(  // abs
            Ok(vec![0x6d, 0xad, 0xde]),
            assemble("adc $dead"));
    }
    #[test]
    fn test_adc_absx() {
        assert_eq!(  // abs,x
            Ok(vec![0x7d, 0xad, 0xde]),
            assemble("adc $dead,x"));
    }
    #[test]
    fn test_adc_absy() {
        assert_eq!(  // abs,y
            Ok(vec![0x79, 0xad, 0xde]),
            assemble("adc $dead,y"));
    }
    #[test]
    fn test_adc_indx() {
        assert_eq!(  // ind x
            Ok(vec![0x61, 0xde]),
            assemble("adc ($de,x)"));
    }
    #[test]
    fn test_adc_indy() {
        assert_eq!(  // ind y
            Ok(vec![0x71, 0xde]),
            assemble("adc ($de),y"));
    }
}
