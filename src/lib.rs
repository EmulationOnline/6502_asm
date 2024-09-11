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
        Err(e) => Err(format!("failed to parse '{rest}' as base {base} value")),
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
        "ora"/*fake placeholder for 0*/, "bit", "jmp", "jmp", /*jmp abs*/ "sty",
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

    fn badmode(name: &str, arg: Operand) -> String {
        format!("Unsupported (op, arg) pair ({name}, {arg:?})")
    }

    // jmp instructions dont follow the rule
    if name == "jmp" {
        let (opcode, bytes) = match op {
            Operand::Indirect(x) => {
                (0x6c, u16b(x))
            },
            Operand::Absolute(x) => {
                (0x4c, u16b(x))
            },
            _ => {
                return Err(badmode(name, op));
            }
        };
        return Ok(vec![opcode, bytes[0], bytes[1]]);
    }

    let (mode, mut arg) = match group {
        // Group 1
        1 => match op {
            Operand::IndirectX(x) => (0, vec![x]),
            Operand::Absolute(x) => if x < 256 {
                (1, u8b(x))  // ZPG
            } else {
                (3, u16b(x))  // Absolute
            },
            Operand::Immediate(x) => (2, vec![x]),
            Operand::IndirectY(x) => (4, vec![x]),
            Operand::AbsX(x) => if x < 256 {
                (5, u8b(x)) // ZPX
            } else {
                (7, u16b(x)) // AbsX
            },
            Operand::AbsY(x) => (6, u16b(x)),
            _ => { return Err(badmode(name, op)); },
        },
        2 => match op {
            Operand::Immediate(x) => (0, vec![x]),
            Operand::Absolute(x) => if x < 256 {
                (1, u8b(x))  // zp
            } else {
                (3, u16b(x)) // abs
            },
            Operand::Acc => (2, vec![]),
            Operand::AbsY(x) => if x < 256 {
                (5, u8b(x))  // zpy
            } else {
                (7, u16b(x)) // abs y
            },
            _ => { return Err(badmode(name, op)); },
        }
        // Group 3 aka bit 0
        0 => match op {
             Operand::Immediate(x) => (0, vec![x]),
             Operand::Absolute(x) => if x < 256 {
                 // zp
                 (1, u8b(x))
             } else {
                 // abs
                 (3, u16b(x))
             },
             Operand::AbsX(x) => if x < 256 {
                 // zp x
                 (5, u8b(x))
             } else {
                 (7, u16b(x))
             }
             _ => { return Err(badmode(name, op)); },
        },
        _ => { return Err(badmode(name, op)); },
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
    Acc,           // lsr a
    Immediate(u8), // #val
    Absolute(u16),  // val. can be zp if small
    AbsX(u16),      // val, X, can be zp if small
    AbsY(u16),      // val, Y
    IndirectX(u8), // (oper,X)
    IndirectY(u8), // (oper), Y
    Indirect(u16),  // (oper)  // used only for jmp
                   
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
        if arg == "a" {
            return Ok(Operand::Acc);
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
        // Indirect for jmp
        if let Some(v) = Self::maybe_re("\\((.*)\\)")?.captures(arg) {
            let arg = v.get(1).unwrap().as_str();
            let arg = read_val(arg)?;
            return Ok(Operand::Indirect(arg));
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
        assert_eq!(  // zpg, x
            Ok(vec![0x75, 0xFF]),
            assemble("adc 255, x"));
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

    #[test]
    fn test_grp2_modes() {
        assert_eq!(  // imm
            Ok(vec![0xA2, 10]),
            assemble("ldx #10"));
        assert_eq!(  // zpg
            Ok(vec![0xA6, 0xfa]),
            assemble("ldx $FA"));
        assert_eq!(  // zp,y
            Ok(vec![0xb6, 0xfa]),
            assemble("ldx $FA,y"));
        assert_eq!(  // abs
            Ok(vec![0xae, 0xfe, 0xca]),
            assemble("ldx $cafe"));
        assert_eq!(  // abs,y
            Ok(vec![0xbe, 0xeb, 0xbe]),
            assemble("ldx $beeb,y"));
        // some instructions support acc mode
        assert_eq!(  // lsr a
            Ok(vec![0x4a]),
                assemble("lsr a"));
    }


    #[test]
    fn test_grp2_badmode() {
        // ldx is a group 2 instruction, which doesnt support
        // abs,x
        assert!(
            assemble("ldx $ff, x").is_err());
    }

    #[test]
    fn test_jmps() {
        assert_eq!(
            Ok(vec![0x6c, 0xba, 0xda]),
            assemble("jmp ($daba)"));
        assert_eq!(
            Ok(vec![0x4c, 0xda, 0xd0]),
            assemble("jmp $d0da"));
    }

    #[test]
    fn test_grp3_ldy() {
        // ldy supports all group 3 addressing modes
        assert_eq!(  // imm
            Ok(vec![0xA0, 0xde]),
            assemble("ldy #$de"));
        assert_eq!(  // zp
            Ok(vec![0xA4, 10]),
            assemble("ldy 10"));
        assert_eq!(  // zp x
            Ok(vec![0xB4, 100]),
            assemble("ldy 100,x"));
        assert_eq!(  // abs
            Ok(vec![0xac, 0xb0, 0xda]),
            assemble("ldy $dab0"));
        assert_eq!(  // abs x
            Ok(vec![0xbc, 0xb0, 0xda]),
            assemble("ldy $dab0, x"));
    }
}
