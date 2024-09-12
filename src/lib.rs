// 6502 assembler.
// Should eventually be a two pass assembler to support labels and
// org.
//
// Note: This is assumed to run client side, so little effort has been
// made to deal with DoS from inputs.

// TODO: remaining issues:
// - branches. all relative. need 2 pass
// - constants

use regex::Regex;
use std::collections::HashMap;

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

fn branch_opcode(name: &str) -> Option<u8> {
    const BRANCHES : &[(&str, u8)] = &[
        ("bpl", 0x10),
        ("bmi", 0x30),
        ("bvc", 0x50),
        ("bvs", 0x70),
        ("bcc", 0x90),
        ("bcs", 0xB0),
        ("bne", 0xD0),
        ("beq", 0xF0),
    ];
    for (n, b) in BRANCHES {
        if *n == name {
            return Some(*b);
        }
    }
    None
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
        // Calls
        ("jsr", 0x20),
        ("rti", 0x40),
        ("rts", 0x60),
        // Others
        ("php", 0x08),
        ("plp", 0x28),
        ("pha", 0x48),
        ("pla", 0x68),
        ("dey", 0x88),
        ("tay", 0xA8),
        ("iny", 0xC8),
        ("inx", 0xE8),

        ("clc", 0x18),
        ("sec", 0x38),
        ("cli", 0x58),
        ("sei", 0x78),
        ("tya", 0x98),
        ("clv", 0xB8),
        ("cld", 0xD8),
        ("sed", 0xF8),

        ("txa", 0x8A),
        ("txs", 0x9A),
        ("tax", 0xAA),
        ("tsx", 0xBA),
        ("dex", 0xCA),
        ("nop", 0xEA),
    ];

    fn badmode(name: &str, arg: Operand) -> String {
        format!("Unsupported (op, arg) pair ({name}, {arg:?})")
    }

    // Branches dont follow the group pattern, 1 byte opcode + 1 byte arg
    if let Some(opcode) = branch_opcode(name) {
        match op {
            Operand::Immediate(v) => {
                return Ok(vec![opcode, v]);
            }, 
            _ => { return Err(badmode(name, op)); },
        }
    }

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
                return Err(format!("Unknown instruction: '{name}'"));
            }
        }
    };


    // jmp instructions dont follow the group pattern. 1 byte opcode + 2 bytes arg
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

#[derive(Debug, PartialEq, Clone)]
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
    Label(String),  // .name
                   
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
        if arg.starts_with(".") {
            return Ok(Operand::Label(arg.to_string()));
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
    Org(usize),
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
            Line::Org(_) => {
                panic!("Org should not be assembled.");
            },
            Line::None |
            Line::Label(_) => Ok(Vec::new()),
            Line::Variable(_, _) => panic!("unimplemented"),
            Line::Opcode(op, v) => {
                encode(op, v.clone())
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
    fn is_label_line(word: &str) -> bool {
        // true iff this word designates a label placement.
        // starts with . and ends with :
        word.starts_with(".") && word.ends_with(":")
    }
    fn tok(line: &str) -> Result<Line, String> {
        let line = line.trim();
        let line = strip_comment(&line);
        let parts :Vec<_> = line.split(" ").collect();
        let rest = parts[1..].join("");
        match parts[0] {
            "" => Ok(Line::None),
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
            },
            "dw" => {
                // little endian u16
                let mut vals : Vec<u8> = Vec::with_capacity(parts.len()*2);
                for i in 1 .. parts.len() {
                    let v = read_val(parts[i])?;
                    let mut bytes = u16b(v);
                    vals.append(&mut bytes);
                }
                Ok(Line::Db(vals))
            },
            "org" => {
                let v = read_val(&rest)?;
                Ok(Line::Org(v as usize))
            },
            x if is_label_line(x) => {
                // Label
                if rest.len() > 0 {
                    // Fail, as the rest of the line would otherwise be silently dropped
                    return Err(format!("label '{}' must be on its own line.", parts[0]));
                }
                let label = parts[0].strip_suffix(":").unwrap();
                Ok(Line::Label(label.to_string()))
            }
            name => {
                // opcode handler.
                let operand = Operand::read(&rest)?;
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

    // Collect runs of bytes by their starting address. Output
    // will be large enough to span all assembled bytes.
    let mut org = 0;
    let mut chunks : HashMap<usize, Binary> = HashMap::new();
    let mut current = Binary::new();
    let mut min_org = usize::MAX;
    let mut max_org = 0;
    fn push (chunks: &mut HashMap<usize, Binary>, current: &mut Binary, 
        min_org: &mut usize, max_org: &mut usize,
        org: usize) {
        if current.len() > 0 {
            chunks.insert(org, current.clone());
            current.clear();
            // apply on push, since orgs can be used but empty and will
            // be ignored for size calcs
            *min_org = (*min_org).min(org);
            *max_org = (*max_org).max(org);
        }
    };

    // label name to the first byte of two bytes that need updating
    let mut label_stubs : HashMap<String, Vec<usize>> = HashMap::new();
    let mut label_vals : HashMap<String, usize> = HashMap::new();
    // Label, address position, lineno. opcode is at addr-1
    let mut branches : Vec<(String, usize, usize)> = Vec::new();

    // Pass one. Assemble as much as possible, making note where fixups
    // are needed in pass 2.
    for (line_no, line) in tokens.into_iter().enumerate() {
        match line {
            Line::Org(next_address) => {
                push(&mut chunks, &mut current, &mut min_org, &mut max_org, org);
                if chunks.contains_key(&next_address) {
                    return Err(format!("reuse of org 0x{next_address:4X} would clobber."));
                }
                org = next_address;
            },
            Line::Label(name) => {
                let address = org + current.len();
                if label_vals.contains_key(&name) {
                    return Err(format!("duplicate definition for label: {name}"));
                }
                label_vals.insert(name, address);
            },
            Line::Opcode(op, Operand::Label(labelname)) => {
                // Branches are relative(u8), everything else is absolute (u16)
                // First pass writes a 0, then second pass writes a proper value.

                let address = org + current.len() +1;
                if let Some(opcode) = branch_opcode(&op) {
                    // Relative, one byte.
                    branches.push((labelname, address, line_no));
                    let mut bytes = Line::Opcode(op, Operand::Immediate(0)).asm().unwrap();
                    current.append(&mut bytes);
                } else {
                    // Absolute, 2 bytes.

                    if !label_stubs.contains_key(&labelname) {
                        // init vector
                        label_stubs.insert(labelname.clone(), Vec::new());
                    }
                    label_stubs.get_mut(&labelname).unwrap().push(address);
                    let mut bytes = Line::Opcode(op, Operand::Absolute(0)).asm().unwrap();
                    current.append(&mut bytes);
                }

            },
            _ => {
                // simply assemble
                let mut bytes = line.asm()?;
                current.append(&mut bytes);
            }
        }
    }
    push(&mut chunks, &mut current, &mut min_org, &mut max_org, org);

    if min_org == usize::MAX {
        // no data
        return Ok(Binary::new());
    }



    // flatten chunks
    let mut output : Binary = Vec::new();
    output.resize(max_org + chunks[&max_org].len() - min_org,
        0); 
    for (start, chunk) in chunks {
        let dest = start - min_org;
        output.as_mut_slice()[dest .. dest + chunk.len()].copy_from_slice(&chunk);
    }

    // Pass two: Rewrite found labels.
    // Note, its easier to perform on the flat memory
    // Absolute references:
    for (labelname, positions) in label_stubs {
        let val = u16b(label_vals[&labelname] as u16);
        for pos in positions {
            let dest = pos - min_org;
            output.as_mut_slice()[dest .. dest+2].copy_from_slice(&val);
        }
    }
    // Relative references for branches.
    for (labelname, position, line_no) in branches {
        let branch_addr = position - 1;
        if !label_vals.contains_key(&labelname) {
            return Err(format!("cannot branch to '{labelname}' no such label."));
        }
        let label_dest = label_vals[&labelname];
        let offset : isize = (label_dest as isize - branch_addr as isize);
        if offset < -128 || offset > 127 {
            return Err(format!(
                    "Line {line_no}: branch offset out of range of signed byte [-128 to 127]"));
        }
        let offset : i8 = offset as i8;
        output[position - min_org] = offset as u8;
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
    fn test_dw() {
        let cases = &[
            (vec![0xad, 0xde], "dw $dead"),
            (vec![0xfe, 0xca, 0xbe, 0xba], "dw $cafe $babe"),
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

    #[test]
    fn test_empty_line() {
        assert_eq!(
            Ok(vec![0x10, 0x25]),
            assemble(r#"
            db $10

            db $25"#));
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

    #[test]
    fn test_single_byte_instrs() {
        let table : &[(&str, u8)]= &[
            // Interrupts etc
            ("brk", 0x00),
            ("jsr", 0x20),
            ("rti", 0x40),
            ("rts", 0x60),

            // Rest
            ("php", 0x08), // push status
            ("plp", 0x28), // pull status
            ("pha", 0x48),
            ("pla", 0x68),
            ("dey", 0x88),
            ("tay", 0xA8),
            ("iny", 0xC8),
            ("inx", 0xE8),

            ("clc", 0x18), // carry clear
            ("sec", 0x38),  // carry set 
            ("cli", 0x58),
            ("sei", 0x78),
            ("tya", 0x98),
            ("clv", 0xb8), // overflow clear
            ("cld", 0xd8), // decimal clear 
            ("sed", 0xf8),

            ("txa", 0x8a),
            ("txs", 0x9a),
            ("tax", 0xaa),
            ("tsx", 0xba),
            ("dex", 0xca),
            ("nop", 0xea),
         ];
         for (name, byte) in table {
             assert_eq!(
                 Ok(vec![*byte]),
                 assemble(name));
         }
    }

    #[test]
    fn test_branches() {
        // branches encode with a relative offset
        // each is two bytes (opcode + arg)
        assert_eq!(
            Ok(vec![
                0xb0,
                0x10, 0xFF,
                0x30, 0xFD,
                0x50, 0xFB,
                0x70, 0xF9,
                0x90, 0xF7,
                0xB0, 0xF5,
                0xD0, 0xF3,
                0xF0, 0xF1,
                0xad, 0xde,
            ]),
            assemble(r#"
            .start:
            db $b0
            bpl .start ; -1
            bmi .start ; -3
            bvc .start ; -5
            bvs .start ; -7
            bcc .start ; -9
            bcs .start ; -11
            bne .start ; -13
            beq .start ; -15
            dw $dead
            "#));


            // ("bpl", // BPL,
            // (BranchMinus, // BMI,
            // (BranchOverflowClear, // BVC,
            // (BranchOverflowSet,// BVS,
            // (BranchCarryClear, // BCC,
            // (BranchCarrySet, // BCS,
            // (BranchNE, // BNE,
            // (BranchEQ, // BEQ,
    }
    #[test]
    fn test_branch_forward() {
        assert_eq!(
            Ok(vec![0x10, 4, 0xea, 0xea, 0xea]),
            assemble(r#"
            bpl .end
            nop
            nop
            .end:
            nop"#));
    }
    #[test]
    fn test_branch_back() {
        // TODO: double check by running in asm
        assert_eq!(
            Ok(vec![0xea, 0xea, 0x10, 0xFE, 0xea, 0xea]),
            assemble(r#"
            .before:
            nop
            nop
            bpl .before
            nop
            nop"#));
    }

    #[test]
    fn test_label_assembles() {
        // unused label, should still assemble.
        assert_eq!(
            Ok(vec![0x10, 0x24]),
            assemble(".start: 
                db $10 $24"));
    }

    #[test]
    fn test_label_supports_jump() {
        assert_eq!(
            Ok(vec![0xea, 0x4c, 0x01, 0x00]),
            assemble(r#"
            nop
            .start:
            jmp .start
            "#));
    }
    #[test]
    fn test_label_start() {
        // With no org, start should be 0x0000
        // jmps are encoded directly
        assert_eq!(
            Ok(vec![
                0x4c, 0, 0
            ]),
            assemble(r#"
            .start:
              jmp .start"#));
    }

    #[test]
    fn test_label_middle() {
        // jump in the middle of a set of
        // instructions

        assert_eq!(
            Ok(vec![0x00, 0x4c, 0x01, 0x00]),
            assemble(r#"
             brk
             .target:
              jmp .target"#));
    }
    
    #[test]
    fn test_assemble_empty() {
        assert_eq!(
            Ok(vec![]),
            assemble(r#"
            org 0

            "#));
    }

    #[test]
    fn test_org_start() {
        // setting an org immediately shouldnt change the length of the
        // program. This would be done if the entire rom is meant to be loaded
        // at an offset, as is the case for some systems.
        assert_eq!(
            Ok(vec![10, 0x10]),
            assemble(r#"
            org $1000
            db 10
            db $10

            "#));
    }

    #[test]
    fn test_org_padding() {
        // if bytes are assembled, org can be used to expand output.
        let mut expected = Vec::new();
        expected.resize(1000, 0);
        assert_eq!(
            Ok(expected),
            assemble(r#"
            org 0
            db 0
            org 999
            db 0"#));
    }


    #[test]
    fn test_org_start_jump() {
        // But an org at the start can influence jumps
        assert_eq!(
            Ok(vec![0x4c, 0x00, 0x10]),
            assemble(r#"
            org $1000
            .start:
            jmp .start
            "#));
    }
}

