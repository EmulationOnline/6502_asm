// 6502 assembler.
// Should eventually be a two pass assembler to support labels and
// org.
//
// Note: This is assumed to run client side, so little effort has been
// made to deal with DoS from inputs.

pub type Binary = Vec<u8>;

enum Operand {
    Immediate(u16),
    Absolute(u16),
}

enum Line {
    // Labels start with a dot, and are followed by a colon
    Label(String),
    Variable(String, u16),
    Opcode(String, Operand),
    Db(Vec<u8>),
    None,
}

impl Line {
    pub fn asm(&self) -> Vec<u8> {
        match self {
            Line::None |
            Line::Label(_) => Vec::new(),
            Line::Variable(_, _) |
            Line::Opcode(_, _) => panic!("unimplemented"),
            Line::Db(v) => v.clone(),
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
    fn read_val(v: &str) -> Result<u16, String> {
        if v.len() == 0 {
            return Err("no input.".to_string());
        }
        // read a single numeric value, either hex or decimal
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
        let mut bytes = line.asm();
        output.append(&mut bytes);
    }

    Ok(output)
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
    fn test_opcodes() {
        // all the supported opcodes
        const TABLE : &[
            (&str, &[u8])] = &[
        ];
    }

    #[test]
    fn test_comment() {
        assert_eq!(
            Ok(vec![10]),
            assemble("db 10; this is a comment"));
    }
}
