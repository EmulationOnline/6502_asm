# 6502 Assembler

This is an assembler for the 6502 I wrote, initially to support
the networked 6502 I made available at 

https://chiplab.emulationonline.com/6502

## Available online

Just want to assemble your program? You can access the assembler
through your browser at https://www.emulationonline.com/systems/chiplab/6502/assembler/

## Current Features

- All official instructions are implemented
- db supports $hex or decimal literals
- db can also take a list of byte values, which will be
placed sequentially.
- labels start with a dot, and end with a colon
- dw is used to define a word (16 bit). Values are stored little endian,
which is how the 6502 typically expects them.

## Known limitations

All addressing modes for a given instruction group are assumed to be supported
with all instructions of the group. For example, group 2 instructions typically
support "a" as an argument for accumulator. stx is a group 2 instruction, yet doesn't support
"stx a".

The assembler currently assembles this without issue.

## Submitting fixes

If you notice any problems, feel free to create an issue, and optionally send
me a pull request with a fix.
