#!/usr/bin/env python3
"""Emit a Lean section for one function of a RISC-V object file.

For function NAME (symbol SYM) it emits:
  * NAME_words : the raw .text words of the function (from the ELF bytes),
  * NAME_llvm  : the program as decoded by llvm-objdump (independent decoder),
                 `none` for words LLVM shows as `unimp`,
  * NAME       : the Program (based at 0; all control flow is pc-relative),
  * NAME_decode: kernel-checked agreement of our decoder with LLVM,
  * per-address @[simp] fetch lemmas and base/length lemmas.

usage: gen_lean_fn.py OBJ SYM NAME
"""
import re
import subprocess
import sys
import tempfile

obj, sym, name = sys.argv[1], sys.argv[2], sys.argv[3]
REG = {"zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4, "t0": 5, "t1": 6, "t2": 7,
       "s0": 8, "s1": 9, **{f"a{i}": 10 + i for i in range(8)},
       **{f"s{i}": 16 + i for i in range(2, 12)}, **{f"t{i}": 25 + i for i in range(3, 7)}}

dis = subprocess.run(["llvm-objdump", "-d", "-M", "no-aliases", obj],
                     capture_output=True, text=True, check=True).stdout
# raw bytes of .text, independently of the disassembly listing
with tempfile.NamedTemporaryFile(suffix=".bin") as tf:
    subprocess.run(["llvm-objcopy", "-O", "binary", "--only-section=.text", obj, tf.name], check=True)
    raw = open(tf.name, "rb").read()

lines, inside, start = [], False, None
for line in dis.splitlines():
    m = re.match(r"^([0-9a-f]+) <(.+)>:$", line)
    if m:
        inside = m[2] == sym
        if inside:
            start = int(m[1], 16)
        continue
    if inside:
        m = re.match(r"\s*([0-9a-f]+):\s+([0-9a-f]{8})\s+(\S+)\s*(.*)", line)
        if m:
            lines.append((int(m[1], 16), int(m[2], 16), m[3], m[4]))
assert lines, f"symbol {sym} not found"

r = lambda x: REG[x]
imm = lambda x: int(x, 0)
words, out = [], []
for addr, word, op, args in lines:
    raw_word = int.from_bytes(raw[addr:addr + 4], "little")
    assert raw_word == word, f"objdump bytes differ from .text bytes at {addr:#x}"
    words.append(word)
    a = [x.strip() for x in re.sub(r"<.*>", "", args).split(",") if x.strip()]
    rel = lambda t: imm(t) - addr
    if op in ("addi", "xori", "andi", "ori", "sltiu"):
        out.append(f"some (.{op} {r(a[0])} {r(a[1])} {imm(a[2]) & 0xfff}#12)")
    elif op in ("slli", "srli", "srai"):
        out.append(f"some (.{op} {r(a[0])} {r(a[1])} {imm(a[2])}#6)")
    elif op == "srliw":
        out.append(f"some (.srliw {r(a[0])} {r(a[1])} {imm(a[2])}#5)")
    elif op == "lui":
        out.append(f"some (.lui {r(a[0])} {imm(a[1]) & 0xfffff}#20)")
    elif op in ("add", "sub", "sll", "sltu", "xor", "or", "and"):
        out.append(f"some (.{op} {r(a[0])} {r(a[1])} {r(a[2])})")
    elif op in ("bgeu", "bltu", "beq", "bne", "blt"):
        out.append(f"some (.{op} {r(a[0])} {r(a[1])} {rel(a[2]) & 0x1fff}#13)")
    elif op == "jal":
        out.append(f"some (.jal {r(a[0])} {rel(a[1]) & 0x1fffff}#21)")
    elif op in ("jalr", "lb", "lbu", "ld", "sb", "sd"):
        mm = re.match(r"(-?0x[0-9a-f]+|-?\d+)\((\w+)\)", a[1])
        off, base = imm(mm[1]) & 0xfff, r(mm[2])
        if op in ("sb", "sd"):   # objdump: sX rs2, off(rs1)
            out.append(f"some (.{op} {base} {r(a[0])} {off}#12)")
        else:
            out.append(f"some (.{op} {r(a[0])} {base} {off}#12)")
    elif op == "unimp":
        out.append("none")
    else:
        sys.exit(f"unsupported instruction {op}")

n = len(words)
print(f"/-! ### `{sym}`: {n} instructions at .text+{start:#x} (relocated to 0) -/\n")
print(f"def {name}_words : List (BitVec 32) :=\n  [" +
      ",\n   ".join("0x%08x#32" % w for w in words) + "]\n")
print(f"/-- `{sym}` as decoded by llvm-objdump (`none` = `unimp`). -/")
print(f"def {name}_llvm : List (Option Instr) :=\n  [" + ",\n   ".join(out) + "]\n")
print(f"def {name} : Program := ⟨0, {name}_words⟩\n")
print(f"/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/")
print(f"theorem {name}_decode : {name}_words.map decode = {name}_llvm := by decide\n")
print(f"@[simp] theorem {name}_base : {name}.base = 0#64 := rfl")
print(f"@[simp] theorem {name}_len : {name}.words.length = {n} := rfl\n")
for k, i in enumerate(out):
    print(f"@[simp] theorem {name}_fetch_{k} : {name}.fetch {4 * k}#64 = {i} := by decide")
print()
