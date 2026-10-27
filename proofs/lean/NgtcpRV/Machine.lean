import RISCV.Instructions

/-!
# A small RV64 machine for straight-line/branching leaf functions

ALU semantics are those of `RISCV.Instructions` (opencompl/riscv-lean), which
are proven equivalent upstream to the authoritative Sail RISC-V model.

This file adds only what riscv-lean does not provide:
* a register file and program counter,
* a decoder for the RV64IM encodings used by the verified functions
  (field layout from the RISC-V Unprivileged ISA, chapter "RV32I Base
  Integer Instruction Set", and transcribed from Sail's `encdec`),
* control transfer (`BTYPE`, `JALR`), transcribed from Sail's
  `execute_BTYPE` / `execute_JALR`, including the misaligned-target fault
  raised by Sail's `jump_to` when the C extension is absent.

Instructions that the decoder does not recognise make the machine fault, so
an unsupported encoding can never be silently given the wrong meaning.
-/

namespace NgtcpRV

abbrev Reg := BitVec 5

inductive Instr where
  | addi (rd rs1 : Reg) (imm : BitVec 12)
  | xori (rd rs1 : Reg) (imm : BitVec 12)
  | andi (rd rs1 : Reg) (imm : BitVec 12)
  | ori  (rd rs1 : Reg) (imm : BitVec 12)
  | lui  (rd : Reg) (imm : BitVec 20)
  | srliw (rd rs1 : Reg) (shamt : BitVec 5)
  | srlw (rd rs1 rs2 : Reg)
  | lb   (rd rs1 : Reg) (imm : BitVec 12)
  | lbu  (rd rs1 : Reg) (imm : BitVec 12)
  | ld   (rd rs1 : Reg) (imm : BitVec 12)
  | sb   (rs1 rs2 : Reg) (imm : BitVec 12)
  | sd   (rs1 rs2 : Reg) (imm : BitVec 12)
  | blt  (rs1 rs2 : Reg) (imm : BitVec 13)
  | jal  (rd : Reg) (imm : BitVec 21)
  | slli (rd rs1 : Reg) (shamt : BitVec 6)
  | srli (rd rs1 : Reg) (shamt : BitVec 6)
  | srai (rd rs1 : Reg) (shamt : BitVec 6)
  | sltiu (rd rs1 : Reg) (imm : BitVec 12)
  | add  (rd rs1 rs2 : Reg)
  | sub  (rd rs1 rs2 : Reg)
  | sll  (rd rs1 rs2 : Reg)
  | sltu (rd rs1 rs2 : Reg)
  | xor  (rd rs1 rs2 : Reg)
  | or   (rd rs1 rs2 : Reg)
  | and  (rd rs1 rs2 : Reg)
  | bgeu (rs1 rs2 : Reg) (imm : BitVec 13)
  | bltu (rs1 rs2 : Reg) (imm : BitVec 13)
  | beq  (rs1 rs2 : Reg) (imm : BitVec 13)
  | bne  (rs1 rs2 : Reg) (imm : BitVec 13)
  | jalr (rd rs1 : Reg) (imm : BitVec 12)
  deriving DecidableEq, Repr

/-- Decode a 32-bit instruction word (RV64IM subset). -/
def decode (w : BitVec 32) : Option Instr :=
  let opcode := w.extractLsb 6 0
  let rd     : Reg := w.extractLsb 11 7
  let funct3 := w.extractLsb 14 12
  let rs1    : Reg := w.extractLsb 19 15
  let rs2    : Reg := w.extractLsb 24 20
  let funct7 := w.extractLsb 31 25
  let immI   : BitVec 12 := w.extractLsb 31 20
  let immS   : BitVec 12 := w.extractLsb 31 25 ++ w.extractLsb 11 7
  let immJ   : BitVec 21 :=
    w.extractLsb 31 31 ++ w.extractLsb 19 12 ++ w.extractLsb 20 20 ++
    w.extractLsb 30 21 ++ 0#1
  let immB   : BitVec 13 :=
    w.extractLsb 31 31 ++ w.extractLsb 7 7 ++ w.extractLsb 30 25 ++
    w.extractLsb 11 8 ++ 0#1
  if opcode = 0b0010011#7 then          -- OP-IMM
    if funct3 = 0#3 then some (.addi rd rs1 immI)
    else if funct3 = 4#3 then some (.xori rd rs1 immI)
    else if funct3 = 6#3 then some (.ori rd rs1 immI)
    else if funct3 = 7#3 then some (.andi rd rs1 immI)
    else if funct3 = 3#3 then some (.sltiu rd rs1 immI)
    else if funct3 = 1#3 ∧ w.extractLsb 31 26 = 0#6 then
      some (.slli rd rs1 (w.extractLsb 25 20))
    else if funct3 = 5#3 ∧ w.extractLsb 31 26 = 0#6 then
      some (.srli rd rs1 (w.extractLsb 25 20))
    else if funct3 = 5#3 ∧ w.extractLsb 31 26 = 16#6 then
      some (.srai rd rs1 (w.extractLsb 25 20))
    else none
  else if opcode = 0b0110011#7 then     -- OP
    if funct7 = 0#7 then
      if funct3 = 0#3 then some (.add rd rs1 rs2)
      else if funct3 = 1#3 then some (.sll rd rs1 rs2)
      else if funct3 = 3#3 then some (.sltu rd rs1 rs2)
      else if funct3 = 4#3 then some (.xor rd rs1 rs2)
      else if funct3 = 6#3 then some (.or rd rs1 rs2)
      else if funct3 = 7#3 then some (.and rd rs1 rs2)
      else none
    else if funct7 = 0b0100000#7 ∧ funct3 = 0#3 then some (.sub rd rs1 rs2)
    else none
  else if opcode = 0b1100011#7 then     -- BRANCH
    if funct3 = 0#3 then some (.beq rs1 rs2 immB)
    else if funct3 = 1#3 then some (.bne rs1 rs2 immB)
    else if funct3 = 4#3 then some (.blt rs1 rs2 immB)
    else if funct3 = 6#3 then some (.bltu rs1 rs2 immB)
    else if funct3 = 7#3 then some (.bgeu rs1 rs2 immB)
    else none
  else if opcode = 0b1100111#7 ∧ funct3 = 0#3 then  -- JALR
    some (.jalr rd rs1 immI)
  else if opcode = 0b1101111#7 then     -- JAL
    some (.jal rd immJ)
  else if opcode = 0b0110111#7 then     -- LUI
    some (.lui rd (w.extractLsb 31 12))
  else if opcode = 0b0011011#7 ∧ funct3 = 5#3 ∧ funct7 = 0#7 then  -- OP-IMM-32: SRLIW
    some (.srliw rd rs1 (w.extractLsb 24 20))
  else if opcode = 0b0111011#7 ∧ funct3 = 5#3 ∧ funct7 = 0#7 then  -- OP-32: SRLW
    some (.srlw rd rs1 rs2)
  else if opcode = 0b0000011#7 then     -- LOAD
    if funct3 = 0#3 then some (.lb rd rs1 immI)
    else if funct3 = 3#3 then some (.ld rd rs1 immI)
    else if funct3 = 4#3 then some (.lbu rd rs1 immI)
    else none
  else if opcode = 0b0100011#7 then     -- STORE
    if funct3 = 0#3 then some (.sb rs1 rs2 immS)
    else if funct3 = 3#3 then some (.sd rs1 rs2 immS)
    else none
  else none

/-- Machine state.  Memory is byte-addressed; `rdok`/`wrok` say which bytes the
    function may read/write.  Any access outside them faults, so proving that a
    run does not fault proves memory safety with respect to those regions. -/
structure State where
  regs  : Reg → BitVec 64
  pc    : BitVec 64
  fault : Bool := false
  mem   : BitVec 64 → BitVec 8 := fun _ => 0
  rdok  : BitVec 64 → Bool := fun _ => false
  wrok  : BitVec 64 → Bool := fun _ => false

/-- `x0` is hardwired to zero. -/
def State.rd (s : State) (r : Reg) : BitVec 64 := if r = 0 then 0 else s.regs r

def State.wr (s : State) (r : Reg) (v : BitVec 64) : State :=
  { s with regs := fun i => if i = r ∧ r ≠ 0 then v else s.regs i }

/-- Sail `jump_to` without the C extension: targets must be 4-byte aligned. -/
def State.jump (s : State) (target : BitVec 64) : State :=
  if target.extractLsb 1 1 = 0#1 then { s with pc := target } else { s with fault := true }

def State.next (s : State) : State := { s with pc := s.pc + 4 }

/-- Little-endian read of 8 bytes (byte `k` is bits `8k .. 8k+7`). -/
def State.read64 (s : State) (a : BitVec 64) : BitVec 64 :=
  (s.mem (a + 7)).setWidth 64 <<< 56 ||| (s.mem (a + 6)).setWidth 64 <<< 48 |||
  (s.mem (a + 5)).setWidth 64 <<< 40 ||| (s.mem (a + 4)).setWidth 64 <<< 32 |||
  (s.mem (a + 3)).setWidth 64 <<< 24 ||| (s.mem (a + 2)).setWidth 64 <<< 16 |||
  (s.mem (a + 1)).setWidth 64 <<< 8 ||| (s.mem a).setWidth 64

/-- All 8 bytes of a doubleword are readable / writable. -/
def State.canRead8 (s : State) (a : BitVec 64) : Bool :=
  s.rdok a && s.rdok (a + 1) && s.rdok (a + 2) && s.rdok (a + 3) &&
  s.rdok (a + 4) && s.rdok (a + 5) && s.rdok (a + 6) && s.rdok (a + 7)

def State.canWrite8 (s : State) (a : BitVec 64) : Bool :=
  s.wrok a && s.wrok (a + 1) && s.wrok (a + 2) && s.wrok (a + 3) &&
  s.wrok (a + 4) && s.wrok (a + 5) && s.wrok (a + 6) && s.wrok (a + 7)

/-- Byte store. -/
def State.store8 (s : State) (a : BitVec 64) (v : BitVec 8) : State :=
  { s with mem := fun x => if x = a then v else s.mem x }

/-- Little-endian 8-byte store. -/
def State.store64 (s : State) (a : BitVec 64) (v : BitVec 64) : State :=
  ((((((((s.store8 a (v.extractLsb 7 0)).store8 (a + 1) (v.extractLsb 15 8)).store8
    (a + 2) (v.extractLsb 23 16)).store8 (a + 3) (v.extractLsb 31 24)).store8
    (a + 4) (v.extractLsb 39 32)).store8 (a + 5) (v.extractLsb 47 40)).store8
    (a + 6) (v.extractLsb 55 48)).store8 (a + 7) (v.extractLsb 63 56))

def State.faulted (s : State) : State := { s with fault := true }

/-- 8-byte accesses must be naturally aligned (misaligned access is treated as
    a fault, which is the conservative choice among Sail's platform options). -/
def aligned8 (a : BitVec 64) : Bool := a.extractLsb 2 0 = 0#3

def exec (i : Instr) (s : State) : State :=
  match i with
  | .addi rd rs1 imm   => (s.wr rd (RV64.addi imm (s.rd rs1))).next
  | .xori rd rs1 imm   => (s.wr rd (RV64.xori imm (s.rd rs1))).next
  | .slli rd rs1 sh    => (s.wr rd (RV64.slli sh (s.rd rs1))).next
  | .srli rd rs1 sh    => (s.wr rd (RV64.srli sh (s.rd rs1))).next
  | .srai rd rs1 sh    => (s.wr rd (RV64.srai sh (s.rd rs1))).next
  | .sltiu rd rs1 imm  => (s.wr rd (RV64.sltiu imm (s.rd rs1))).next
  | .add rd rs1 rs2    => (s.wr rd (RV64.add (s.rd rs2) (s.rd rs1))).next
  | .sub rd rs1 rs2    => (s.wr rd (RV64.sub (s.rd rs2) (s.rd rs1))).next
  | .sll rd rs1 rs2    => (s.wr rd (RV64.sll (s.rd rs2) (s.rd rs1))).next
  | .sltu rd rs1 rs2   => (s.wr rd (RV64.sltu (s.rd rs2) (s.rd rs1))).next
  | .xor rd rs1 rs2    => (s.wr rd (RV64.xor (s.rd rs2) (s.rd rs1))).next
  | .or rd rs1 rs2     => (s.wr rd (RV64.or (s.rd rs2) (s.rd rs1))).next
  | .and rd rs1 rs2    => (s.wr rd (RV64.and (s.rd rs2) (s.rd rs1))).next
  | .andi rd rs1 imm   => (s.wr rd (RV64.andi imm (s.rd rs1))).next
  | .ori rd rs1 imm    => (s.wr rd (RV64.ori imm (s.rd rs1))).next
  | .lui rd imm        => (s.wr rd (RV64.lui imm)).next
  | .srliw rd rs1 sh   => (s.wr rd (RV64.srliw sh (s.rd rs1))).next
  | .srlw rd rs1 rs2   => (s.wr rd (RV64.srlw (s.rd rs2) (s.rd rs1))).next
  | .lb rd rs1 imm     =>
      let a := s.rd rs1 + imm.signExtend 64
      if s.rdok a then (s.wr rd ((s.mem a).signExtend 64)).next else s.faulted
  | .lbu rd rs1 imm    =>
      let a := s.rd rs1 + imm.signExtend 64
      if s.rdok a then (s.wr rd ((s.mem a).zeroExtend 64)).next else s.faulted
  | .ld rd rs1 imm     =>
      let a := s.rd rs1 + imm.signExtend 64
      if aligned8 a ∧ s.canRead8 a then (s.wr rd (s.read64 a)).next else s.faulted
  | .sb rs1 rs2 imm    =>
      let a := s.rd rs1 + imm.signExtend 64
      if s.wrok a then (s.store8 a ((s.rd rs2).extractLsb 7 0)).next else s.faulted
  | .sd rs1 rs2 imm    =>
      let a := s.rd rs1 + imm.signExtend 64
      if aligned8 a ∧ s.canWrite8 a then (s.store64 a (s.rd rs2)).next else s.faulted
  | .blt rs1 rs2 imm   =>
      if (s.rd rs1).slt (s.rd rs2) then s.jump (s.pc + imm.signExtend 64) else s.next
  | .jal rd imm        =>
      let s' := s.jump (s.pc + imm.signExtend 64)
      if s'.fault then s' else s'.wr rd (s.pc + 4)
  | .beq rs1 rs2 imm   =>
      if s.rd rs1 = s.rd rs2 then s.jump (s.pc + imm.signExtend 64) else s.next
  | .bne rs1 rs2 imm   =>
      if s.rd rs1 ≠ s.rd rs2 then s.jump (s.pc + imm.signExtend 64) else s.next
  | .bltu rs1 rs2 imm  =>
      if s.rd rs1 < s.rd rs2 then s.jump (s.pc + imm.signExtend 64) else s.next
  | .bgeu rs1 rs2 imm  =>
      if s.rd rs1 ≥ s.rd rs2 then s.jump (s.pc + imm.signExtend 64) else s.next
  | .jalr rd rs1 imm   =>
      -- Sail: link = next pc; target = rs1 + sext(imm) with bit 0 cleared;
      -- the target is computed from rs1 before rd is written.
      let target := (s.rd rs1 + imm.signExtend 64) &&& ~~~1#64
      let s' := s.jump target
      if s'.fault then s' else s'.wr rd (s.pc + 4)

/-- A program is a list of instruction words loaded at address `base`. -/
structure Program where
  base  : BitVec 64
  words : List (BitVec 32)

/-- Fetch and decode the word at `pc`; `none` outside the program. -/
def Program.fetch (p : Program) (pc : BitVec 64) : Option Instr :=
  let off := pc - p.base
  if off.extractLsb 1 0 = 0#2 ∧ off.toNat / 4 < p.words.length then
    (p.words[off.toNat / 4]?).bind decode
  else none

/-- One step. Leaving the program (e.g. returning to the caller) halts:
    the state is left unchanged. A fault or an undecodable word also halts. -/
def step (p : Program) (s : State) : State :=
  if s.fault then s else
  if s.pc - p.base < BitVec.ofNat 64 (4 * p.words.length) then
    match p.fetch s.pc with
    | some i => exec i s
    | none   => { s with fault := true }
  else s

def run (p : Program) : Nat → State → State
  | 0, s => s
  | n + 1, s => run p n (step p s)


/-! ## Symbolic-execution lemmas

`step_lit` unfolds a step only on a concrete (structure-literal) state, and
`step_ite` splits a step over a conditional state.  Together they keep
symbolic execution linear in the number of paths instead of duplicating the
state at every use of `s` inside `step`. -/

theorem step_lit (p : Program) (R : Reg → BitVec 64) (pc : BitVec 64)
    (m : BitVec 64 → BitVec 8) (r w : BitVec 64 → Bool) :
    step p { regs := R, pc := pc, fault := false, mem := m, rdok := r, wrok := w } =
      if pc - p.base < BitVec.ofNat 64 (4 * p.words.length) then
        match p.fetch pc with
        | some i => exec i { regs := R, pc := pc, fault := false, mem := m, rdok := r, wrok := w }
        | none   => { regs := R, pc := pc, fault := true, mem := m, rdok := r, wrok := w }
      else { regs := R, pc := pc, fault := false, mem := m, rdok := r, wrok := w } := by
  simp [step]

/-- A faulted state never changes again. -/
theorem step_fault (p : Program) (R : Reg → BitVec 64) (pc : BitVec 64)
    (m : BitVec 64 → BitVec 8) (r w : BitVec 64 → Bool) :
    step p { regs := R, pc := pc, fault := true, mem := m, rdok := r, wrok := w } =
      { regs := R, pc := pc, fault := true, mem := m, rdok := r, wrok := w } := by
  simp [step]

theorem step_ite (p : Program) (c : Prop) [Decidable c] (a b : State) :
    step p (if c then a else b) = if c then step p a else step p b := by
  split <;> rfl

theorem run_ite (p : Program) (n : Nat) (c : Prop) [Decidable c] (a b : State) :
    run p n (if c then a else b) = if c then run p n a else run p n b := by
  split <;> rfl

theorem ite_app {α β : Type} (c : Prop) [Decidable c] (f g : α → β) (x : α) :
    (if c then f else g) x = if c then f x else g x := by
  split <;> rfl

end NgtcpRV
