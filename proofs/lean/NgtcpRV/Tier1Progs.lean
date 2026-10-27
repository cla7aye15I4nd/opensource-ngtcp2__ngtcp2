import NgtcpRV.Machine
import NgtcpRV.BitLemmas

/-!
# QUIC variable-length integers and `ngtcp2_range`: programs

Sources: `lib/ngtcp2_conv.c` and `lib/ngtcp2_range.c`, extracted verbatim by
`rv/extract.py` (with `rv/prelude.h`: byte-swaps as compiler builtins and a
debug-build `assert` that traps), compiled with
`clang --target=riscv64-unknown-elf -march=rv64im -mabi=lp64 -O2`.
-/

namespace NgtcpRV

/-! ### `ngtcp2_put_uvarintlen`: 17 instructions at .text+0x0 (relocated to 0) -/

def putUvarintlen_words : List (BitVec 32) :=
  [0x04000593#32,
   0x00b57663#32,
   0x00100513#32,
   0x00008067#32,
   0x00e55593#32,
   0x00059663#32,
   0x00200513#32,
   0x00008067#32,
   0x01e55593#32,
   0x00059663#32,
   0x00400513#32,
   0x00008067#32,
   0x03e55513#32,
   0x00051663#32,
   0x00800513#32,
   0x00008067#32,
   0xc0001073#32]

/-- `ngtcp2_put_uvarintlen` as decoded by llvm-objdump (`none` = `unimp`). -/
def putUvarintlen_llvm : List (Option Instr) :=
  [some (.addi 11 0 64#12),
   some (.bgeu 10 11 12#13),
   some (.addi 10 0 1#12),
   some (.jalr 0 1 0#12),
   some (.srli 11 10 14#6),
   some (.bne 11 0 12#13),
   some (.addi 10 0 2#12),
   some (.jalr 0 1 0#12),
   some (.srli 11 10 30#6),
   some (.bne 11 0 12#13),
   some (.addi 10 0 4#12),
   some (.jalr 0 1 0#12),
   some (.srli 10 10 62#6),
   some (.bne 10 0 12#13),
   some (.addi 10 0 8#12),
   some (.jalr 0 1 0#12),
   none]

def putUvarintlen : Program := ⟨0, putUvarintlen_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem putUvarintlen_decode : putUvarintlen_words.map decode = putUvarintlen_llvm := by decide

@[simp] theorem putUvarintlen_base : putUvarintlen.base = 0#64 := rfl
@[simp] theorem putUvarintlen_len : putUvarintlen.words.length = 17 := rfl

@[simp] theorem putUvarintlen_fetch_0 : putUvarintlen.fetch 0#64 = some (.addi 11 0 64#12) := by decide
@[simp] theorem putUvarintlen_fetch_1 : putUvarintlen.fetch 4#64 = some (.bgeu 10 11 12#13) := by decide
@[simp] theorem putUvarintlen_fetch_2 : putUvarintlen.fetch 8#64 = some (.addi 10 0 1#12) := by decide
@[simp] theorem putUvarintlen_fetch_3 : putUvarintlen.fetch 12#64 = some (.jalr 0 1 0#12) := by decide
@[simp] theorem putUvarintlen_fetch_4 : putUvarintlen.fetch 16#64 = some (.srli 11 10 14#6) := by decide
@[simp] theorem putUvarintlen_fetch_5 : putUvarintlen.fetch 20#64 = some (.bne 11 0 12#13) := by decide
@[simp] theorem putUvarintlen_fetch_6 : putUvarintlen.fetch 24#64 = some (.addi 10 0 2#12) := by decide
@[simp] theorem putUvarintlen_fetch_7 : putUvarintlen.fetch 28#64 = some (.jalr 0 1 0#12) := by decide
@[simp] theorem putUvarintlen_fetch_8 : putUvarintlen.fetch 32#64 = some (.srli 11 10 30#6) := by decide
@[simp] theorem putUvarintlen_fetch_9 : putUvarintlen.fetch 36#64 = some (.bne 11 0 12#13) := by decide
@[simp] theorem putUvarintlen_fetch_10 : putUvarintlen.fetch 40#64 = some (.addi 10 0 4#12) := by decide
@[simp] theorem putUvarintlen_fetch_11 : putUvarintlen.fetch 44#64 = some (.jalr 0 1 0#12) := by decide
@[simp] theorem putUvarintlen_fetch_12 : putUvarintlen.fetch 48#64 = some (.srli 10 10 62#6) := by decide
@[simp] theorem putUvarintlen_fetch_13 : putUvarintlen.fetch 52#64 = some (.bne 10 0 12#13) := by decide
@[simp] theorem putUvarintlen_fetch_14 : putUvarintlen.fetch 56#64 = some (.addi 10 0 8#12) := by decide
@[simp] theorem putUvarintlen_fetch_15 : putUvarintlen.fetch 60#64 = some (.jalr 0 1 0#12) := by decide
@[simp] theorem putUvarintlen_fetch_16 : putUvarintlen.fetch 64#64 = none := by decide

/-! ### `ngtcp2_get_uvarintlen`: 5 instructions at .text+0x44 (relocated to 0) -/

def getUvarintlen_words : List (BitVec 32) :=
  [0x00054503#32,
   0x00655513#32,
   0x00100593#32,
   0x00a59533#32,
   0x00008067#32]

/-- `ngtcp2_get_uvarintlen` as decoded by llvm-objdump (`none` = `unimp`). -/
def getUvarintlen_llvm : List (Option Instr) :=
  [some (.lbu 10 10 0#12),
   some (.srli 10 10 6#6),
   some (.addi 11 0 1#12),
   some (.sll 10 11 10),
   some (.jalr 0 1 0#12)]

def getUvarintlen : Program := ⟨0, getUvarintlen_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem getUvarintlen_decode : getUvarintlen_words.map decode = getUvarintlen_llvm := by decide

@[simp] theorem getUvarintlen_base : getUvarintlen.base = 0#64 := rfl
@[simp] theorem getUvarintlen_len : getUvarintlen.words.length = 5 := rfl

@[simp] theorem getUvarintlen_fetch_0 : getUvarintlen.fetch 0#64 = some (.lbu 10 10 0#12) := by decide
@[simp] theorem getUvarintlen_fetch_1 : getUvarintlen.fetch 4#64 = some (.srli 10 10 6#6) := by decide
@[simp] theorem getUvarintlen_fetch_2 : getUvarintlen.fetch 8#64 = some (.addi 11 0 1#12) := by decide
@[simp] theorem getUvarintlen_fetch_3 : getUvarintlen.fetch 12#64 = some (.sll 10 11 10) := by decide
@[simp] theorem getUvarintlen_fetch_4 : getUvarintlen.fetch 16#64 = some (.jalr 0 1 0#12) := by decide

/-! ### `ngtcp2_get_uvarint`: 86 instructions at .text+0x58 (relocated to 0) -/

def getUvarint_words : List (BitVec 32) :=
  [0x0005c603#32,
   0x00665693#32,
   0x00100713#32,
   0x00d74c63#32,
   0x04069c63#32,
   0x00158593#32,
   0x00c53023#32,
   0x00058513#32,
   0x00008067#32,
   0x00200613#32,
   0x06c69263#32,
   0x00358603#32,
   0x0025c683#32,
   0x0015c703#32,
   0x0005c783#32,
   0x0ff67613#32,
   0x00869693#32,
   0x01071713#32,
   0x03a79793#32,
   0x00c6e633#32,
   0x0227d793#32,
   0x00e7e733#32,
   0x00c76633#32,
   0x00c53023#32,
   0x00458513#32,
   0x00008067#32,
   0x0005c603#32,
   0x0015c683#32,
   0x00861613#32,
   0x00d66633#32,
   0x03261613#32,
   0x03265613#32,
   0x00c53023#32,
   0x00258513#32,
   0x00008067#32,
   0x0005c603#32,
   0x0015c683#32,
   0x0025c703#32,
   0x0035c783#32,
   0x0045c803#32,
   0x0055c883#32,
   0x0065c283#32,
   0x0075c303#32,
   0x00ff03b7#32,
   0x01071713#32,
   0x01879793#32,
   0x00e7e733#32,
   0x0ff00793#32,
   0x00889893#32,
   0x0108e833#32,
   0x01029893#32,
   0x01831313#32,
   0x011368b3#32,
   0x00010337#32,
   0x01879793#32,
   0xf0030313#32,
   0x00869693#32,
   0x00c6e6b3#32,
   0x03f67613#32,
   0x00829293#32,
   0x03861613#32,
   0x00d766b3#32,
   0x0108e733#32,
   0x02071813#32,
   0x0187571b#32,
   0x0066f8b3#32,
   0x00d866b3#32,
   0x00e2e733#32,
   0x02889893#32,
   0x0186d813#32,
   0x0086d293#32,
   0x0186d31b#32,
   0x0076f6b3#32,
   0x01166633#32,
   0x00787833#32,
   0x00f2f7b3#32,
   0x02031313#32,
   0x01869693#32,
   0x0107e7b3#32,
   0x0066e6b3#32,
   0x00e7e733#32,
   0x00d66633#32,
   0x00e66633#32,
   0x00c53023#32,
   0x00858513#32,
   0x00008067#32]

/-- `ngtcp2_get_uvarint` as decoded by llvm-objdump (`none` = `unimp`). -/
def getUvarint_llvm : List (Option Instr) :=
  [some (.lbu 12 11 0#12),
   some (.srli 13 12 6#6),
   some (.addi 14 0 1#12),
   some (.blt 14 13 24#13),
   some (.bne 13 0 88#13),
   some (.addi 11 11 1#12),
   some (.sd 10 12 0#12),
   some (.addi 10 11 0#12),
   some (.jalr 0 1 0#12),
   some (.addi 12 0 2#12),
   some (.bne 13 12 100#13),
   some (.lb 12 11 3#12),
   some (.lbu 13 11 2#12),
   some (.lbu 14 11 1#12),
   some (.lbu 15 11 0#12),
   some (.andi 12 12 255#12),
   some (.slli 13 13 8#6),
   some (.slli 14 14 16#6),
   some (.slli 15 15 58#6),
   some (.or 12 13 12),
   some (.srli 15 15 34#6),
   some (.or 14 15 14),
   some (.or 12 14 12),
   some (.sd 10 12 0#12),
   some (.addi 10 11 4#12),
   some (.jalr 0 1 0#12),
   some (.lbu 12 11 0#12),
   some (.lbu 13 11 1#12),
   some (.slli 12 12 8#6),
   some (.or 12 12 13),
   some (.slli 12 12 50#6),
   some (.srli 12 12 50#6),
   some (.sd 10 12 0#12),
   some (.addi 10 11 2#12),
   some (.jalr 0 1 0#12),
   some (.lbu 12 11 0#12),
   some (.lbu 13 11 1#12),
   some (.lbu 14 11 2#12),
   some (.lbu 15 11 3#12),
   some (.lbu 16 11 4#12),
   some (.lbu 17 11 5#12),
   some (.lbu 5 11 6#12),
   some (.lbu 6 11 7#12),
   some (.lui 7 4080#20),
   some (.slli 14 14 16#6),
   some (.slli 15 15 24#6),
   some (.or 14 15 14),
   some (.addi 15 0 255#12),
   some (.slli 17 17 8#6),
   some (.or 16 17 16),
   some (.slli 17 5 16#6),
   some (.slli 6 6 24#6),
   some (.or 17 6 17),
   some (.lui 6 16#20),
   some (.slli 15 15 24#6),
   some (.addi 6 6 3840#12),
   some (.slli 13 13 8#6),
   some (.or 13 13 12),
   some (.andi 12 12 63#12),
   some (.slli 5 5 8#6),
   some (.slli 12 12 56#6),
   some (.or 13 14 13),
   some (.or 14 17 16),
   some (.slli 16 14 32#6),
   some (.srliw 14 14 24#5),
   some (.and 17 13 6),
   some (.or 13 16 13),
   some (.or 14 5 14),
   some (.slli 17 17 40#6),
   some (.srli 16 13 24#6),
   some (.srli 5 13 8#6),
   some (.srliw 6 13 24#5),
   some (.and 13 13 7),
   some (.or 12 12 17),
   some (.and 16 16 7),
   some (.and 15 5 15),
   some (.slli 6 6 32#6),
   some (.slli 13 13 24#6),
   some (.or 15 15 16),
   some (.or 13 13 6),
   some (.or 14 15 14),
   some (.or 12 12 13),
   some (.or 12 12 14),
   some (.sd 10 12 0#12),
   some (.addi 10 11 8#12),
   some (.jalr 0 1 0#12)]

def getUvarint : Program := ⟨0, getUvarint_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem getUvarint_decode : getUvarint_words.map decode = getUvarint_llvm := by decide

@[simp] theorem getUvarint_base : getUvarint.base = 0#64 := rfl
@[simp] theorem getUvarint_len : getUvarint.words.length = 86 := rfl

@[simp] theorem getUvarint_fetch_0 : getUvarint.fetch 0#64 = some (.lbu 12 11 0#12) := by decide
@[simp] theorem getUvarint_fetch_1 : getUvarint.fetch 4#64 = some (.srli 13 12 6#6) := by decide
@[simp] theorem getUvarint_fetch_2 : getUvarint.fetch 8#64 = some (.addi 14 0 1#12) := by decide
@[simp] theorem getUvarint_fetch_3 : getUvarint.fetch 12#64 = some (.blt 14 13 24#13) := by decide
@[simp] theorem getUvarint_fetch_4 : getUvarint.fetch 16#64 = some (.bne 13 0 88#13) := by decide
@[simp] theorem getUvarint_fetch_5 : getUvarint.fetch 20#64 = some (.addi 11 11 1#12) := by decide
@[simp] theorem getUvarint_fetch_6 : getUvarint.fetch 24#64 = some (.sd 10 12 0#12) := by decide
@[simp] theorem getUvarint_fetch_7 : getUvarint.fetch 28#64 = some (.addi 10 11 0#12) := by decide
@[simp] theorem getUvarint_fetch_8 : getUvarint.fetch 32#64 = some (.jalr 0 1 0#12) := by decide
@[simp] theorem getUvarint_fetch_9 : getUvarint.fetch 36#64 = some (.addi 12 0 2#12) := by decide
@[simp] theorem getUvarint_fetch_10 : getUvarint.fetch 40#64 = some (.bne 13 12 100#13) := by decide
@[simp] theorem getUvarint_fetch_11 : getUvarint.fetch 44#64 = some (.lb 12 11 3#12) := by decide
@[simp] theorem getUvarint_fetch_12 : getUvarint.fetch 48#64 = some (.lbu 13 11 2#12) := by decide
@[simp] theorem getUvarint_fetch_13 : getUvarint.fetch 52#64 = some (.lbu 14 11 1#12) := by decide
@[simp] theorem getUvarint_fetch_14 : getUvarint.fetch 56#64 = some (.lbu 15 11 0#12) := by decide
@[simp] theorem getUvarint_fetch_15 : getUvarint.fetch 60#64 = some (.andi 12 12 255#12) := by decide
@[simp] theorem getUvarint_fetch_16 : getUvarint.fetch 64#64 = some (.slli 13 13 8#6) := by decide
@[simp] theorem getUvarint_fetch_17 : getUvarint.fetch 68#64 = some (.slli 14 14 16#6) := by decide
@[simp] theorem getUvarint_fetch_18 : getUvarint.fetch 72#64 = some (.slli 15 15 58#6) := by decide
@[simp] theorem getUvarint_fetch_19 : getUvarint.fetch 76#64 = some (.or 12 13 12) := by decide
@[simp] theorem getUvarint_fetch_20 : getUvarint.fetch 80#64 = some (.srli 15 15 34#6) := by decide
@[simp] theorem getUvarint_fetch_21 : getUvarint.fetch 84#64 = some (.or 14 15 14) := by decide
@[simp] theorem getUvarint_fetch_22 : getUvarint.fetch 88#64 = some (.or 12 14 12) := by decide
@[simp] theorem getUvarint_fetch_23 : getUvarint.fetch 92#64 = some (.sd 10 12 0#12) := by decide
@[simp] theorem getUvarint_fetch_24 : getUvarint.fetch 96#64 = some (.addi 10 11 4#12) := by decide
@[simp] theorem getUvarint_fetch_25 : getUvarint.fetch 100#64 = some (.jalr 0 1 0#12) := by decide
@[simp] theorem getUvarint_fetch_26 : getUvarint.fetch 104#64 = some (.lbu 12 11 0#12) := by decide
@[simp] theorem getUvarint_fetch_27 : getUvarint.fetch 108#64 = some (.lbu 13 11 1#12) := by decide
@[simp] theorem getUvarint_fetch_28 : getUvarint.fetch 112#64 = some (.slli 12 12 8#6) := by decide
@[simp] theorem getUvarint_fetch_29 : getUvarint.fetch 116#64 = some (.or 12 12 13) := by decide
@[simp] theorem getUvarint_fetch_30 : getUvarint.fetch 120#64 = some (.slli 12 12 50#6) := by decide
@[simp] theorem getUvarint_fetch_31 : getUvarint.fetch 124#64 = some (.srli 12 12 50#6) := by decide
@[simp] theorem getUvarint_fetch_32 : getUvarint.fetch 128#64 = some (.sd 10 12 0#12) := by decide
@[simp] theorem getUvarint_fetch_33 : getUvarint.fetch 132#64 = some (.addi 10 11 2#12) := by decide
@[simp] theorem getUvarint_fetch_34 : getUvarint.fetch 136#64 = some (.jalr 0 1 0#12) := by decide
@[simp] theorem getUvarint_fetch_35 : getUvarint.fetch 140#64 = some (.lbu 12 11 0#12) := by decide
@[simp] theorem getUvarint_fetch_36 : getUvarint.fetch 144#64 = some (.lbu 13 11 1#12) := by decide
@[simp] theorem getUvarint_fetch_37 : getUvarint.fetch 148#64 = some (.lbu 14 11 2#12) := by decide
@[simp] theorem getUvarint_fetch_38 : getUvarint.fetch 152#64 = some (.lbu 15 11 3#12) := by decide
@[simp] theorem getUvarint_fetch_39 : getUvarint.fetch 156#64 = some (.lbu 16 11 4#12) := by decide
@[simp] theorem getUvarint_fetch_40 : getUvarint.fetch 160#64 = some (.lbu 17 11 5#12) := by decide
@[simp] theorem getUvarint_fetch_41 : getUvarint.fetch 164#64 = some (.lbu 5 11 6#12) := by decide
@[simp] theorem getUvarint_fetch_42 : getUvarint.fetch 168#64 = some (.lbu 6 11 7#12) := by decide
@[simp] theorem getUvarint_fetch_43 : getUvarint.fetch 172#64 = some (.lui 7 4080#20) := by decide
@[simp] theorem getUvarint_fetch_44 : getUvarint.fetch 176#64 = some (.slli 14 14 16#6) := by decide
@[simp] theorem getUvarint_fetch_45 : getUvarint.fetch 180#64 = some (.slli 15 15 24#6) := by decide
@[simp] theorem getUvarint_fetch_46 : getUvarint.fetch 184#64 = some (.or 14 15 14) := by decide
@[simp] theorem getUvarint_fetch_47 : getUvarint.fetch 188#64 = some (.addi 15 0 255#12) := by decide
@[simp] theorem getUvarint_fetch_48 : getUvarint.fetch 192#64 = some (.slli 17 17 8#6) := by decide
@[simp] theorem getUvarint_fetch_49 : getUvarint.fetch 196#64 = some (.or 16 17 16) := by decide
@[simp] theorem getUvarint_fetch_50 : getUvarint.fetch 200#64 = some (.slli 17 5 16#6) := by decide
@[simp] theorem getUvarint_fetch_51 : getUvarint.fetch 204#64 = some (.slli 6 6 24#6) := by decide
@[simp] theorem getUvarint_fetch_52 : getUvarint.fetch 208#64 = some (.or 17 6 17) := by decide
@[simp] theorem getUvarint_fetch_53 : getUvarint.fetch 212#64 = some (.lui 6 16#20) := by decide
@[simp] theorem getUvarint_fetch_54 : getUvarint.fetch 216#64 = some (.slli 15 15 24#6) := by decide
@[simp] theorem getUvarint_fetch_55 : getUvarint.fetch 220#64 = some (.addi 6 6 3840#12) := by decide
@[simp] theorem getUvarint_fetch_56 : getUvarint.fetch 224#64 = some (.slli 13 13 8#6) := by decide
@[simp] theorem getUvarint_fetch_57 : getUvarint.fetch 228#64 = some (.or 13 13 12) := by decide
@[simp] theorem getUvarint_fetch_58 : getUvarint.fetch 232#64 = some (.andi 12 12 63#12) := by decide
@[simp] theorem getUvarint_fetch_59 : getUvarint.fetch 236#64 = some (.slli 5 5 8#6) := by decide
@[simp] theorem getUvarint_fetch_60 : getUvarint.fetch 240#64 = some (.slli 12 12 56#6) := by decide
@[simp] theorem getUvarint_fetch_61 : getUvarint.fetch 244#64 = some (.or 13 14 13) := by decide
@[simp] theorem getUvarint_fetch_62 : getUvarint.fetch 248#64 = some (.or 14 17 16) := by decide
@[simp] theorem getUvarint_fetch_63 : getUvarint.fetch 252#64 = some (.slli 16 14 32#6) := by decide
@[simp] theorem getUvarint_fetch_64 : getUvarint.fetch 256#64 = some (.srliw 14 14 24#5) := by decide
@[simp] theorem getUvarint_fetch_65 : getUvarint.fetch 260#64 = some (.and 17 13 6) := by decide
@[simp] theorem getUvarint_fetch_66 : getUvarint.fetch 264#64 = some (.or 13 16 13) := by decide
@[simp] theorem getUvarint_fetch_67 : getUvarint.fetch 268#64 = some (.or 14 5 14) := by decide
@[simp] theorem getUvarint_fetch_68 : getUvarint.fetch 272#64 = some (.slli 17 17 40#6) := by decide
@[simp] theorem getUvarint_fetch_69 : getUvarint.fetch 276#64 = some (.srli 16 13 24#6) := by decide
@[simp] theorem getUvarint_fetch_70 : getUvarint.fetch 280#64 = some (.srli 5 13 8#6) := by decide
@[simp] theorem getUvarint_fetch_71 : getUvarint.fetch 284#64 = some (.srliw 6 13 24#5) := by decide
@[simp] theorem getUvarint_fetch_72 : getUvarint.fetch 288#64 = some (.and 13 13 7) := by decide
@[simp] theorem getUvarint_fetch_73 : getUvarint.fetch 292#64 = some (.or 12 12 17) := by decide
@[simp] theorem getUvarint_fetch_74 : getUvarint.fetch 296#64 = some (.and 16 16 7) := by decide
@[simp] theorem getUvarint_fetch_75 : getUvarint.fetch 300#64 = some (.and 15 5 15) := by decide
@[simp] theorem getUvarint_fetch_76 : getUvarint.fetch 304#64 = some (.slli 6 6 32#6) := by decide
@[simp] theorem getUvarint_fetch_77 : getUvarint.fetch 308#64 = some (.slli 13 13 24#6) := by decide
@[simp] theorem getUvarint_fetch_78 : getUvarint.fetch 312#64 = some (.or 15 15 16) := by decide
@[simp] theorem getUvarint_fetch_79 : getUvarint.fetch 316#64 = some (.or 13 13 6) := by decide
@[simp] theorem getUvarint_fetch_80 : getUvarint.fetch 320#64 = some (.or 14 15 14) := by decide
@[simp] theorem getUvarint_fetch_81 : getUvarint.fetch 324#64 = some (.or 12 12 13) := by decide
@[simp] theorem getUvarint_fetch_82 : getUvarint.fetch 328#64 = some (.or 12 12 14) := by decide
@[simp] theorem getUvarint_fetch_83 : getUvarint.fetch 332#64 = some (.sd 10 12 0#12) := by decide
@[simp] theorem getUvarint_fetch_84 : getUvarint.fetch 336#64 = some (.addi 10 11 8#12) := by decide
@[simp] theorem getUvarint_fetch_85 : getUvarint.fetch 340#64 = some (.jalr 0 1 0#12) := by decide

/-! ### `ngtcp2_put_uvarint`: 51 instructions at .text+0x1b0 (relocated to 0) -/

def putUvarint_words : List (BitVec 32) :=
  [0x03f00613#32,
   0x00b66663#32,
   0x00150613#32,
   0x0b00006f#32,
   0x00e5d613#32,
   0x02061463#32,
   0x00859613#32,
   0x0085d693#32,
   0x0ff6f713#32,
   0x00d50023#32,
   0x00b500a3#32,
   0x00e66733#32,
   0x00250613#32,
   0x04076593#32,
   0x0840006f#32,
   0x01e5d613#32,
   0x02061863#32,
   0x0185d69b#32,
   0x0185d713#32,
   0x0085d793#32,
   0x0105d813#32,
   0x00450613#32,
   0x00e50023#32,
   0x010500a3#32,
   0x00f50123#32,
   0x00b501a3#32,
   0xf806e593#32,
   0x0500006f#32,
   0x03e5d613#32,
   0x04061a63#32,
   0x0385d693#32,
   0x0285d713#32,
   0x0185d613#32,
   0x0085d793#32,
   0x0105d813#32,
   0x0205d893#32,
   0x0305d293#32,
   0x00c50223#32,
   0x010502a3#32,
   0x00f50323#32,
   0x00b503a3#32,
   0x00850613#32,
   0x00d50023#32,
   0x005500a3#32,
   0x00e50123#32,
   0x011501a3#32,
   0xfc06e593#32,
   0x00b50023#32,
   0x00060513#32,
   0x00008067#32,
   0xc0001073#32]

/-- `ngtcp2_put_uvarint` as decoded by llvm-objdump (`none` = `unimp`). -/
def putUvarint_llvm : List (Option Instr) :=
  [some (.addi 12 0 63#12),
   some (.bltu 12 11 12#13),
   some (.addi 12 10 1#12),
   some (.jal 0 176#21),
   some (.srli 12 11 14#6),
   some (.bne 12 0 40#13),
   some (.slli 12 11 8#6),
   some (.srli 13 11 8#6),
   some (.andi 14 13 255#12),
   some (.sb 10 13 0#12),
   some (.sb 10 11 1#12),
   some (.or 14 12 14),
   some (.addi 12 10 2#12),
   some (.ori 11 14 64#12),
   some (.jal 0 132#21),
   some (.srli 12 11 30#6),
   some (.bne 12 0 48#13),
   some (.srliw 13 11 24#5),
   some (.srli 14 11 24#6),
   some (.srli 15 11 8#6),
   some (.srli 16 11 16#6),
   some (.addi 12 10 4#12),
   some (.sb 10 14 0#12),
   some (.sb 10 16 1#12),
   some (.sb 10 15 2#12),
   some (.sb 10 11 3#12),
   some (.ori 11 13 3968#12),
   some (.jal 0 80#21),
   some (.srli 12 11 62#6),
   some (.bne 12 0 84#13),
   some (.srli 13 11 56#6),
   some (.srli 14 11 40#6),
   some (.srli 12 11 24#6),
   some (.srli 15 11 8#6),
   some (.srli 16 11 16#6),
   some (.srli 17 11 32#6),
   some (.srli 5 11 48#6),
   some (.sb 10 12 4#12),
   some (.sb 10 16 5#12),
   some (.sb 10 15 6#12),
   some (.sb 10 11 7#12),
   some (.addi 12 10 8#12),
   some (.sb 10 13 0#12),
   some (.sb 10 5 1#12),
   some (.sb 10 14 2#12),
   some (.sb 10 17 3#12),
   some (.ori 11 13 4032#12),
   some (.sb 10 11 0#12),
   some (.addi 10 12 0#12),
   some (.jalr 0 1 0#12),
   none]

def putUvarint : Program := ⟨0, putUvarint_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem putUvarint_decode : putUvarint_words.map decode = putUvarint_llvm := by decide

@[simp] theorem putUvarint_base : putUvarint.base = 0#64 := rfl
@[simp] theorem putUvarint_len : putUvarint.words.length = 51 := rfl

@[simp] theorem putUvarint_fetch_0 : putUvarint.fetch 0#64 = some (.addi 12 0 63#12) := by decide
@[simp] theorem putUvarint_fetch_1 : putUvarint.fetch 4#64 = some (.bltu 12 11 12#13) := by decide
@[simp] theorem putUvarint_fetch_2 : putUvarint.fetch 8#64 = some (.addi 12 10 1#12) := by decide
@[simp] theorem putUvarint_fetch_3 : putUvarint.fetch 12#64 = some (.jal 0 176#21) := by decide
@[simp] theorem putUvarint_fetch_4 : putUvarint.fetch 16#64 = some (.srli 12 11 14#6) := by decide
@[simp] theorem putUvarint_fetch_5 : putUvarint.fetch 20#64 = some (.bne 12 0 40#13) := by decide
@[simp] theorem putUvarint_fetch_6 : putUvarint.fetch 24#64 = some (.slli 12 11 8#6) := by decide
@[simp] theorem putUvarint_fetch_7 : putUvarint.fetch 28#64 = some (.srli 13 11 8#6) := by decide
@[simp] theorem putUvarint_fetch_8 : putUvarint.fetch 32#64 = some (.andi 14 13 255#12) := by decide
@[simp] theorem putUvarint_fetch_9 : putUvarint.fetch 36#64 = some (.sb 10 13 0#12) := by decide
@[simp] theorem putUvarint_fetch_10 : putUvarint.fetch 40#64 = some (.sb 10 11 1#12) := by decide
@[simp] theorem putUvarint_fetch_11 : putUvarint.fetch 44#64 = some (.or 14 12 14) := by decide
@[simp] theorem putUvarint_fetch_12 : putUvarint.fetch 48#64 = some (.addi 12 10 2#12) := by decide
@[simp] theorem putUvarint_fetch_13 : putUvarint.fetch 52#64 = some (.ori 11 14 64#12) := by decide
@[simp] theorem putUvarint_fetch_14 : putUvarint.fetch 56#64 = some (.jal 0 132#21) := by decide
@[simp] theorem putUvarint_fetch_15 : putUvarint.fetch 60#64 = some (.srli 12 11 30#6) := by decide
@[simp] theorem putUvarint_fetch_16 : putUvarint.fetch 64#64 = some (.bne 12 0 48#13) := by decide
@[simp] theorem putUvarint_fetch_17 : putUvarint.fetch 68#64 = some (.srliw 13 11 24#5) := by decide
@[simp] theorem putUvarint_fetch_18 : putUvarint.fetch 72#64 = some (.srli 14 11 24#6) := by decide
@[simp] theorem putUvarint_fetch_19 : putUvarint.fetch 76#64 = some (.srli 15 11 8#6) := by decide
@[simp] theorem putUvarint_fetch_20 : putUvarint.fetch 80#64 = some (.srli 16 11 16#6) := by decide
@[simp] theorem putUvarint_fetch_21 : putUvarint.fetch 84#64 = some (.addi 12 10 4#12) := by decide
@[simp] theorem putUvarint_fetch_22 : putUvarint.fetch 88#64 = some (.sb 10 14 0#12) := by decide
@[simp] theorem putUvarint_fetch_23 : putUvarint.fetch 92#64 = some (.sb 10 16 1#12) := by decide
@[simp] theorem putUvarint_fetch_24 : putUvarint.fetch 96#64 = some (.sb 10 15 2#12) := by decide
@[simp] theorem putUvarint_fetch_25 : putUvarint.fetch 100#64 = some (.sb 10 11 3#12) := by decide
@[simp] theorem putUvarint_fetch_26 : putUvarint.fetch 104#64 = some (.ori 11 13 3968#12) := by decide
@[simp] theorem putUvarint_fetch_27 : putUvarint.fetch 108#64 = some (.jal 0 80#21) := by decide
@[simp] theorem putUvarint_fetch_28 : putUvarint.fetch 112#64 = some (.srli 12 11 62#6) := by decide
@[simp] theorem putUvarint_fetch_29 : putUvarint.fetch 116#64 = some (.bne 12 0 84#13) := by decide
@[simp] theorem putUvarint_fetch_30 : putUvarint.fetch 120#64 = some (.srli 13 11 56#6) := by decide
@[simp] theorem putUvarint_fetch_31 : putUvarint.fetch 124#64 = some (.srli 14 11 40#6) := by decide
@[simp] theorem putUvarint_fetch_32 : putUvarint.fetch 128#64 = some (.srli 12 11 24#6) := by decide
@[simp] theorem putUvarint_fetch_33 : putUvarint.fetch 132#64 = some (.srli 15 11 8#6) := by decide
@[simp] theorem putUvarint_fetch_34 : putUvarint.fetch 136#64 = some (.srli 16 11 16#6) := by decide
@[simp] theorem putUvarint_fetch_35 : putUvarint.fetch 140#64 = some (.srli 17 11 32#6) := by decide
@[simp] theorem putUvarint_fetch_36 : putUvarint.fetch 144#64 = some (.srli 5 11 48#6) := by decide
@[simp] theorem putUvarint_fetch_37 : putUvarint.fetch 148#64 = some (.sb 10 12 4#12) := by decide
@[simp] theorem putUvarint_fetch_38 : putUvarint.fetch 152#64 = some (.sb 10 16 5#12) := by decide
@[simp] theorem putUvarint_fetch_39 : putUvarint.fetch 156#64 = some (.sb 10 15 6#12) := by decide
@[simp] theorem putUvarint_fetch_40 : putUvarint.fetch 160#64 = some (.sb 10 11 7#12) := by decide
@[simp] theorem putUvarint_fetch_41 : putUvarint.fetch 164#64 = some (.addi 12 10 8#12) := by decide
@[simp] theorem putUvarint_fetch_42 : putUvarint.fetch 168#64 = some (.sb 10 13 0#12) := by decide
@[simp] theorem putUvarint_fetch_43 : putUvarint.fetch 172#64 = some (.sb 10 5 1#12) := by decide
@[simp] theorem putUvarint_fetch_44 : putUvarint.fetch 176#64 = some (.sb 10 14 2#12) := by decide
@[simp] theorem putUvarint_fetch_45 : putUvarint.fetch 180#64 = some (.sb 10 17 3#12) := by decide
@[simp] theorem putUvarint_fetch_46 : putUvarint.fetch 184#64 = some (.ori 11 13 4032#12) := by decide
@[simp] theorem putUvarint_fetch_47 : putUvarint.fetch 188#64 = some (.sb 10 11 0#12) := by decide
@[simp] theorem putUvarint_fetch_48 : putUvarint.fetch 192#64 = some (.addi 10 12 0#12) := by decide
@[simp] theorem putUvarint_fetch_49 : putUvarint.fetch 196#64 = some (.jalr 0 1 0#12) := by decide
@[simp] theorem putUvarint_fetch_50 : putUvarint.fetch 200#64 = none := by decide

/-! ### `ngtcp2_range_intersect`: 13 instructions at .text+0x288 (relocated to 0) -/

def rangeIntersect_words : List (BitVec 32) :=
  [0x00053603#32,
   0x0005b683#32,
   0x00c6e463#32,
   0x00068613#32,
   0x00853503#32,
   0x0085b583#32,
   0x00b56463#32,
   0x00058513#32,
   0x00a635b3#32,
   0x40b006b3#32,
   0x00a6f5b3#32,
   0x00c6f533#32,
   0x00008067#32]

/-- `ngtcp2_range_intersect` as decoded by llvm-objdump (`none` = `unimp`). -/
def rangeIntersect_llvm : List (Option Instr) :=
  [some (.ld 12 10 0#12),
   some (.ld 13 11 0#12),
   some (.bltu 13 12 8#13),
   some (.addi 12 13 0#12),
   some (.ld 10 10 8#12),
   some (.ld 11 11 8#12),
   some (.bltu 10 11 8#13),
   some (.addi 10 11 0#12),
   some (.sltu 11 12 10),
   some (.sub 13 0 11),
   some (.and 11 13 10),
   some (.and 10 13 12),
   some (.jalr 0 1 0#12)]

def rangeIntersect : Program := ⟨0, rangeIntersect_words⟩

/-- Our decoder agrees with LLVM's on every word (kernel-checked). -/
theorem rangeIntersect_decode : rangeIntersect_words.map decode = rangeIntersect_llvm := by decide

@[simp] theorem rangeIntersect_base : rangeIntersect.base = 0#64 := rfl
@[simp] theorem rangeIntersect_len : rangeIntersect.words.length = 13 := rfl

@[simp] theorem rangeIntersect_fetch_0 : rangeIntersect.fetch 0#64 = some (.ld 12 10 0#12) := by decide
@[simp] theorem rangeIntersect_fetch_1 : rangeIntersect.fetch 4#64 = some (.ld 13 11 0#12) := by decide
@[simp] theorem rangeIntersect_fetch_2 : rangeIntersect.fetch 8#64 = some (.bltu 13 12 8#13) := by decide
@[simp] theorem rangeIntersect_fetch_3 : rangeIntersect.fetch 12#64 = some (.addi 12 13 0#12) := by decide
@[simp] theorem rangeIntersect_fetch_4 : rangeIntersect.fetch 16#64 = some (.ld 10 10 8#12) := by decide
@[simp] theorem rangeIntersect_fetch_5 : rangeIntersect.fetch 20#64 = some (.ld 11 11 8#12) := by decide
@[simp] theorem rangeIntersect_fetch_6 : rangeIntersect.fetch 24#64 = some (.bltu 10 11 8#13) := by decide
@[simp] theorem rangeIntersect_fetch_7 : rangeIntersect.fetch 28#64 = some (.addi 10 11 0#12) := by decide
@[simp] theorem rangeIntersect_fetch_8 : rangeIntersect.fetch 32#64 = some (.sltu 11 12 10) := by decide
@[simp] theorem rangeIntersect_fetch_9 : rangeIntersect.fetch 36#64 = some (.sub 13 0 11) := by decide
@[simp] theorem rangeIntersect_fetch_10 : rangeIntersect.fetch 40#64 = some (.and 11 13 10) := by decide
@[simp] theorem rangeIntersect_fetch_11 : rangeIntersect.fetch 44#64 = some (.and 10 13 12) := by decide
@[simp] theorem rangeIntersect_fetch_12 : rangeIntersect.fetch 48#64 = some (.jalr 0 1 0#12) := by decide

end NgtcpRV
