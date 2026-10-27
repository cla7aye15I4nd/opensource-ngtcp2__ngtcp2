# RISC-V machine-code proofs (Lean 4, kernel-checked)

An independent, strictly stronger verification layer than the CBMC suite: each
ngtcp2 function is compiled to RV64, and its MACHINE CODE is proven correct in
Lean 4, with proof terms checked by the Lean kernel (axioms: only propext,
Classical.choice, Quot.sound — see Audit.lean). CBMC trusts an external
SAT/SMT solver; these proofs trust only the Lean kernel.

Functions proven at the machine-code level:
- ngtcp2_pkt_adjust_pkt_num  (AdjustPktNum.lean): decode==LLVM, execution
  recovers the packet number per RFC 9000 §17.1; + native bv_decide cross-check.
- ngtcp2_get_uvarint / get_uvarintlen / put_uvarintlen (Varint.lean).
- ngtcp2_range_init (RangeInit.lean): decode==LLVM, correct return, and
  SPATIAL MEMORY SAFETY — with write permission to exactly the 16-byte range
  object, the run does not fault, so every store lands inside the object; memory
  outside is unchanged.

Build: depends on opencompl/riscv-lean (RV64 semantics proven equivalent to the
Sail model). With that dependency fetched, `lake build` then `lake env lean
Audit.lean` reproduces the kernel-checked results. gen_lean_fn.py emits the Lean
`Program` for a function from its RISC-V object file (words + an independent
llvm-objdump decode, kernel-checked to agree).
