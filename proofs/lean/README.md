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
- ngtcp2_put_uvarint (PutUvarint.lean): the varint ENCODER, 51 instructions / 30 byte-stores / 4 magnitude branches; with write access to [p,p+8) and n<2^62 the run does not fault (spatial WRITE-safety on every path).
- ngtcp2_range_intersect (RangeIntersect.lean): decode==LLVM; with read access to exactly the two 16-byte argument objects it returns without faulting (spatial READ-safety across data-dependent branches) and performs no stores.
- ngtcp2_range_init (RangeInit.lean): decode==LLVM, correct return, and
  SPATIAL MEMORY SAFETY — with write permission to exactly the 16-byte range
  object, the run does not fault, so every store lands inside the object; memory
  outside is unchanged.

Build: depends on opencompl/riscv-lean (RV64 semantics proven equivalent to the
Sail model). With that dependency fetched, `lake build` then `lake env lean
Audit.lean` reproduces the kernel-checked results. gen_lean_fn.py emits the Lean
`Program` for a function from its RISC-V object file (words + an independent
llvm-objdump decode, kernel-checked to agree).
