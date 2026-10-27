import NgtcpRV
open NgtcpRV

/-! Axiom audit. Primary (kernel-checked) results must depend only on
`propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms adjustPktNum_decode
#print axioms adjustPktNum_machine_eq_C
#print axioms adjustC_recovers
#print axioms adjustC_rfc
#print axioms adjustPktNum_machine_recovers
#print axioms adjustPktNum_machine_rfc
/-! Cross-check (bv_decide, natively checked LRAT): expected to list native axioms. -/
#print axioms CrossCheck.bv_adjustPktNum_machine_recovers
/-! range_init machine-code proof (kernel-checked). -/
#print axioms rangeInit_decode
#print axioms rangeInit_ok
#print axioms rangeIntersect_decode
#print axioms rangeIntersect_ok
