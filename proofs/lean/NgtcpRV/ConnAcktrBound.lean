/-!
Ack-tracker entry bound (acktr.c / acktr.h).

The ack tracker keeps acknowledged packet-number ranges in a structure capped at
`NGTCP2_ACKTR_MAX_ENT = NGTCP2_MAX_ACK_RANGES + 1 = 33` entries; when generating an
ACK frame it emits at most `NGTCP2_MAX_ACK_RANGES = 32` ranges.  We prove the
entry count the generator uses stays within the array bound.
-/
namespace NgtcpRV.ConnAcktrBound

def MAX_ACK_RANGES : Nat := 32
def ACKTR_MAX_ENT : Nat := MAX_ACK_RANGES + 1

/-- The number of ranges emitted, clamped at MAX_ACK_RANGES. -/
def emittedRanges (available : Nat) : Nat := min available MAX_ACK_RANGES

theorem emitted_le_max (available : Nat) : emittedRanges available ≤ 32 := by
  unfold emittedRanges MAX_ACK_RANGES; omega

/-- The emitted ranges fit within the ACKTR_MAX_ENT-entry store (with room for the
in-progress entry). -/
theorem emitted_within_store (available : Nat) : emittedRanges available < ACKTR_MAX_ENT := by
  unfold emittedRanges ACKTR_MAX_ENT MAX_ACK_RANGES; omega

end NgtcpRV.ConnAcktrBound
