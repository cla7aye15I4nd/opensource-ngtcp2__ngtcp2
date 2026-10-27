import NgtcpRV.ConnCongestion
import NgtcpRV.ConnAmplification
/-!
Connection-migration state reset (conn.c, RFC 9000 §9.4).

On migration to a new path, an endpoint resets its congestion controller (back to
the initial window) and treats the new path as unvalidated (anti-amplification
counters reset to zero), until the new path is validated.  We prove both resets
preserve their safety invariants: the reset congestion window still respects the
floor, and the fresh amplification state satisfies `bytes_sent <= 3*bytes_recv`.
-/
namespace NgtcpRV.ConnMigration
open NgtcpRV.ConnCongestion NgtcpRV.ConnAmplification

/-- Migrating resets the congestion window to the minimum — still at/above floor. -/
theorem migration_cwnd_safe (s : CcState) (h : CcInv s) : CcInv (reset s) := reset_inv s h

/-- A freshly-migrated path starts with zero bytes sent/received, trivially within
the 3x anti-amplification bound. -/
theorem migration_amp_fresh : AmpInv ⟨0, 0⟩ := by unfold AmpInv; decide

end NgtcpRV.ConnMigration
