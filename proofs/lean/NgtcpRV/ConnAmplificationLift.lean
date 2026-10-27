/-!
Anti-amplification lift on path validation (conn.c `dcid_tx_left`, RFC 9000 §8.1).

The 3x anti-amplification limit applies only to UNVALIDATED paths.  Once a path is
validated (`NGTCP2_DCID_FLAG_PATH_VALIDATED`), `dcid_tx_left` returns `SIZE_MAX`
— the limit is lifted and the endpoint may send freely.  We model `dcid_tx_left`
and prove: on a validated path the allowance is `SIZE_MAX` (effectively
unlimited), and on an unvalidated path it is the 3x budget (per `ConnFlowControl`).
-/
namespace NgtcpRV.ConnAmplificationLift

def SIZE_MAX : Nat := 2 ^ 64 - 1

/-- `dcid_tx_left`: SIZE_MAX if the path is validated, else `3*recv - sent`. -/
def dcidTxLeft (validated : Bool) (bytesRecv bytesSent : Nat) : Nat :=
  if validated then SIZE_MAX else 3 * bytesRecv - bytesSent

/-- **Validated path is unlimited**: a validated path has the maximum allowance. -/
theorem validated_unlimited (bytesRecv bytesSent : Nat) :
    dcidTxLeft true bytesRecv bytesSent = SIZE_MAX := by
  unfold dcidTxLeft; simp

/-- **Unvalidated path is 3x-limited**: the allowance on an unvalidated path is the
3x budget. -/
theorem unvalidated_three_x (bytesRecv bytesSent : Nat) :
    dcidTxLeft false bytesRecv bytesSent = 3 * bytesRecv - bytesSent := by
  unfold dcidTxLeft; simp

end NgtcpRV.ConnAmplificationLift
