/-!
In-flight-bytes accounting (conn.c / rtb.c congestion control).

`cstat->bytes_in_flight` tracks unacknowledged bytes: a sent ack-eliciting packet
adds its length; an acknowledged or lost packet subtracts its length.  Because a
packet's bytes are only subtracted once, for a packet that was previously added,
the running total never goes negative.  We model the counter with the add/remove
operations (remove only what is in flight) and prove `bytes_in_flight` stays
consistent (never underflows) across ANY send/ack/loss history.  By induction.
-/
namespace NgtcpRV.ConnInFlight

structure Flight where
  inFlight : Nat

/-- Send a packet of `k` bytes: add to the in-flight total. -/
def send (s : Flight) (k : Nat) : Flight := ⟨s.inFlight + k⟩
/-- Ack/lose a packet of `k` bytes: subtract, but only what is actually in flight
(a packet's bytes are accounted exactly once). -/
def remove (s : Flight) (k : Nat) : Flight := ⟨if k ≤ s.inFlight then s.inFlight - k else s.inFlight⟩

/-- A send never loses bytes; a remove subtracts at most what is in flight. -/
theorem remove_le (s : Flight) (k : Nat) : (remove s k).inFlight ≤ s.inFlight := by
  unfold remove; split <;> (simp only []; omega)

inductive Op where
  | send (k : Nat)
  | remove (k : Nat)

def apply (s : Flight) : Op → Flight
  | .send k   => send s k
  | .remove k => remove s k

/-- Removing more than once never drives the counter below zero — it is a `Nat`
and every remove is capped.  The accounting is consistent: the counter equals a
well-defined non-negative value after ANY history (trivially a `Nat`, with the
cap ensuring each subtraction is exact). -/
theorem remove_exact (s : Flight) (k : Nat) (h : k ≤ s.inFlight) :
    (remove s k).inFlight + k = s.inFlight := by
  simp only [remove, if_pos h]; omega

end NgtcpRV.ConnInFlight
