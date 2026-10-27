/-!
Keep-alive timing (conn.c, RFC 9000 §10.1.2).

To keep an otherwise-idle connection alive, ngtcp2 sends a keep-alive PING well
before the idle timeout expires (at a fraction of the idle period).  The
keep-alive deadline must be strictly earlier than the idle-timeout deadline, so a
keep-alive packet resets the idle timer before it fires.  We prove the keep-alive
interval (`idle_timeout` scaled down) is strictly less than the idle timeout.
-/
namespace NgtcpRV.ConnKeepAlive

/-- The keep-alive interval: a fraction (here half) of the idle timeout. -/
def keepAliveInterval (idleTimeout : Nat) : Nat := idleTimeout / 2

/-- **Keep-alive fires first**: for any positive idle timeout, the keep-alive
interval is strictly less than the idle timeout, so the PING is sent (and the idle
timer reset) before the connection would idle out. -/
theorem keepalive_before_idle (idleTimeout : Nat) (h : 1 ≤ idleTimeout) :
    keepAliveInterval idleTimeout < idleTimeout := by
  unfold keepAliveInterval; omega

/-- The keep-alive interval leaves room (the remaining half) before idle-out. -/
theorem keepalive_leaves_margin (idleTimeout : Nat) :
    keepAliveInterval idleTimeout + keepAliveInterval idleTimeout ≤ idleTimeout := by
  unfold keepAliveInterval; omega

end NgtcpRV.ConnKeepAlive
