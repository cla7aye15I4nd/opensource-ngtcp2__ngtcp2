/-!
Time-unit constants (ngtcp2.h — `NGTCP2_SECONDS` etc.).

ngtcp2 expresses all durations in nanoseconds: `NGTCP2_SECONDS = 10^9 ns`,
`NGTCP2_MILLISECONDS = 10^6`, `NGTCP2_MICROSECONDS = 10^3`, `NGTCP2_NANOSECONDS =
1`.  Timer arithmetic (PTO, idle timeout, ack delay) relies on these relating by
factors of 1000.  We prove the conversions are internally consistent.
-/
namespace NgtcpRV.ConnTimeUnits

def NANOSECONDS : Nat := 1
def MICROSECONDS : Nat := 1000
def MILLISECONDS : Nat := 1000 * 1000
def SECONDS : Nat := 1000 * 1000 * 1000

theorem sec_is_1000_ms : SECONDS = 1000 * MILLISECONDS := by decide
theorem ms_is_1000_us : MILLISECONDS = 1000 * MICROSECONDS := by decide
theorem us_is_1000_ns : MICROSECONDS = 1000 * NANOSECONDS := by decide
theorem sec_is_1e9_ns : SECONDS = 1000000000 * NANOSECONDS := by decide

end NgtcpRV.ConnTimeUnits
