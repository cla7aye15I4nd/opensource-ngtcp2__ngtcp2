/* Proof stub: reaching ngtcp2_unreachable() is a verification failure.
   (The real implementation calls abort(), which CBMC would otherwise
   model as assume(false) and silently prune the path.) */
void ngtcp2_unreachable_fail(const char *file, int line, const char *func) {
  (void)file; (void)line; (void)func;
  __CPROVER_assert(0, "ngtcp2_unreachable() reached");
  __CPROVER_assume(0);
}
