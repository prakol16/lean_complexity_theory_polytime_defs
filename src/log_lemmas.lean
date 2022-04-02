import data.nat.log
import tactic


namespace nat

lemma log_pow_k_le (b x k : ℕ) : log b (x^k) ≤ k * (log b x + 1) :=
begin
  cases b, { simp, }, cases b, { simp, },
  set b' := b.succ.succ, have one_lt : 1 < b' := by simp [b'],
  suffices : x^k ≤ b'^(k*(log b' x+1)),
  { refine (log_le_log_of_le this).trans _, rw log_pow one_lt, },
  rw pow_mul', mono,
  cases x, { exact zero_le _, },
  apply le_of_lt, apply lt_pow_succ_log_self; simp,
end

lemma log_succ_le (b x : ℕ) : log b (x + 1) ≤ x :=
begin
  cases b, { simp, }, cases b, { simp, },
  conv_rhs { rw ← @log_pow b.succ.succ (show 1 < b.succ.succ, by simp) x, },
  apply log_monotone,
  apply le_of_lt_succ, simp only [nat.succ_eq_add_one, add_lt_add_iff_right],
  apply lt_pow_self, simp,
end

end nat