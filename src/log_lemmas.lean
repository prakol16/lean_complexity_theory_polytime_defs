import data.nat.log
import tactic


namespace nat

attribute [simp] log_mul_base

@[simp] lemma log_base_mul (b n : ℕ) (hb : 1 < b) (hn : 0 < n) : log b (b * n) = log b n + 1 :=
by { rw mul_comm, simp [hb, hn], }

@[simp] lemma log_base_mul_add_lt_base (b n x : ℕ) (hb : 1 < b) (hn : 0 < n) (hx : x < b) :
  log b (b * n + x) = (log b n) + 1 :=
begin
  suffices : log b ((b * n + x) / b * b) = log b n + 1, { simpa, },
  conv_lhs { rw [add_comm, add_mul_div_left _ _ (nat.zero_lt_one.trans hb), div_eq_of_lt hx], },
  simp [hb, hn],
end

lemma lt_pow_succ_log_self' {b : ℕ} (hb : 1 < b) (x : ℕ) : x < b^(log b x + 1) :=
begin
  cases x, { simp, linarith, },
  apply lt_pow_succ_log_self hb,
  simp,
end

lemma log_pow_k_le (b x k : ℕ) : log b (x^k) ≤ k * (log b x + 1) :=
begin
  cases b, { simp, }, cases b, { simp, },
  set b' := b.succ.succ, have one_lt : 1 < b' := by simp [b'],
  suffices : x^k ≤ b'^(k*(log b' x+1)),
  { refine (log_le_log_of_le this).trans _, rw log_pow one_lt, },
  rw pow_mul', mono,
  apply le_of_lt, apply lt_pow_succ_log_self' one_lt,
end

lemma log_succ_le (b x : ℕ) : log b (x + 1) ≤ x :=
begin
  cases b, { simp, }, cases b, { simp, },
  conv_rhs { rw ← @log_pow b.succ.succ (show 1 < b.succ.succ, by simp) x, },
  apply log_monotone,
  apply le_of_lt_succ, simp only [nat.succ_eq_add_one, add_lt_add_iff_right],
  apply lt_pow_self, simp,
end

lemma lt_pow_succ_of_log_le {b x y : ℕ} (hb : 1 < b) (h : log b x ≤ y) : x < b^(y+1) :=
calc x < b^(log b x + 1) : lt_pow_succ_log_self' hb x
   ... ≤ b^(y + 1) : by { apply pow_mono (le_of_lt hb), simpa, }


end nat