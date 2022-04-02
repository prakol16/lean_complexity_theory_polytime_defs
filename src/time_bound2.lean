import code2
import frespects_pfun
import log_lemmas

open computability (encode_nat decode_nat)

def time : code → ℕ →. ℕ
| code.fst := λ v, pure (nat.log 2 v + 1)
| code.snd := λ v, pure (nat.log 2 v + 1)
| (code.bit _) := λ v, pure (nat.log 2 v + 1)
| (code.pair c₁ c₂) := λ v, (+3) <$> (time c₁ v) + (time c₂ v)
| (code.comp c₁ c₂) := λ v, (+1) <$> (time c₂ v) + (c₂.eval v >>= time c₁)
| (code.case c₁ c₂ c₃) := λ v, (+1) <$> (match encode_nat v with
  | [] := time c₃ 0
  | (ff :: xs) := time c₁ (decode_nat xs)
  | (tt :: xs) := time c₂ (decode_nat xs)
end)
| (code.fix f) := λ v₀, (+1) <$> (@pfun.fix (ℕ × ℕ) ℕ $ 
  λ vt, (time f vt.1) >>= λ t',
    (f.eval vt.1).map (λ v' : ℕ,
      if v'.unpair'.1 = 0 then sum.inl (vt.2+t')
      else sum.inr (v'.unpair'.2, vt.2+t'))
  ) (v₀, 0)

lemma add_def (x y : part ℕ) : x + y = x >>= λ x', y >>= (λ y', pure (x' + y')) :=
by { simp only [(+), (<*>)], simp, refl, }

private lemma time_frespects_once_eval_aux (f : code)
  (ih : ∀ (n : ℕ), (time f n).dom ↔ (f.eval n).dom) :
  pfun.frespects_once
  (λ (vt : ℕ × ℕ), (time f vt.1) >>= λ t',
    (f.eval vt.1).map (λ v' : ℕ,
      if v'.unpair'.1 = 0 then sum.inl (vt.2+t')
      else sum.inr (v'.unpair'.2, vt.2+t')))
  (λ (v : ℕ), (f.eval v).map $ λ v',
    if (nat.unpair' v').1 = 0 then sum.inl (nat.unpair' v').2 else sum.inr (nat.unpair' v').2)
  prod.fst :=
begin
  intro a, split,
  { simp [ih], }, split,
  { intro a',
    simp only [part.bind_eq_bind, part.mem_bind_iff, part.mem_map_iff, exists_prop, forall_exists_index, and_imp],
    intros n hn e he h, use e, refine ⟨he, _⟩,
    split_ifs at h, { contradiction, },
    rw ← h, split_ifs; refl,  },
  simp only [part.bind_eq_bind, part.mem_bind_iff, part.mem_map_iff, exists_prop, forall_exists_index, and_imp],
  intros n₁ n₂ hn₂ b hb h,
  refine ⟨b.unpair'.snd, b, hb, _⟩,
  split_ifs at h ⊢, { refl, }, { contradiction, },
end

lemma time_dom_iff_eval_dom (c : code) (n : ℕ) : (time c n).dom ↔ (c.eval n).dom :=
begin
  induction c generalizing n,
  iterate 3 { simp [time], refl, },
  case code.pair : c₁ c₂ c₁ih c₂ih { simp [time, add_def, c₁ih, c₂ih], },
  case code.comp : c₁ c₂ c₁ih c₂ih { simp [time, add_def, c₁ih, c₂ih], tauto, },
  case code.case : c₁ c₂ c₃ c₁ih c₂ih c₃ih { simp only [time, code.eval],
    rcases (encode_nat n) with _|_|_; simp [c₁ih, c₂ih, c₃ih, time], },
  case code.fix : f ih
  { simp only [time, code.eval], refine pfun.eq_dom_of_frespects_once prod.fst _ _,
    exact time_frespects_once_eval_aux _ ih, }
end

lemma exists_mem_time_iff_exists_mem_dom (c : code) (n : ℕ) : (∃ t, t ∈ time c n) ↔ ∃ m, m ∈ c.eval n :=
by { rw [← part.dom_iff_mem, ← part.dom_iff_mem], apply time_dom_iff_eval_dom, }

lemma time_frespects_once_eval (f : code) :
  pfun.frespects_once
  (λ (vt : ℕ × ℕ), (time f vt.1) >>= λ t',
    (f.eval vt.1).map (λ v' : ℕ,
      if v'.unpair'.1 = 0 then sum.inl (vt.2+t')
      else sum.inr (v'.unpair'.2, vt.2+t')))
  (λ (v : ℕ), (f.eval v).map $ λ v',
    if (nat.unpair' v').1 = 0 then sum.inl (nat.unpair' v').2 else sum.inr (nat.unpair' v').2)
  prod.fst :=
by { apply time_frespects_once_eval_aux, simp [time_dom_iff_eval_dom], }

def time_bound (c : code) (bound : ℕ → ℕ) : Prop :=
∀ (n m : ℕ), n ≤ m → ∃ t ∈ time c n, t ≤ bound (nat.log 2 m)

def time_bound_of_monotonic_iff (c : code) {bound : ℕ → ℕ} (mono : monotone bound) :
  time_bound c bound ↔ ∀ n, ∃ t ∈ time c n, t ≤ bound (nat.log 2 n) :=
begin
  split, { intros h n, exact h n n rfl.le, },
  intros h n m hnm,
  obtain ⟨t, ht, H⟩ := h n,
  use [t, ht],
  refine H.trans _,
  apply mono, exact nat.log_le_log_of_le hnm,
end

/- Why isn't this already a lemma? -/
lemma sq_mono : monotone (λ n : ℕ, n^2) := by { intros x y hxy, nlinarith, }

lemma pair_bound {v₁ v₂ b₁ b₂ : ℕ} (hv₁ : nat.log 2 v₁ ≤ b₁^2) (hv₂ : nat.log 2 v₂ ≤ b₂^2) :
  nat.log 2 (nat.mkpair' v₁ v₂) ≤ (b₁ + b₂ + 3)^2 :=
begin
  have : 2 * nat.log 2 (nat.log 2 v₁ + 1) ≤ 4 * b₁ + 4 :=
    calc 2 * nat.log 2 (nat.log 2 v₁ + 1)
      ≤ 2 * nat.log 2 (b₁^2 + 1) : by { mono*,  { apply nat.log_monotone, mono, }, all_goals { exact zero_le _, }, }
  ... ≤ 2 * nat.log 2 ((b₁ + 1)^2) : by { mono*, { apply nat.log_monotone, ring_nf SOP, simp, }, all_goals { exact zero_le _, }, }
  ... ≤ 2 * (2 * (nat.log 2 (b₁ + 1) + 1)) : by { mono, { apply nat.log_pow_k_le, }, all_goals { exact zero_le _, }, }
  ... = 4 * nat.log 2 (b₁ + 1) + 4 : by ring
  ... ≤ 4 * b₁ + 4 : by { mono*, { exact nat.log_succ_le _ _, }, all_goals { exact zero_le _, }, },
  
  exact calc nat.log 2 (nat.mkpair' v₁ v₂)
      ≤ nat.log 2 v₁ + nat.log 2 v₂ + 2 * nat.log 2 (nat.log 2 v₁ + 1) + 5 : nat.mkpair'_le v₁ v₂
  ... ≤ b₁^2 + b₂^2 + (4 * b₁ + 4) + 5 : by mono*
  ... ≤ (b₁ + b₂ + 3)^2 : by { ring_nf, nlinarith, }
end

lemma eval_le_time {c : code} {n m t : ℕ} (hm : m ∈ c.eval n) (ht : t ∈ time c n) : nat.log 2 m ≤ t^2 :=
begin
  induction c generalizing n m t,
  -- TODO: these 3 cases are very similar (only the last part is different),
  -- but iterate gives some weird error, figure out why
  case code.fst : { simp only [time, part.pure_eq_some, code.eval, part.mem_some_iff] at hm ht, subst ht, subst hm,
    rw sq, exact (le_add_right (nat.log_le_log_of_le (nat.unpair'_fst_le n))).trans (nat.le_mul_self _), },
  case code.snd : { simp only [time, part.pure_eq_some, code.eval, part.mem_some_iff] at hm ht, subst ht, subst hm,
    rw sq, exact (le_add_right (nat.log_le_log_of_le (nat.unpair'_snd_le n))).trans (nat.le_mul_self _), },
  case code.bit : b { simp only [time, part.pure_eq_some, code.eval, part.mem_some_iff, pfun.coe_val] at hm ht, subst ht, subst hm,
    rw sq, refine trans _ (nat.le_mul_self _), cases n, { cases b; simp [nat.bit], }, simp, },
  case code.pair : c₁ c₂ c₁ih c₂ih
  { simp only [time, add_def, part.map_eq_map, part.pure_eq_some, part.bind_eq_bind, part.bind_some_eq_map, part.bind_map,
  part.mem_bind_iff, part.mem_map_iff, exists_prop, code.eval, part.ret_eq_some] at hm ht,
    obtain ⟨t₁, ht₁, t₂, ht₂, ht⟩ := ht, subst ht,
    obtain ⟨v₁, hv₁, v₂, hv₂, hm⟩ := hm, subst hm,
    rw [add_assoc t₁ 3 t₂, add_comm 3 t₂, ← add_assoc t₁ t₂ 3],
    exact pair_bound (c₁ih hv₁ ht₁) (c₂ih hv₂ ht₂), },
  case code.comp : c₁ c₂ c₁ih c₂ih
  { simp only [time, code.eval, exists_prop, part.pure_eq_some, part.bind_eq_bind, part.bind_map, part.map_eq_map, part.mem_bind_iff, add_def] at hm ht,
    obtain ⟨t₂, ht₂, t₁, ⟨v, hv, ht₁⟩, ht⟩ := ht,
    obtain ⟨v', hv', hm⟩ := hm, have := part.mem_unique hv hv', subst this,
    refine (c₁ih hm ht₁).trans _, apply sq_mono, simp only [part.mem_some_iff] at ht, rw ht,
    simp, },
  case code.case : c₁ c₂ c₃ c₁ih c₂ih c₃ih
  { simp only [time, part.map_eq_map, part.mem_map_iff, exists_prop, code.eval] at hm ht,
    rcases encode_nat n with _|_|_; simp only [time, code.eval],
    { rintros h ⟨t₃, ht₃, ht⟩, refine (c₃ih h ht₃).trans _,  apply sq_mono, rw ← ht, simp, },
    { rintros h ⟨t₁, ht₁, ht⟩, refine (c₁ih h ht₁).trans _, apply sq_mono, rw ← ht, simp, },
    { rintros h ⟨t₂, ht₂, ht⟩, refine (c₂ih h ht₂).trans _, apply sq_mono, rw ← ht, simp, }, },
  case code.fix : f ih
  { simp only [time, part.mem_map_iff, part.map_eq_map] at ht,
    rename t t_succ, obtain ⟨t, ht, ht_succ⟩ := ht,
    obtain ⟨⟨mL, tL⟩, htime, heval⟩ := pfun.frespects_last_step (time_frespects_once_eval f) ht hm,
    simp only [part.mem_map_iff, exists_prop, part.bind_eq_bind, part.mem_bind_iff] at htime heval,
    obtain ⟨m', hm', hmm'⟩ := heval, obtain ⟨tf, htf, m'', hm'', htL⟩ := htime,
    have : m' = m'' := part.mem_unique hm' hm'', subst this, clear hm'',
    split_ifs at hmm' htL, swap, { contradiction, },
    exact calc nat.log 2 m ≤ nat.log 2 m' : by { apply nat.log_monotone, rw ← hmm', exact nat.unpair'_snd_le _, }
                      ...  ≤ tf^2 : ih hm' htf
                      ...  ≤ t_succ^2 : by { rw [← ht_succ, ← htL], mono, apply le_add_right, simp, }, },
end

lemma one_le_time {c : code} {n t : ℕ} (ht : t ∈ time c n) : 1 ≤ t :=
begin
  cases c,
  iterate 3 { simp [time] at ht, simp [ht], },
  all_goals { simp only [time, add_def, part.map_eq_map, part.pure_eq_some, part.bind_eq_bind, part.bind_some_eq_map, part.bind_map,
      part.mem_bind_iff, part.mem_map_iff, exists_prop] at ht, },
  { obtain ⟨_, _, _, _, ht⟩ := ht, rw ← ht, nlinarith only, },
  { obtain ⟨_, _, _, _, ht⟩ := ht, rw ← ht, nlinarith only, },
  { obtain ⟨_, _, ht⟩ := ht, rw ← ht, nlinarith only, },
  { obtain ⟨_, _, ht⟩ := ht, rw ← ht, nlinarith only, },
end

lemma time_bound_fst : time_bound code.fst (λ t, t+1) :=
by { rw time_bound_of_monotonic_iff, { simp [time], }, { intros x y h, simpa }, }

lemma time_bound_snd : time_bound code.snd (λ t, t+1) :=
by { rw time_bound_of_monotonic_iff, { simp [time], }, { intros x y h, simpa }, }

lemma time_bound_bit (b : bool) : time_bound (code.bit b) (λ t, t+1) :=
by { rw time_bound_of_monotonic_iff, { simp [time], }, { intros x y h, simpa }, }

lemma time_bound_pair {c₁ c₂ : code} {b₁ b₂ : ℕ → ℕ} (hb₁ : time_bound c₁ b₁) (hb₂ : time_bound c₂ b₂) :
  time_bound (code.pair c₁ c₂) (λ t, (b₁ t) + (b₂ t) + 3) :=
begin
  intros n N h,
  obtain ⟨t₁, ht₁, hb₁⟩ := hb₁ n N h, obtain ⟨t₂, ht₂, hb₂⟩ := hb₂ n N h,
  use (t₁ + t₂ + 3), split,
  { rw ← part.eq_some_iff at ht₁ ht₂, simp [time, ht₁, ht₂, add_def], ring, },
  { mono*, },
end

lemma time_bound_comp {c₁ c₂ : code} {b₁ b₂ : ℕ → ℕ} (hb₁ : time_bound c₁ b₁) (hb₂ : time_bound c₂ b₂) :
  time_bound (code.comp c₁ c₂) (λ t, (b₂ t) + (b₁ ((b₂ t)^2 + 1)) + 1) :=
begin
  intros n N h,
  obtain ⟨t₂, ht₂, hb₂⟩ := hb₂ n N h,
  obtain ⟨m, hm⟩ := (exists_mem_time_iff_exists_mem_dom c₂ n).mp ⟨_, ht₂⟩,
  obtain ⟨t₁, ht₁, hb₁⟩ := hb₁ m (2^((b₂ $ nat.log 2 N)^2 + 1)) _,
  { use t₁ + t₂ + 1, split,
    { rw ← part.eq_some_iff at ht₁ ht₂ hm, simp [time, ht₁, ht₂, add_def, hm], ring, },
    rw add_comm t₁ t₂, mono*, rwa nat.log_pow (show 1 < 2, by norm_num) at hb₁, },
  apply le_of_lt, apply nat.lt_pow_succ_of_log_le, { norm_num },
  exact calc nat.log 2 m ≤ t₂^2 : eval_le_time hm ht₂
                     ... ≤ (b₂ $ nat.log 2 N)^2 : by mono,
end

