import data.num.basic
import data.nat.log
import computability.encoding
import lists

attribute [simp] computability.decode_encode_nat
attribute [simp] nat.log_mul_base

namespace nat

@[simp] lemma log_base_mul (b n : ℕ) (hb : 1 < b) (hn : 0 < n) : log b (b * n) = (log b n) + 1 :=
by { rw mul_comm, exact nat.log_mul_base b n hb hn, } 

@[simp] lemma log_base_mul_add (b n x : ℕ) (hb : 1 < b) (hn : 0 < n) (hx : x < b) : log b (b * n + x) = (log b n) + 1 :=
begin
  suffices : log b ((b * n + x) / b * b) = log b n + 1, { simpa, },
  conv_lhs { rw [add_comm, add_mul_div_left _ _ (nat.zero_lt_one.trans hb), div_eq_of_lt hx], },
  simp [hb, hn],
end

@[simp] lemma log2_bit (n : ℕ) (hn : 0 < n) (b : bool) : log 2 (bit b n) = (log 2 n) + 1 :=
begin
  cases n, { simp at hn, contradiction, },
  cases b; simp [nat.bit, nat.bit0_val n.succ, nat.bit1_val n.succ],
end

end nat

open computability (encode_nat decode_nat)

namespace option

lemma iget_eq_get_of_some {α : Type*} [inhabited α] (x : option α) (h : x.is_some) :
  x.iget = get h := by { cases x, { cases h, }, refl, }


lemma get_or_else_eq_get_of_some {α : Type*} {x : option α} (d : α) (h : x.is_some) :
  x.get_or_else d = get h := by { cases x, { cases h, }, refl, }

lemma is_some_iff_not_is_none {α : Type*} (x : option α) :
  x.is_some ↔ ¬x.is_none := by cases x; simp

lemma get_or_else_of_mem {α : Type*} {x : option α} {y : α} (hy : y ∈ x) (d : α) :
  x.get_or_else d = y := by { cases x, { cases hy, }, simpa using hy, }

end option

namespace pos_num

lemma bit0_val (n : pos_num) : (bit0 n : ℕ) = 2 * (n : ℕ) :=
by { rw cast_bit0 n, exact nat.bit0_val _, }

lemma bit1_val (n : pos_num) : (bit1 n : ℕ) = 2 * (n : ℕ) + 1 :=
by { rw cast_bit1 n, exact nat.bit1_val _, }

end pos_num

namespace computability


lemma encode_decode_pos_num {ls : list bool} (h : ls.last'.iget = tt) :
  encode_pos_num (decode_pos_num ls) = ls :=
begin
  induction ls with hd tl ih, { exfalso, simpa using h, },
  cases tl with h t, { simp at h, subst h, refl, },
  specialize ih _, { simpa using h, },
  cases hd; simp [decode_pos_num, encode_pos_num, ih],
end

lemma encode_decode_num {ls : list bool} (h : ls.last'.get_or_else tt = tt) :
  encode_num (decode_num ls) = ls :=
begin
  cases ls with hd tl, { refl, },
  simp only [decode_num], simp only [encode_num, if_false, pos_num.cast_to_num],
  apply encode_decode_pos_num, convert h,
  rwa [option.iget_eq_get_of_some, option.get_or_else_eq_get_of_some],
  apply list.last_cons_is_some,
end

lemma encode_decode_nat (ls : list bool) (h : ls.last'.get_or_else tt = tt) :
  encode_nat (decode_nat ls) = ls :=
by simp [encode_nat, decode_nat, encode_decode_num h]

lemma encode_pos_num_last (n : pos_num) : tt ∈ (encode_pos_num n).last' :=
begin
  induction n with b₀ ih b₀ ih, { simp, refl, },
  all_goals { simp only [encode_pos_num], cases encode_pos_num b₀, { cases ih, }, simp [ih], },
end

example (n : pos_num) : bit1 (num.pos n : num) = num.pos (bit1 n) := by { refl, }
example (n : pos_num) : bit1 n = pos_num.bit1 n := pos_num.bit1_of_bit1 n

lemma encode_num_bit0 (n : num) (hn : n ≠ 0): encode_num (bit0 n) = ff :: encode_num n :=
begin
  cases n, { contradiction, },
  change bit0 (num.pos n) with num.pos (bit0 n),
  simp [encode_num, encode_pos_num, pos_num.bit0_of_bit0],
end

@[simp] lemma encode_nat_bit0 (n : ℕ) (hn : n ≠ 0) : encode_nat (bit0 n) = ff :: encode_nat n :=
by simp [encode_nat, encode_num_bit0, hn]

@[simp] lemma encode_num_bit1 (n : num) : encode_num (bit1 n) = tt :: encode_num n :=
begin
  cases n, { refl, },
  change bit1 (num.pos n) with num.pos (bit1 n),
  simp [encode_num, encode_pos_num, pos_num.bit1_of_bit1],
end

@[simp] lemma encode_nat_bit1 (n : ℕ) : encode_nat (bit1 n) = tt :: encode_nat n :=
by simp [encode_nat, encode_num_bit1]

@[simp] lemma decode_nat_bit (b : bool) (bs : list bool) (hbs : bs ≠ []) : decode_nat (b :: bs) = nat.bit b (decode_nat bs) :=
by cases b; simp [decode_nat, decode_num]; simp [decode_pos_num, hbs, nat.bit]

@[simp] lemma decode_nat_bit1 (bs : list bool) : decode_nat (tt :: bs) = bit1 (decode_nat bs) :=
by { cases bs, { refl, }, simp [nat.bit], }

lemma decode_nat_invalid (bs : list bool) (h : ff ∈ bs.last') : decode_nat bs = decode_nat (bs ++ [tt]) :=
begin
  induction bs with hd tl ih, { simp at h, contradiction, },
  cases tl with h t,
  { simp at h, subst h, dec_trivial, },
  specialize ih _, { rw option.mem_iff, simpa using h, },
  cases hd; simp [ih],
end

lemma encode_num_last (n : num) : (encode_num n).last'.get_or_else tt = tt :=
by { cases n, { refl, }, apply option.get_or_else_of_mem (encode_pos_num_last n), }

@[simp] lemma encode_nat_last (n : ℕ) : (encode_nat n).last'.get_or_else tt = tt := encode_num_last n

@[simp] lemma encode_pos_num_len (n : pos_num) : (encode_pos_num n).length = (nat.log 2 n) + 1 :=
begin
  induction n, { simp [encode_pos_num], },
  { simpa [encode_pos_num, pos_num.bit1_val], },
  { simpa [encode_pos_num, pos_num.bit0_val], },
end

lemma encode_num_len (n : num) : (encode_num n).length = if n = 0 then 0 else (nat.log 2 n) + 1 :=
begin
  cases n, { refl, },
  have : num.pos n ≠ 0 := dec_trivial,
  simp [encode_nat, encode_num, this],
end

lemma encode_nat_len (n : ℕ) : (encode_nat n).length = if n = 0 then 0 else nat.log 2 n + 1 :=
by simp [encode_nat, encode_num_len n]

lemma encode_nat_len_le (n : ℕ) : (encode_nat n).length ≤ nat.log 2 n + 1 :=
by { rw encode_nat_len, split_ifs; simp, }

@[simp] lemma encode_nat_zero : encode_nat 0 = [] := rfl
@[simp] lemma encode_nat_one : encode_nat 1 = [tt] := rfl
@[simp] lemma decode_nat_nil : decode_nat [] = 0 := rfl

lemma encode_nat_succ_ne_nil (n : ℕ) : encode_nat n.succ ≠ [] :=
by simp [← list.length_eq_zero, encode_nat_len]

lemma encode_nat_nil_iff_zero (n : ℕ) : encode_nat n = [] ↔ n = 0 :=
⟨λ h, by { cases n, refl, cases encode_nat_succ_ne_nil n h, }, λ h, by { rw h, refl, }⟩

lemma append_bits {n : ℕ} (bs : list bool) (h : n ≠ 0) : decode_nat (bs ++ encode_nat n) = bs.foldr nat.bit n :=
begin
  induction bs with hd tl ih, { simp, },
  cases n, { contradiction, },
  rw [list.cons_append, decode_nat_bit], { simp [ih] },
  exact list.append_ne_nil_of_ne_nil_right _ _ (encode_nat_succ_ne_nil n),
end

lemma append_bits' (n : ℕ) {bs : list bool} (h : bs.last'.get_or_else tt = tt) : decode_nat (bs ++ encode_nat n) = bs.foldr nat.bit n :=
begin
  induction bs with hd tl ih, { simp, },
  cases tl with h t,
  { simp at h, subst h, simp [nat.bit], },
  rw list.last'_cons at h,
  { specialize ih h, simp only [list.cons_append] at ih, simp [ih], },
  trivial,
end

lemma decode_nat_lb (l : list bool) (h : l.last'.get_or_else tt = tt) : (decode_nat l : ℤ) ≤ (2^l.length : ℤ) - 1 :=
begin
  induction l with hd tl ih, { simp, },
  cases hd,
  { have : tl ≠ [], { intro H, simp [H] at h, contradiction, },
    specialize ih _, { simp [this] at h, assumption, },
    simp only [this, nat.bit, decode_nat_bit, not_false_iff, ne.def, bool.cond_ff, list.length, pow_succ],
    rw nat.bit0_val, simp, linarith [ih], },
  specialize ih _,
  { cases tl, { refl }, simpa using h, },
  simp only [list.length, decode_nat_bit1, pow_succ],
  rw nat.bit1_val, simp, linarith [ih],
end

lemma decode_nat_ub (l : list bool) (h : l ≠ []) : 2^(l.length - 1) ≤ decode_nat l :=
begin
  induction l with hd tl ih, { contradiction, }, clear h,
  cases tl with h t, { cases hd; dec_trivial, },
  specialize ih _, { trivial, },
  cases hd; simp [nat.bit] at ⊢ ih,
  { conv_rhs { rw nat.bit0_val }, rw [pow_add, mul_comm], simpa, },
  conv_rhs { rw nat.bit1_val }, rw [pow_add, mul_comm], linarith [ih],
end

@[simp] lemma decode_nat_zero_iff_nil (l : list bool) : decode_nat l = 0 ↔ l = [] :=
begin
  split, swap, { rintro rfl, simp, },
  intro h,
  by_contra H,
  have := decode_nat_ub l H,
  rw [h, nonpos_iff_eq_zero] at this,
  apply pow_ne_zero _ _ this, trivial,
end

lemma decode_nat_mono (l₁ l₂ : list bool) (hl₁ : l₁.last'.get_or_else tt = tt) (h : l₁.length < l₂.length) :
  (decode_nat l₁) < (decode_nat l₂) :=
begin
  have h₁ := decode_nat_lb l₁ hl₁,
  have h₂ := decode_nat_ub l₂ (λ z, by { subst z, simpa using h, }),
  have : (2^l₁.length : ℤ) - 1 < 2^(l₂.length - 1),
  { have : l₁.length ≤ l₂.length - 1,
    { zify, rw int.coe_nat_sub,
      { apply int.le_of_lt_add_one, simpa using h, },
      rw nat.succ_le_iff, exact pos_of_gt h, },
    rw int.sub_one_lt_iff, apply pow_le_pow, { norm_num, }, { assumption, }, },
  zify at ⊢ h₂,
  exact lt_of_lt_of_le (lt_of_le_of_lt h₁ this) h₂,
end

lemma decode_nat_quasimono (l₁ l₂ : list bool) (h : l₁.length + 1 < l₂.length) :
  (decode_nat l₁) < (decode_nat l₂) :=
begin
  rcases H : l₁.last' with _|_|_,
  { apply decode_nat_mono, { rw H, refl }, linarith only [h], },
  { rw decode_nat_invalid l₁, apply decode_nat_mono, { simp, }, { simpa }, rw H, simp, },
  { apply decode_nat_mono, { rw H, simp, }, linarith only [h], },
end

end computability

namespace list

/-- (a, b) -> 2|a| + b size pairing function -/
def mkpair' (a b : list bool) : list bool :=
(list.repeat ff a.length) ++ (tt :: (a ++ b))

def unpair' (x : list bool) : list bool × list bool :=
(x.after (=tt)).split_at (x.take_while (=ff)).length

@[simp] lemma unpair'_mkpair' (a b : list bool) :
  unpair' (mkpair' a b) = (a, b) :=
begin
  simp only [unpair'],
  have h₁ : (mkpair' a b).after (=tt) = a ++ b,
  { apply list.after_spec, { simp [list.mem_repeat], }, { refl, }, },
  have h₂ : ((mkpair' a b).take_while (=ff)).length = a.length,
  { erw list.take_while_spec, { apply list.length_repeat, }, { simp [list.mem_repeat], }, trivial, },
  simp [h₁, h₂],
end

@[simp] lemma mkpair'_length (a b : list bool) : (mkpair' a b).length = 2*a.length + b.length + 1 :=
by { simp [mkpair'], ring, }

def mkpair (a b : list bool) : list bool :=
mkpair' (encode_nat a.length) (a ++ b)

def unpair (ls : list bool) : list bool × list bool :=
(unpair' ls).2.split_at (decode_nat (unpair' ls).1)

@[simp] lemma mkpair_unpair (a b : list bool) : unpair (mkpair a b) = (a, b) :=
by simp [unpair, mkpair]

lemma mkpair_length (a b : list bool) : (mkpair a b).length =
  if a.length = 0 then b.length + 1 else 2*(nat.log 2 a.length) + a.length + b.length + 3 :=
begin
  simp [mkpair, computability.encode_nat_len],
  split_ifs with h, { rw h, ring, }, ring, 
end

lemma mkpair_length_le (a b : list bool) : (mkpair a b).length ≤ 2*(nat.log 2 a.length) + a.length + b.length + 3 :=
by { rw mkpair_length, split_ifs; linarith, }

lemma mkpair'_last (a b : list bool) : (mkpair' a b).last' =
  some (b.last'.get_or_else (a.last'.get_or_else tt)) :=
begin
  simp only [mkpair'],
  cases b, cases a,
  all_goals { simp [option.get_or_else_eq_get_of_some _ (list.last_cons_is_some _ _)], },
end

lemma mkpair_last (a b : list bool) : (mkpair a b).last' =
  some (b.last'.get_or_else (a.last'.get_or_else tt)) :=
begin
  simp only [mkpair, mkpair'_last],
  cases b, cases a,
  all_goals { simp [option.get_or_else_eq_get_of_some _ (list.last_cons_is_some _ _)], },
end

lemma unpair'_snd_last (x : list bool) (hx : tt ∈ x.last') : (unpair' x).2.last'.get_or_else tt = tt :=
begin
  simp [unpair'],
  set l := (take_while (λ a, a = ff) x).length with e, rw ← e,
  by_cases l < (after (=tt) x).length,
  { simp [h], have := after_last x (=tt) ff,
    cases (after (=tt) x).last' with val, { refl, },
    simp at this, cases val, { cases option.mem_unique hx (this rfl), },
    refl, },
  simp at h, simp [h],
end

lemma unpair_snd_last (x : list bool) (hx : tt ∈ x.last') : (unpair x).2.last'.get_or_else tt = tt :=
begin
  simp [unpair], set l := decode_nat x.unpair'.fst,
  by_cases l < x.unpair'.snd.length,
  { simp [h, unpair'_snd_last x hx], },
  simp at h, simp [h],
end

lemma unpair_fst_len_lt (a : list bool) (ha : 1 < a.length) : (unpair a).1.length + 1 < a.length :=
begin
  simp only [unpair, unpair', list.drop_drop, list.length_drop, list.length_take, list.split_at_eq_take_drop],
  rcases a with _|_|_, { simp at ha, contradiction, },
  { simp only [length, add_lt_add_iff_right, min_lt_iff], right,
    apply nat.lt_of_le_of_lt (nat.sub_le _ _),
    simpa [after, after_length_lt] using ha, },
  { simp only [length, add_lt_add_iff_right, min_lt_iff], left,
    simpa [take_while, if_false] using ha, },
end

lemma unpair_snd_len_lt (a : list bool) (ha : a ≠ []) : (unpair a).2.length < a.length :=
begin
  simp only [unpair, unpair', drop_drop, split_at_eq_take_drop, length_drop],
  apply lt_of_le_of_lt (nat.sub_le _ _),
  rwa [after_length_lt, length_pos_iff_ne_nil],
end

end list

namespace nat

def mkpair' (a b : ℕ) : ℕ := 
decode_nat (list.mkpair (encode_nat a) (encode_nat b))

def unpair' (n : ℕ) : ℕ × ℕ :=
(decode_nat (list.unpair (encode_nat n)).1, decode_nat (list.unpair (encode_nat n)).2)

lemma unpair'_fst_lt (n : ℕ) : (unpair' n.succ).1 < n.succ :=
begin
  cases n, { dec_trivial, },
  simp only [unpair'], conv_rhs { rw ← computability.decode_encode_nat n.succ.succ, },
  apply computability.decode_nat_quasimono,
  apply list.unpair_fst_len_lt,
  simp [computability.encode_nat_len, pos_iff_ne_zero, log_eq_zero_iff, succ_eq_add_one],
  push_neg, simp [add_assoc],
end

lemma unpair'_fst_le (n : ℕ) : (unpair' n).1 ≤ n :=
by { cases n, dec_trivial, exact le_of_lt (unpair'_fst_lt _), }

lemma unpair'_snd_lt (n : ℕ) : (unpair' n.succ).2 < n.succ :=
begin
  simp only [unpair'], conv_rhs { rw ← computability.decode_encode_nat n.succ, },
  apply computability.decode_nat_mono,
  { rw list.unpair_snd_last,
    have := computability.encode_nat_last n.succ,
    rw option.get_or_else_eq_get_of_some at this, swap,
    { simpa using computability.encode_nat_succ_ne_nil n, },
    rw ← this, exact option.get_mem _, },
  apply list.unpair_snd_len_lt _ (computability.encode_nat_succ_ne_nil n),
end

lemma unpair'_snd_le (n : ℕ) : n.unpair'.2 ≤ n :=
by { cases n, dec_trivial, exact le_of_lt (unpair'_snd_lt _), }

@[simp] lemma unpair'_mkpair' (a b : ℕ) : unpair' (mkpair' a b) = (a, b) :=
begin
  simp only [unpair', mkpair'],
  rw computability.encode_decode_nat, { simp },
  simp [list.mkpair_last],
end

lemma mkpair'_zero (a : ℕ) : mkpair' 0 a = bit1 a :=
by simp [mkpair', list.mkpair, list.mkpair', nat.bit]

lemma mkpair'_one (a : ℕ) : mkpair' 1 a = bit0 (bit1 (bit1 (bit1 a))) :=
by simp [mkpair', list.mkpair, list.mkpair', nat.bit]

lemma mkpair'_ne_zero (a b : ℕ) : mkpair' a b ≠ 0 :=
by simp [mkpair', list.mkpair, list.mkpair']

lemma mkpair'_le (a b : ℕ) : nat.log 2 (mkpair' a b) ≤
  log 2 a + log 2 b + 2 * log 2 (log 2 a + 1) + 5 :=
begin
  simp only [mkpair'],
  exact calc log 2 (decode_nat (list.mkpair (encode_nat a) (encode_nat b)))
        ≤ log 2 (2^((list.mkpair (encode_nat a) (encode_nat b)).length) - 1) :
          by { apply log_monotone, zify [int.coe_nat_sub (one_le_iff_ne_zero.mpr (pow_ne_zero _ (show 2 ≠ 0, by norm_num)))], 
               apply computability.decode_nat_lb, rw list.mkpair_last, simp, }
    ...  ≤ (list.mkpair (encode_nat a) (encode_nat b)).length :
          by { conv_rhs { rw ← log_pow (show 1 < 2, by norm_num) (list.mkpair _ _).length }, apply log_monotone, exact tsub_le_self, }
    ... ≤ 2*(log 2 (encode_nat a).length) + (encode_nat a).length + (encode_nat b).length + 3 : list.mkpair_length_le _ _
    ... ≤ 2*(log 2 (log 2 a + 1)) + (log 2 a + 1) + (log 2 b + 1) + 3 :
          by { mono*, all_goals { try { apply log_monotone}, try { exact zero_le _, }, }, all_goals { exact computability.encode_nat_len_le _, }, }
    ... = _ : by ring_nf
end

example (n : ℕ) : 1 ≤ n ↔ n ≠ 0 := one_le_iff_ne_zero

def mklist (ls : list ℕ) : ℕ := ls.foldr nat.mkpair' 0
def unlist : ℕ → list ℕ
| 0 := []
| (succ n) := have wf : (unpair' n.succ).2 < n.succ := unpair'_snd_lt n,
              (unpair' n.succ).1 :: (unlist (unpair' n.succ).2)

@[simp] lemma unlist_mklist (ls : list ℕ) : unlist (mklist ls) = ls :=
begin
  induction ls with h t ih, { simp [mklist, unlist], },
  simp only [mklist, list.foldr],
  cases e : mkpair' h _, { cases mkpair'_ne_zero _ _ e, },
  simp only [unlist], rw ← e,
  split; simp, exact ih,
end

end nat


