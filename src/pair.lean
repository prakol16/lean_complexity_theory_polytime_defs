import data.num.basic
import computability.encoding
import lists

attribute [simp] computability.decode_encode_nat
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

lemma encode_num_last (n : num) : (encode_num n).last'.get_or_else tt = tt :=
by { cases n, { refl, }, apply option.get_or_else_of_mem (encode_pos_num_last n), }

@[simp] lemma encode_nat_last (n : ℕ) : (encode_nat n).last'.get_or_else tt = tt := encode_num_last n

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

def mkpair (a b : list bool) : list bool :=
mkpair' (encode_nat a.length) (a ++ b)

def unpair (ls : list bool) : list bool × list bool :=
(unpair' ls).2.split_at (decode_nat (unpair' ls).1)

@[simp] lemma mkpair_unpair (a b : list bool) : unpair (mkpair a b) = (a, b) :=
by simp [unpair, mkpair]

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

end list

namespace nat

def mkpair' (a b : ℕ) : ℕ := 
decode_nat (list.mkpair (encode_nat a) (encode_nat b))

def unpair' (n : ℕ) : ℕ × ℕ :=
(decode_nat (list.unpair (encode_nat n)).1, decode_nat (list.unpair (encode_nat n)).2)

@[simp] lemma unpair'_mkpair' (a b : ℕ) : unpair' (mkpair' a b) = (a, b) :=
begin
  simp only [unpair', mkpair'],
  rw computability.encode_decode_nat, { simp },
  simp [list.mkpair_last],
end

#eval mkpair' 3 4

end nat
