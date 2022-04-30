import computability.partrec
import computability.encoding
import pair
import part

namespace num

@[simp] lemma bit1_ne_zero (n : num) : n.bit1 ≠ 0 := by cases n; trivial
@[simp] lemma bit0_zero_iff_zero (n : num) : n.bit0 = 0 ↔ n = 0 :=
⟨λ h, by { cases n, { refl, }, contradiction, }, by { rintro rfl, refl, }⟩
@[simp] lemma succ_ne_zero (n : num) : n + 1 ≠ 0 := by cases n; trivial

end num

open num (to_bits of_bits)

section
parameter (ι : Type)

/--
A `code` is a description of an algorithm. The semantics are as follows:
  - `fst` takes as input the encoding of a pair `(a, b)` and outputs `a`
  - `snd` takes as input the encoding of a pair `(a, b)` and outputs `b`
  - `bit` takes as input a natural number `n` and appends the bit `b` (in the least significant place)
  - `pair` given `c₁` and `c₂`, the code which outputs the pair `(c₁(x), c₂(x))` on input `x`
  - `comp` compose two codes
  - `case` given `f g h`, calls `f` if the least significant bit (lsb) is `0`, `g` if it is `1`, and `h` if the number is `0`
  - `fix` given `f`, repeatedly calls `f` on the input, interpreting the result as a tuple `(a, b)` until `a = 0`.
-/
inductive code
| fst : code
| snd : code
| bit : bool → code
| pair : code → code → code
| comp : code → code → code
| case : code → code → code → code
| fix : code → code

parameter {ι}
@[simp] def code.eval : code → ℕ →. ℕ
| code.fst := λ n, part.some (nat.unpair' n).1
| code.snd := λ n, part.some (nat.unpair' n).2
| (code.bit b) := nat.bit b
| (code.pair f g) := λ v, do x ← f.eval v, y ← g.eval v, return (nat.mkpair' x y) 
| (code.comp f g) := λ v, g.eval v >>= f.eval
| (code.case f g h) := λ v, match to_bits v with
  | [] := h.eval 0
  | (ff :: xs) := f.eval (of_bits xs)
  | (tt :: xs) := g.eval (of_bits xs)
end
| (code.fix f) := pfun.fix $ λ v, (f.eval v).map $ λ v',
  if (nat.unpair' v').1 = 0 then sum.inl (nat.unpair' v').2 else sum.inr (nat.unpair' v').2

end

section
/- In this section we define many useful starting codes, such as `code.id` and `code.const` 
   These functions rely on the particular encoding of `nat.mkpair'`; the reason for this is to minimize
   the number of primitive functions we need to put in `code`. Specifically, they take advantage of the fact
   that we can split a sequence of bits into a tuple where the first entry has constant size by adding
   some constant number of "header" bits. -/

open code
local infixr `∘`:90 := comp

def zero : code := fst ∘ (bit tt)
@[simp] lemma zero_apply (n : ℕ) : zero.eval n = part.some 0 :=
by simp [zero, nat.bit, ← nat.mkpair'_zero]

def one : code := bit tt ∘ zero
@[simp] lemma one_apply (n : ℕ) : one.eval n = part.some 1 :=
by simp [one, nat.bit]

protected def code.id : code := snd ∘ (bit tt)
@[simp] lemma id_apply (n : ℕ) : code.id.eval n = part.some n :=
by simp [code.id, nat.bit, ← nat.mkpair'_zero]

def append_const : list bool → code
| [] := code.id
| (b :: bs) := bit b ∘ (append_const bs)
lemma append_const_apply' (bs : list bool) (n : ℕ) (hn : n ≠ 0 ∨ bs ∈ set.range to_bits) :
  (append_const bs).eval n = part.some (of_bits (bs ++ to_bits n)) :=
begin
  induction bs with hd tl ih, { simp [append_const], },
  specialize ih _, { cases hn, { tauto, }, exact or.inr (num.mem_to_bits_range_of_cons hn), },
  by_cases tl = [],
  { subst h, simp [num.mem_to_bits_range_iff] at hn,
    cases hn, swap, { subst hn, simp [append_const], refl, },
    cases hd; simp [append_const, ih, (show (to_bits n) ≠ [], by simpa)]; refl, },
  cases hd; simp [append_const, ih, h]; refl,
end

protected def code.const (c : ℕ) : code := (append_const (to_bits c)) ∘ zero
@[simp] lemma const_apply (c n : ℕ) : (code.const c).eval n = part.some c :=
begin
  simp only [code.const, code.eval, zero_apply, part.bind_eq_bind, part.bind_some],
  rw append_const_apply', { simp, },
  right, simp,
end

/-- Clamps a natural number to {0, 1}. Returns `0` if the input is `0` and `1` otherwise -/
def to_bit : code := case one one zero
@[simp] lemma to_bit_apply (n : ℕ) : to_bit.eval n = part.some (if n = 0 then 0 else 1) :=
begin
  have : to_bits n = [] ↔ n = 0 := by simp,
  simp only [to_bit, code.eval],
  rcases (to_bits n) with _|_|_,
  all_goals { intro, simp * at *, },
end

/-- Returns the right shift of a number `n` -/
def tail : code := snd ∘ (bit ff) ∘ (bit tt) ∘ (bit tt)
@[simp] lemma tail_apply_bit1 (n : ℕ) : tail.eval (bit1 n) = part.some n :=
by simp [tail, nat.bit, ← nat.mkpair'_one]
@[simp] lemma tail_apply_bit0 (n : ℕ) : tail.eval (bit0 n) = part.some n :=
begin
  cases n, { simp [tail], dec_trivial, },
  simp [tail, nat.unpair', nat.bit, num.bit0_of_bit0, num.bit1_of_bit1, nat.unpair',
    list.unpair, list.unpair', list.take_while, list.after],
end

/-- Evaluates `f` and `g` on the input;, then appends the bit `to_bit f` to `g` -/
def cons_bit (f g : code) : code := (case (tail ∘ tail) (bit ff) zero) ∘ (pair (to_bit ∘ f) g)
@[simp] lemma cons_bit_apply (f g : code) (n : ℕ) :
  (cons_bit f g).eval n = f.eval n >>= (λ r, (g.eval n).map (if r = 0 then bit0 else bit1)) :=
begin
  simp only [cons_bit, code.eval],
  cases (f.eval n) with d₁ v₁, by_cases h₁ : d₁, swap, { simp [h₁], }, simp only [h₁, part.mk_some],
  cases (g.eval n) with d₂ v₂, by_cases h₂ : d₂, swap, { simp [h₂], }, simp only [h₂, part.mk_some],
  cases v₁ h₁,
  { simp [nat.mkpair'_zero, nat.bit], },
  { simp [nat.mkpair'_one, nat.bit, num.bit0_of_bit0, num.bit1_of_bit1], }
end

protected def code.ite (c f g : code) : code :=
(case f g f) ∘ (cons_bit c code.id)
@[simp] lemma code_ite_apply (c f g : code) (n : ℕ) :
  (code.ite c f g).eval n = (c.eval n) >>= λ r, if r = 0 then f.eval n else g.eval n :=
begin
  simp only [code.ite, code.eval, cons_bit_apply, id_apply],
  cases (c.eval n) with d₁ v₁, by_cases h₁ : d₁, swap, { simp [h₁], }, simp only [h₁, part.mk_some],
  cases v₁ h₁,
  { cases n; simp, }, simp,
end

end

