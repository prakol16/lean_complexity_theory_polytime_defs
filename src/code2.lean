import computability.partrec
import computability.encoding
import pair
import part

open computability (encode_nat decode_nat)

section
parameter (ι : Type)

inductive code
| fst : code
| snd : code
| bit : bool → code
| pair : code → code → code
| comp : code → code → code
| case : code → code → code → code
| fix : code → code

parameter {ι}
/-- Given an implementation `impl` of the oracles, we can evaluate the `code`. -/
@[simp] def code.eval : code → ℕ →. ℕ
| code.fst := λ n, part.some (nat.unpair' n).1
| code.snd := λ n, part.some (nat.unpair' n).2
| (code.bit b) := nat.bit b
| (code.pair f g) := λ v, do x ← f.eval v, y ← g.eval v, return (nat.mkpair' x y) 
| (code.comp f g) := λ v, g.eval v >>= f.eval
| (code.case f g h) := λ v, match encode_nat v with
  | [] := h.eval 0
  | (ff :: xs) := f.eval (decode_nat xs)
  | (tt :: xs) := g.eval (decode_nat xs)
end
| (code.fix f) := pfun.fix $ λ v, (f.eval v).map $ λ v',
  if (nat.unpair' v').1 = 0 then sum.inl (nat.unpair v').2 else sum.inr (nat.unpair v').2

end

section
open code
local notation `{` x `, ` y `}` := pair x y
infixr `∘`:90 := comp

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
@[simp] lemma append_const_apply (bs : list bool) (n : ℕ) :
  (append_const bs).eval n = part.some (bs.foldr nat.bit n) :=
by { induction bs with _ _ ih, { simp [append_const], }, simp [append_const, ih], }
lemma append_const_apply' (bs : list bool) (n : ℕ) (hn : n ≠ 0 ∨ bs.last'.get_or_else tt = tt) :
  (append_const bs).eval n = part.some (decode_nat (bs ++ encode_nat n)) :=
by { cases hn, rw [append_const_apply, computability.append_bits _ hn], rw [append_const_apply, computability.append_bits' _ hn], }

def to_bit : code := case one one zero
@[simp] lemma to_bit_apply (n : ℕ) : to_bit.eval n = part.some (if n = 0 then 0 else 1) :=
begin
  have := computability.encode_nat_nil_iff_zero n,
  simp only [to_bit, code.eval],
  rcases (encode_nat n) with _|_|_,
  all_goals { intro, simp * at *, },
end


def tail : code := snd ∘ (bit ff) ∘ (bit tt) ∘ (bit tt)
@[simp] lemma tail_apply_bit1 (n : ℕ) : tail.eval (bit1 n) = part.some n :=
by simp [tail, nat.bit, ← nat.mkpair'_one]
@[simp] lemma tail_apply_bit0 (n : ℕ) : tail.eval (bit0 n) = part.some n :=
begin
  cases n;
  simp [tail, nat.bit, nat.unpair', list.unpair, list.unpair', list.take_while, list.after],
end

/-- Slight hack, uses details of the encoding of `pair` -/
def cons_bit (f g : code) : code := (case (tail ∘ tail) (bit ff) zero) ∘ (pair (to_bit ∘ f) g)
@[simp] lemma cons_bit_apply (f g : code) (n : ℕ) :
  (cons_bit f g).eval n = f.eval n >>= (λ r, (g.eval n).map (if r = 0 then bit0 else bit1)) :=
begin
  simp only [cons_bit, code.eval],
  cases (f.eval n) with d₁ v₁, by_cases h₁ : d₁, swap, { simp [h₁], }, simp only [h₁, part.mk_some],
  cases (g.eval n) with d₂ v₂, by_cases h₂ : d₂, swap, { simp [h₂], }, simp only [h₂, part.mk_some],
  cases v₁ h₁,
  { simp [nat.mkpair'_zero, nat.bit], },
  { simp [nat.mkpair'_one, nat.bit], }
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

