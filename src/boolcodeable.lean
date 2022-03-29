import computability.encoding
import lists
import tactic.linarith

/-! This file defines `canonical` encodings of various types into `list bool` (i.e. `bitstring`).
  The type itself is equivalent to `fin_encoding` with alphabet `bool`. However, the idea is
  that these encodings will be "canonical" in the sense that we are very careful with putting
  instances on them, and that all the encodings are fast (i.e. polynomial time, logarithmic space,
  maybe even better) to decode and encode. However, we do not put any such formal constraints.
  
  TODO: this duplicates a lot of code and ideas from `fin_encoding`, `primcodeable`, `encodeable`, etc. 
  How should we unify this? -/


section
universes u v

/-- A bitstring is a `list bool`, but this is an "internal representation" thing. Eventually,
  we should have enough abstraction that we rarely need to work with the underlying bits representing
  a type, and can instead simply work with the higher-level encodings
  (obviously, not in these initial files that build up the representations though).
  
  A file that does need to explicitly deal with the fact that `bitstring` data is a list of bools should
  mark `bitstring` as `reducible`
  
  TODO: decide if this is actually a good design choice -/
@[irreducible, derive [inhabited, has_to_string]]
def bitstring := list bool

local attribute [reducible] bitstring

def bitstring.sizeof : bitstring → ℕ := @list.length bool

@[priority 5000]
instance : has_sizeof bitstring := ⟨bitstring.sizeof⟩

/-- TODO: remove (?) -/
def bitstring.mk (bs : list bool) : bitstring := bs

/-- A type is `boolcodeable` if it is encodable into `bitstring` -/
class boolcodeable (α : Type*) :=
(encode : α → bitstring)
(decode [] : bitstring → option α)
(decode_encode : ∀ x, decode (encode x) = some x)

attribute [simp] boolcodeable.decode_encode

namespace boolcodeable

def to_fin_encoding (α : Type) [boolcodeable α] : computability.fin_encoding α := 
{ Γ := bool,
  encode := boolcodeable.encode,
  decode := boolcodeable.decode α,
  decode_encode := boolcodeable.decode_encode,
  Γ_fin := infer_instance }

/-- A boolean value `b` is encoded as `[b]` -/
instance : boolcodeable bool := 
{ encode := λ x, [x],
  decode := λ x, x.head',
  decode_encode := by simp }

/-- A bitstring is encoded with the identity. Note that `list bool` is encoded differently
  (it inherits the generic `list α` encoding) -/
@[priority 5000]
instance : boolcodeable bitstring :=
{ encode := id,
  decode := some,
  decode_encode := λ x, rfl }

@[simp] lemma encode_bitstring (ls : bitstring) : encode ls = ls := rfl
@[simp] lemma decode_bitstring (ls : bitstring) : (decode bitstring ls) = some ls := rfl

instance : boolcodeable pempty :=
{ encode := pempty.elim,
  decode := λ _, none,
  decode_encode := λ x, x.elim }

instance : boolcodeable punit :=
{ encode := λ _, [],
  decode := λ _, some punit.star,
  decode_encode := by simp }

/-- A natural number `n : ℕ` is encoded using its binary representation -/
instance : boolcodeable ℕ := 
{ encode := computability.encode_nat,
  decode := λ n, some (computability.decode_nat n),
  decode_encode := λ n, congr_arg _ (computability.decode_encode_nat n) }

/-- A tuple `(a, b)` is encoded as follows: we first write `a.length` `ff`'s, followed by `tt`; 
  this keeps track of the length of `a`. Then we simply concatenate `a` with `b`.
  Since `(a, b).sizeof = 2*a.sizeof + b + 1`, the tuple can be nested only in the second argument
  to retain an efficient (i.e. linear) representation. -/
def encode_tuple (a b : bitstring) : bitstring := 
(list.repeat ff a.length) ++ (tt :: (a ++ b))

lemma encode_tuple_sizeof (a b : bitstring) : (encode_tuple a b).sizeof = 2*a.sizeof + b.sizeof + 1 :=
by { simp [encode_tuple, bitstring.sizeof], ring, }

def decode_tuple (x : bitstring) : bitstring × bitstring :=
(x.after (=tt)).split_at (x.take_while (=ff)).length

@[simp] lemma decode_encode_tuple (a b : bitstring) :
  decode_tuple (encode_tuple a b) = (a, b) :=
begin
  simp only [decode_tuple],
  have h₁ : (encode_tuple a b).after (=tt) = a ++ b,
  { apply list.after_spec, { simp [list.mem_repeat], }, { refl, }, },
  have h₂ : ((encode_tuple a b).take_while (=ff)).length = a.length,
  { erw list.take_while_spec, { apply list.length_repeat, }, { simp [list.mem_repeat], }, trivial, },
  simp [h₁, h₂],
end

instance {α β : Type} [boolcodeable α] [boolcodeable β] : boolcodeable (α × β) := 
{ encode := λ x, encode_tuple (encode x.1) (encode x.2),
  decode := λ x, (do
    a ← decode α (decode_tuple x).1,
    b ← decode β (decode_tuple x).2,
    return (a, b)
  ),
  decode_encode := λ x, by { simp, refl, } }

lemma encode_product_def {α β : Type} [boolcodeable α] [boolcodeable β] (a : α) (b : β) :
  encode (a, b) = encode_tuple (encode a) (encode b) := rfl

/-- The first item of a tuple has smaller size than the tuple; useful for well-founded recursion -/
lemma decode_fst_length_lt (b : bitstring) (hb : 0 < b.length) :
  (decode_tuple b).1.sizeof < b.sizeof :=
begin
  simp only [decode_tuple, list.split_at_eq_take_drop],
  generalize : (b.take_while (=ff)).length = l,
  exact calc ((b.after (=tt)).take l).length
      ≤ (b.after (=tt)).length : list.length_le_of_sublist (list.take_sublist _ _)
 ...  < b.length : by rwa list.after_length_lt,
end

/-- The second item of a tuple has smaller size than the tuple; useful for well-founded recursion -/
lemma decode_snd_length_lt (b : bitstring) (hb : 0 < b.length) :
  (decode_tuple b).2.sizeof < b.sizeof :=
begin
  simp only [decode_tuple, list.split_at_eq_take_drop],
  generalize : (b.take_while (=ff)).length = l,
  exact calc ((b.after (=tt)).drop l).length
      ≤ (b.after (=tt)).length : list.length_le_of_sublist (list.drop_sublist _ _)
 ...  < b.length : by rwa list.after_length_lt,
end

/-- The sum type `α ⊕ β` is encoded by using the first bit to indicate which of `α` or `β` it is -/
instance {α β : Type} [boolcodeable α] [boolcodeable β] : boolcodeable (α ⊕ β) := 
{ encode := λ x, x.elim (λ a, ff :: encode a) (λ b, tt :: encode b),
  decode := λ x, if x.head = ff then (decode α x.tail).map sum.inl else (decode β x.tail).map sum.inr,
  decode_encode := λ x, by cases x; simp, }

/-- A list is encoded as nested tuples i.e. `[a₁, a₂, a₃, ...]` is encoded as
  `(a₁, (a₂, (a₃, ...)))`. This has only a constant-factor overhead (at most 3 assuming the items' encodings are nonempty),
  because the tuple encoding is efficient in the second argument.
  More precisely, the encoding of a list `L` whose items have a sum of sizes of `S` has total size `2S + len(L)`. -/
def decode_bitstring_list {α : Type} [boolcodeable α] : bitstring → option (list α)
| [] := some []
| ls@(x :: xs) :=
    let b := decode_tuple ls in
    have wf : b.2.length < ls.length := decode_snd_length_lt (x :: xs) (by simp),
  (do
    a ← decode α b.1,
    b' ← decode_bitstring_list b.2,
    return (a :: b'))

lemma decode_bitstring_list_def {α : Type} [boolcodeable α] (ls : bitstring) (hls : 0 < ls.length) :
  decode_bitstring_list ls = (do a : α ← decode α (decode_tuple ls).1, b ← decode_bitstring_list (decode_tuple ls).2, return (a :: b)) :=
by { cases ls, { exfalso, simpa using hls, }, simp only [decode_bitstring_list], }

lemma decode_bitstring_list_spec {α : Type} [boolcodeable α] (x : α) (xs : bitstring) :
  (decode_bitstring_list (encode_tuple (encode x) xs) : option (list α)) = (decode_bitstring_list xs) >>= (λ ls : list α, return $ x :: ls) :=
by { rw decode_bitstring_list_def, { simp, }, simp [encode_tuple, ← add_assoc], }

instance {α : Type} [boolcodeable α] : boolcodeable (list α) :=
{ encode := λ x, x.foldr (λ hd tl, encode_tuple (encode hd) tl) [],
  decode := decode_bitstring_list,
  decode_encode := λ x,
  by { induction x with _ _ ih, { simp [decode_bitstring_list], }, simp [decode_bitstring_list_spec, ih], refl, } }

lemma list_encode_def {α : Type} [boolcodeable α] (x : α) (xs : list α) :
  encode (x :: xs) = encode_tuple (encode x) (encode xs) := rfl

lemma list_encode_empty_iff {α : Type} [boolcodeable α] (ls : list α) :
  (encode ls).empty = ls.empty :=
begin
  cases ls with hd tl, { refl, }, 
  have : 0 < (encode $ hd :: tl).length := by simp [encode, encode_tuple, ← add_assoc],
  simp [list.empty_ff_iff_neq_nil, ← list.length_eq_zero], linarith,
end 

/-- Transport an encoding along an equivalence -/
def of_equiv {α β : Type} [boolcodeable α] (eqv : α ≃ β) : boolcodeable β :=
{ encode := λ x, encode (eqv.inv_fun x),
  decode := λ x, (decode α x).map eqv,
  decode_encode := by simp }

instance {α : Type} [boolcodeable α] : boolcodeable (option α) :=
of_equiv (equiv.option_equiv_sum_punit α).symm

end boolcodeable

end