import computability.turing_machine
import computability.partrec
import boolcodeable
import part

/-- If you fold a list using `bind` and you encounter `none` at any point, the result will be `none` -/
@[simp] lemma foldl_bind_part_none {α β : Type*} (f : α → β → part α) (ls : list β) :
  ls.foldl (λ (a : part α) (hd : β), a.bind (λ a', f a' hd)) part.none = part.none :=
by { induction ls with hd tl ih, { refl, }, simpa, }

section
parameter (ι : Type)

local attribute [reducible] bitstring

/-- The current implementation has all the "starting functions" that `code` starts out with
into `oracle`. The oracles have type `ι`.

The spec for `code` is basically the same as `to_partrec.code`

TODO: decide if this is a good design decision or if all the oracles
should just be moved into `code` explicitly. Maybe `code`'s with oracles can be created at a future date. -/
inductive code
| oracle : ι →  code
| pair : code → code → code
| comp : code → code → code
| case : code → code → code
| fix : code → code

parameter {ι}
/-- Given an implementation `impl` of the oracles, we can evaluate the `code`. -/
@[simp] def code.eval (impl : ι → bitstring → bitstring) : code → bitstring →. bitstring
| (code.oracle i) := λ v, pure (impl i v)
| (code.pair f g) := λ v, do x ← f.eval v, y ← g.eval v, return (boolcodeable.encode (x, y)) 
| (code.comp f g) := λ v, g.eval v >>= f.eval
| (code.case f g) := λ v, if v.head = ff then f.eval v.tail else g.eval v.tail
| (code.fix f) := pfun.fix $ λ v, (f.eval v).map $ λ v',
  if v'.head = ff then sum.inl v'.tail else sum.inr v'.tail

-- TODO: add code.eval_tree which evaluates without `impl` (or maybe a partial `impl`), and returns
-- a (possibly infinite) binary tree consisting of all the possible outputs based on the results of the oracle.

/-
Description of oracles:
  - `fst` -- decodes a tuple `(a, b)` and returns `a`
  - `snd` -- decodes a tuple `(a, b)` and returns `b`
  - `head` -- returns the first bit. Note that this does NOT return the first element of an encoded list. 
  - `tail` -- returns all but the first bit
  - `append` -- concatentates two bitstrings
  - `ff'` -- returns the constant `ff` bit
  - `tt'` -- returns the constant `tt'` bit
  - `isempty` -- returns `[ff]` or `[tt]` based on if the input is `0` bits long
  - `id` -- returns the bitstring unchanged
  - `add` -- adds two encodings of natural numbers
  - `sum` -- subtracts two encodings of natural numbers
  - `mul` -- multiplies two encodings of natural numbers 

Note that all of these are not necessary
For example, `fst`, `snd`, `append`, `ff'`, `tt'`, `isempty` should be enough, if we change the
implementation of `ff'` and `tt'` to cons instead of returns a constant bitstring.

In particular, the implementations could be something like (pseudocode):
  - `nil = fst (tt :: input)` (i.e. `fst ∘ tt'`)
  - `id = snd (tt :: input)`
  - `head = fst (ff :: tt :: input)`
  - `tail = snd (ff :: tt :: input)`

However, these depend on the implementation details of the encoding of tuples. I'm adding more here
just for convenience for now, and so that it's easier to change that encoding if need be,
but when we compile to TM's, we will want to remove some.
-/
inductive ocl
| fst | snd | head | tail | append | isempty | id
| ff' | tt'
| add | mul | sub


@[simp] def impl : ocl → bitstring → bitstring
| ocl.fst := λ x, (boolcodeable.decode_tuple x).1
| ocl.snd := λ x, (boolcodeable.decode_tuple x).2
| ocl.ff' := λ _, [ff]
| ocl.tt' := λ _, [tt]
| ocl.head := λ x, [x.head]
| ocl.tail := list.tail
| ocl.isempty := λ x, [x.empty]
| ocl.id := λ x, x
| ocl.append := λ x, function.uncurry list.append (boolcodeable.decode _ x).iget
| ocl.add := λ x, boolcodeable.encode (function.uncurry nat.add (boolcodeable.decode _ x).iget)
| ocl.mul := λ x, boolcodeable.encode (function.uncurry nat.mul (boolcodeable.decode _ x).iget)
| ocl.sub := λ x, boolcodeable.encode (function.uncurry nat.sub (boolcodeable.decode _ x).iget)

end

section
/-! Here, we define lots of misc. functions that will be useful, culminating with an implementation of
  `list.foldl`. Given that, we should be able to implement everything else useful. -/
open ocl code boolcodeable (encode decode encode_tuple decode_tuple)

local attribute [reducible] bitstring

-- TODO: choose better notation
local notation f `ᵒ`:10000 := oracle f
local notation `{` x `, ` y `}` := pair x y
infixr `∘`:90 := comp

-- Just testing some lemmas
def append' (f g : code ocl) : code ocl := appendᵒ ∘ {f, g}
@[simp] lemma append'_apply (f g : code ocl) (bs : bitstring) :
  (append' f g).eval impl bs = (do x ← f.eval impl bs, y ← g.eval impl bs, return (x ++ y)) :=
begin
  simp only [append', code.eval],
  -- TODO: extract to tactic (e.g. `assume_halts`)
  -- Also this uses LEM. I don't feel bad about it. But we really need a good
  -- tactic that helps break `part`'s into cases, because they are annoying to work with right now.
  cases (f.eval impl bs) with d₁ v₁, by_cases h₁ : d₁, swap, { simp [h₁], }, simp only [h₁, part.mk_some],
  cases (g.eval impl bs) with d₂ v₂, by_cases h₂ : d₂, swap, { simp [h₂], }, simp only [h₂, part.mk_some],
  simp, refl,
end

def nil : code ocl := tailᵒ ∘ ff'ᵒ
@[simp] lemma nil_apply (bs : bitstring) : nil.eval impl bs = part.some [] := by simp [nil]

def cons (f g : code ocl) : code ocl := appendᵒ ∘ {headᵒ ∘ f, g}
@[simp] lemma cons_apply (f g : code ocl) (bs : bitstring) :
  (cons f g).eval impl bs = (do x ← f.eval impl bs, y ← g.eval impl bs, return (x.head :: y)) :=
begin
  simp only [cons, code.eval],
  cases (f.eval impl bs) with d₁ v₁, by_cases h₁ : d₁, swap, { simp [h₁], }, simp only [h₁, part.mk_some],
  cases (g.eval impl bs) with d₂ v₂, by_cases h₂ : d₂, swap, { simp [h₂], }, simp only [h₂, part.mk_some],
  simp,
end

def snoc (f g : code ocl) : code ocl := appendᵒ ∘ {f, headᵒ ∘ g}
def const_op (b : bool) : code ocl := if b = ff then ff'ᵒ else tt'ᵒ
@[simp] lemma const_op_apply (b : bool) (bs : bitstring) :
  (const_op b).eval impl bs = part.some [b] :=
by cases b; simp [const_op]


def bool_op (fn : bool → bool → bool) : code ocl :=
(case 
  (case (const_op $ fn ff ff) (const_op $ fn ff tt))
  (case (const_op $ fn tt ff) (const_op $ fn tt tt)))

lemma bool_op_apply (fn : bool → bool → bool) (b₁ b₂ : bool) (bs : list bool) :
  (bool_op fn).eval impl (b₁ :: b₂ :: bs) = part.some [fn b₁ b₂] :=
by cases b₁; cases b₂; simp [bool_op]

def xor_code : code ocl := bool_op bxor

def code_ite (c f g : code ocl) : code ocl :=
  (case g f) ∘ (cons c idᵒ)

@[simp] lemma code_ite_apply (c f g : code ocl) (bs : bitstring) :
  (code_ite c f g).eval impl bs = (c.eval impl bs) >>= (λ r, if r.head = tt then f.eval impl bs else g.eval impl bs) :=
begin
  simp only [code_ite, code.eval, cons_apply],
  cases (c.eval impl bs) with d₁ v₁, by_cases h₁ : d₁, swap, { simp [h₁], }, simp only [h₁, part.mk_some],
  simp [← eq_ff_eq_not_eq_tt],
end

def is_list_empty : code ocl := isemptyᵒ
@[simp] lemma is_list_empty_apply {α : Type} [boolcodeable α] (ls : list α) :
  is_list_empty.eval impl (encode ls) = part.some [ls.empty] :=
by simp [is_list_empty, boolcodeable.list_encode_empty_iff]

def list_head : code ocl := fstᵒ
@[simp] lemma list_head_apply {α : Type} [boolcodeable α] (x : α) (xs : list α) :
  list_head.eval impl (encode $ x :: xs) = part.some (encode x) :=
by simp [list_head, boolcodeable.list_encode_def]

def list_tail : code ocl := sndᵒ
@[simp] lemma list_tail_apply {α : Type} [boolcodeable α] (x : α) (xs : list α) :
  list_tail.eval impl (encode $ x :: xs) = part.some (encode xs) :=
by simp [list_tail, boolcodeable.list_encode_def]

def list_foldl_aux (step : code ocl /- (acc, hd) → acc -/) : code ocl :=
let acc := fstᵒ,
    hd := list_head ∘ sndᵒ,
    tl := list_tail ∘ sndᵒ in
code_ite (is_list_empty ∘ sndᵒ)
  (append' ff'ᵒ acc) -- If it is empty, do not recurse further (append ff'ᵒ)
  (append' tt'ᵒ {step ∘ {acc, hd}, tl}) -- Otherwise, append tt'ᵒ and do one step

lemma list_foldl_aux_apply {α : Type} [boolcodeable α]
  (step : code ocl) (acc : bitstring) (ls : list α) :
  (list_foldl_aux step).eval impl (encode_tuple acc (encode ls)) = (ls.cases_on'
    (part.some $ acc)
    (λ hd tl, (step.eval impl $ encode_tuple acc (encode hd)).map (λ r, encode_tuple r (encode tl)))) 
    .map (λ r, (bnot ls.empty) :: r) :=
by cases ls; simp [list_foldl_aux, boolcodeable.encode_product_def]

def list_foldl (step : code ocl) : code ocl := fix (list_foldl_aux step)

lemma list_foldl_apply {α : Type} [boolcodeable α] (step : code ocl) (base : bitstring) (ls : list α) :
  (list_foldl step).eval impl (encode_tuple base $ encode ls) =
  ls.foldl (λ acc hd, acc >>= λ r, step.eval impl $ encode_tuple r (encode hd)) (part.some $ encode base) :=
begin
  induction ls with hd tl ih generalizing base,
  { simp [list_foldl, part.eq_some_iff], apply pfun.fix_stop, rw list_foldl_aux_apply, simp, },
  simp [list_foldl] at ⊢ ih,
  rw pfun.fix_iterate' _ ((step.eval impl $ encode_tuple base (encode hd)).map (λ r, encode_tuple r (encode tl))),
  { simp [ih], clear ih,
    cases (step.eval impl $ encode_tuple base (encode hd)) with d₁ v₁, by_cases h₁ : d₁, swap, { simp [h₁], }, simp only [h₁, part.mk_some],
    simp, },
  clear ih, simp [list_foldl_aux_apply],
  cases (step.eval impl $ encode_tuple base (encode hd)) with d₁ v₁, by_cases h₁ : d₁, swap, { simp [h₁], }, simp only [h₁, part.mk_some],
  simp,
end

lemma list_foldl_apply' {α β : Type} [boolcodeable α] [boolcodeable β] (step : α → β → α) {step_cd : code ocl} (base : α) (ls : list β)
  (hstep : ∀ (a : α) (b : β), step_cd.eval impl (encode (a, b)) = part.some (encode $ step a b)) :
  (list_foldl step_cd).eval impl (encode (base, ls)) = part.some (encode (ls.foldl step base)) :=
begin
  simp [boolcodeable.encode_product_def, list_foldl_apply],
  induction ls with hd tl ih generalizing base, { simp, }, 
  simp [← boolcodeable.encode_product_def, hstep, ih],
end

def list_cons : code ocl := idᵒ
@[simp] lemma list_cons_apply {α : Type} [boolcodeable α] (hd : α) (tl : list α) :
  list_cons.eval impl (encode (hd, tl)) = part.some (encode (hd :: tl)) := rfl

/-- TODO: let's make a prop `is_polynomial` which is true iff a function has *some implementation*
  that is polynomial-time. This is a lot easier to think about, since we don't constantly have to deal
  with encodings. Then, we can make a tactic like `continuity` for polynomial time functions.
  
  What we want to write here is
  `reverse = λ x : list α, x.foldl (λ acc hd, hd :: acc) []`
  and have lean automatically translate into the existence of something like this. -/
def reverse : code ocl := list_foldl (list_cons ∘ {sndᵒ, fstᵒ}) ∘ {nil, idᵒ}
lemma reverse_apply {α : Type} [boolcodeable α] (ls : list α) :
  reverse.eval impl (encode ls) = part.some (encode (ls.reverse)) :=
begin
  simp [reverse],
  have : encode (@list.nil bool, encode ls) = encode (@list.nil α, ls) := rfl, rw this, clear this,
  rw list_foldl_apply' (λ acc hd, hd :: acc),
  { congr, exact list.foldl_of_cons ls, },
  intros a b,
  simp [boolcodeable.encode_product_def],
  rw ← boolcodeable.encode_product_def,
  simp,
end

/- TODO: figure out why encoding/decoding nat's is somewhat slow -/
#eval decode ℕ ((list_foldl addᵒ).eval impl $ encode (0, [0, 1, 5, 100])).unwrap
end
