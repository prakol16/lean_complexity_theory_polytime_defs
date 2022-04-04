import polytime
open computability (encode_nat decode_nat)


@[simp] def encode_option_nat : option ℕ → ℕ
| none := 0
| (some n) := bit1 n

@[simp] def decode_option_nat : ℕ → option ℕ
| 0 := none
| n := some (decode_nat (encode_nat n).tail)

@[simp] lemma decode_option_nat_bit1 (n : ℕ) : decode_option_nat (bit1 n) = some n :=
by { cases e : (bit1 n), { simp at e, contradiction, },
  simp only [decode_option_nat, nat.succ_ne_zero, not_false_iff], rw ← e, simp, }

@[simp] lemma decode_encode_option_nat (n : option ℕ) : decode_option_nat (encode_option_nat n) = n :=
by { cases n, { refl, }, simp, }

class polycodable (α : Type*) :=
(encode : α → ℕ)
(decode [] : ℕ → option α)
(decode_encode : ∀ x, decode (encode x) = some x)
(poly [] : ∃ c : code, polytime c ∧ ∀ x, c.eval x =  part.some (encode_option_nat ((decode x).map encode)))

attribute [simp] polycodable.decode_encode

open polycodable

instance : polycodable ℕ := 
{ encode := id,
  decode := some,
  decode_encode := λ n, rfl,
  poly := ⟨code.bit tt, polytime_bit _, λ n, by simp [nat.bit]⟩ }

@[simp] lemma encode_nat_id (n : ℕ) : encode n = n := rfl
@[simp] lemma decode_nat_id (n : ℕ) : decode ℕ n = some n := rfl

def decode_option_code (f : code) : code :=
code.case ((code.case zero (code.bit tt) zero).comp f) ((code.case zero (code.bit tt) zero).comp f) zero

lemma polytime_decode_option_code {f : code} (hf : polytime f) : polytime (decode_option_code f) :=
begin
  -- TODO: This obviously needs to be a tactic
  apply polytime_case,
  { apply polytime_comp, { apply polytime_case, apply polytime_zero, apply polytime_bit, apply polytime_zero, }, exact hf, },
  apply polytime_comp, apply polytime_case, apply polytime_zero, apply polytime_bit, apply polytime_zero, exact hf, apply polytime_zero,
end

instance {α : Type} [polycodable α] : polycodable (option α) :=
{ encode := λ x, encode_option_nat (x.map encode),
  decode := λ x, some ((decode_option_nat x) >>= decode α),
  decode_encode := λ x, by cases x; simp,
  poly :=
  begin
    obtain ⟨c, pc, ec⟩ := polycodable.poly α,
    use (code.bit tt).comp (decode_option_code c), split,
    { apply polytime_comp (polytime_bit _), exact polytime_decode_option_code pc, },
    intro x, simp only [decode_option_code],
    rcases e : (encode_nat x) with _|_|_,
    { rw computability.encode_nat_nil_iff_zero at e, subst e, simp [nat.bit], },
    { have : x ≠ 0 := λ h, by { subst h, simpa using e, },
      simp [e, this, nat.bit, ec],
      cases decode α (decode_nat this_tl); simp, },
    { have : x ≠ 0 := λ h, by { subst h, simpa using e, },
      simp [e, this, nat.bit, ec],
      cases decode α (decode_nat this_tl); simp, },
  end  }

def is_polytime {α β : Type} [polycodable α] [polycodable β] (f : α → β) : Prop :=
∃ c : code, polytime c ∧ ∀ x : ℕ, c.eval x = part.some (encode ((decode α x).map f))

@[simps] def polycodable.mk' {α : Type} (encode : α → ℕ) (decode : ℕ → option α) (decode_encode : ∀ x, decode (encode x) = some x)
  (poly : is_polytime (λ x, (decode x).map encode)) : polycodable α := 
{ encode := encode,
  decode := decode,
  decode_encode := decode_encode,
  poly :=
  begin
    obtain ⟨c, pc, hc⟩ := poly,
    use tail.comp c,
    split, { exact polytime_comp polytime_tail pc, },
    intro x, specialize hc x,
    simp [hc, polycodable.encode],
  end }

variables {α β γ : Type} [polycodable α] [polycodable β] [polycodable γ]

lemma encode_decode_is_polytime : is_polytime (λ x : ℕ, (decode α x).map encode) :=
begin
  obtain ⟨c, pc, hc⟩ := poly α,
  use (code.bit tt).comp c,
  split, { exact polytime_comp (polytime_bit _) pc, },
  intro x, specialize hc x,
  simp [hc, polycodable.encode, nat.bit],
end

lemma is_polytime_iff (f : α → β) :
  is_polytime f ↔ ∃ c : code, polytime c ∧ ∀ x : α, c.eval (encode x) = part.some (encode (f x)) :=
begin
  split,
  { rintro ⟨c, pc, hc⟩,
    use tail.comp c,
    split, { exact polytime_comp polytime_tail pc,},
    intro x, specialize hc (encode x),
    simp [hc, polycodable.encode], },
  rintro ⟨c, pc, hc⟩,
  obtain ⟨de, pde, hde⟩ := polycodable.poly α,
  use (code.case zero ((code.bit tt).comp c) zero).comp de,
  split, { exact polytime_comp (polytime_case polytime_zero (polytime_comp (polytime_bit _) pc) polytime_zero) pde, },
  intro x, specialize hde x,
  cases decode α x,
  { simp [hde], refl, }, simp [hde, hc], refl,
end

lemma is_polytime_comp {f : β → γ} {g : α → β} (hf : is_polytime f) (hg : is_polytime g) : is_polytime (f ∘ g) :=
begin
  simp only [is_polytime_iff] at *,
  rcases hf with ⟨fc, pfc, hfc⟩, rcases hg with ⟨gc, pgc, hgc⟩,
  use [fc.comp gc, polytime_comp pfc pgc], intro, simp [hfc, hgc],
end

lemma is_polytime_encode : is_polytime (@encode α _) :=
by { rw is_polytime_iff, use [code.id, polytime_id], intro, simp, }

lemma is_polytime_decode : is_polytime (decode α) :=
by { rw is_polytime_iff, exact poly α, }

lemma is_polytime_option_elim (n : β) {s : α → β} (hs : is_polytime s) : is_polytime (λ x : option α, x.elim n s) :=
begin
  simp only [is_polytime_iff] at *,
  rcases hs with ⟨sc, psc, hsc⟩,
  use code.case zero sc (code.const (encode n)), split, { exact polytime_case polytime_zero psc (polytime_const _), },
  intro x, cases x; simp [encode, hsc],
end

lemma is_polytime_some : is_polytime (@some α) :=
by { rw is_polytime_iff, use code.bit tt, split, { exact polytime_bit _, }, simp [encode, nat.bit], }

lemma is_polytime_option_map {f : α → β} (hf : is_polytime f) : is_polytime (λ x : option α, x.map f) :=
begin
  convert_to is_polytime (λ x : option α, x.elim none (λ x', some (f x'))),
  { ext x : 1, cases x; simp, },
  exact is_polytime_option_elim _ (is_polytime_comp is_polytime_some hf),
end

lemma is_polytime_option_bind {f : α → option β} (hf : is_polytime f) : is_polytime (λ x : option α, x.bind f) :=
begin
  convert_to is_polytime (λ x : option α, x.elim none (λ x', f x')),
  { ext x : 1, cases x; simp, },
  apply is_polytime_option_elim _ hf,
end

section prod

instance {α β : Type} [polycodable α] [polycodable β] : polycodable (α × β) :=
polycodable.mk'
  (λ x, nat.mkpair' (encode x.1) (encode x.2))
  (λ x, (decode α (nat.unpair' x).1) >>= (λ x₁, (decode β (nat.unpair' x).2).map $ λ x₂, (x₁, x₂)))
  (λ x, by simp [return, pure])
begin
  convert_to is_polytime
    (λ x, (decode α (nat.unpair' x).1) >>=
    (λ x₁, (decode β (nat.unpair' x).2).map (
    λ x₂, nat.mkpair' (encode x₁) (encode x₂)))),
  { ext x : 1, cases decode α (nat.unpair' x).1; simp, },
  
end


end prod

-- instance {α β : Type*} [polycodable α] [polycodable β] : polycodable (α × β) :=
-- { encode := λ x, nat.mkpair' (encode x.1) (encode x.2),
--   decode := λ x, decode α (nat.unpair' x).1 >>= (λ x₁, decode β (nat.unpair' x).2 >>= λ x₂, return (x₁, x₂)),
--   decode_encode := _,
--   poly := _ }