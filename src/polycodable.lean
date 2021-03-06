import polytime
open num (to_bits of_bits)


@[simp] def encode_option_nat : option ℕ → ℕ
| none := 0
| (some n) := bit1 n

@[simp] def decode_option_nat : ℕ → option ℕ
| 0 := none
| n := some (of_bits (to_bits n).tail)

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
    rcases e : (to_bits x) with _|_|_,
    { simp only [num.to_bits_nil_iff, nat.cast_eq_zero] at e, subst e, simp [nat.bit], },
    all_goals { have : x ≠ 0 := λ h, by { subst h, simpa using e, },
      simp [e, this, nat.bit, ec],
      cases decode α (of_bits this_tl); simp, },
  end  }

def is_polytime {α β : Type} [polycodable α] [polycodable β] (f : α → β) : Prop :=
∃ c : code, polytime c ∧ ∀ x, c.eval (encode x) = part.some (encode $ f x)

@[simps] def polycodable.mk' {α : Type} (encode : α → ℕ) (decode : ℕ → option α) (decode_encode : ∀ x, decode (encode x) = some x)
  (poly : is_polytime (λ x, (decode x).map encode)) : polycodable α := 
{ encode := encode,
  decode := decode,
  decode_encode := decode_encode,
  poly := by simpa [is_polytime, polycodable.encode] using poly }

variables {α β γ : Type} [polycodable α] [polycodable β] [polycodable γ]

lemma encode_decode_is_polytime (α : Type) [polycodable α] : is_polytime (λ x : ℕ, (decode α x).map encode) :=
by simpa [is_polytime, polycodable.encode] using poly α

lemma is_polytime_iff (f : α → β) :
  is_polytime f ↔ ∃ c : code, polytime c ∧ ∀ x : ℕ, c.eval x = part.some (encode $ (decode α x).map f) :=
begin
  split, swap,
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

lemma is_polytime_comp {f : β → γ} {g : α → β} : is_polytime f → is_polytime g → is_polytime (f ∘ g)
| ⟨fc, fp, hf⟩ ⟨gc, gp, hg⟩ := ⟨fc.comp gc, polytime_comp fp gp, λ x, by simp [hf, hg]⟩

lemma is_polytime_encode (α : Type) [polycodable α] : is_polytime (@encode α _) :=
⟨code.id, polytime_id, λ x, by simp⟩

lemma is_polytime_decode (α : Type) [polycodable α] : is_polytime (decode α) := poly α

lemma is_polytime_const (β : Type) [polycodable β] (x : α) : is_polytime (λ _ : β, x) :=
⟨code.const (encode x), polytime_const _, λ x, by simp⟩ 

section equiv

def polycodable_of_equiv {β : Type} (eqv : α ≃ β) : polycodable β :=
polycodable.mk'
  (λ b, (polycodable.encode (eqv.symm b)))
  (λ n, (polycodable.decode α n).map eqv)
  (λ b, by simp)
  (by { convert encode_decode_is_polytime α, ext b : 1, cases decode α b; simp, })

lemma is_polytime_of_equiv_symm {β : Type} (eqv : α ≃ β)
  {f : α → γ} (hf : is_polytime f) : @is_polytime β γ (polycodable_of_equiv eqv) _ (f ∘ eqv.symm) :=
by { rcases hf with ⟨c, pc, hc⟩, use c, split, { assumption, }, intro x, exact hc (eqv.symm x), }

lemma is_polytime_of_equiv {β : Type} (eqv : α ≃ β)
  {f : γ → α} (hf : is_polytime f) : @is_polytime γ β _ (polycodable_of_equiv eqv) (eqv ∘ f) :=
by { rcases hf with ⟨c, pc, hc⟩, use c, split, { assumption, }, intro x, rw hc x, simp [encode], }

end equiv

section bool

instance : polycodable bool :=
polycodable.mk'
(λ b, cond b 1 0) (λ n, some (if n = 0 then ff else tt)) (λ x, by cases x; simp)
⟨(code.bit tt).comp to_bit, polytime_comp (polytime_bit _) polytime_to_bit, λ x, by cases x; simp; refl⟩

lemma is_polytime_cond {c : α → bool} {f g : α → β} : is_polytime c → is_polytime f → is_polytime g → is_polytime (λ x, cond (c x) (f x) (g x))
| ⟨cc, cp, hc⟩ ⟨fc, fp, hf⟩ ⟨gc, gp, hg⟩ :=
⟨code.ite cc gc fc, (polytime_ite cp gp fp), λ x, by cases e : c x; simp [hc, hf, hg, e]⟩

lemma is_polytime_is_some (α : Type) [polycodable α] : is_polytime (@option.is_some α) :=
⟨to_bit, polytime_to_bit, λ x, by cases x; simp [polycodable.encode]⟩

end bool

section prod

instance {α β : Type} [polycodable α] [polycodable β] : polycodable (α × β) :=
polycodable.mk'
  (λ x, nat.mkpair' (encode x.1) (encode x.2))
  (λ x, (decode α (nat.unpair' x).1) >>= (λ x₁, (decode β (nat.unpair' x).2).map $ λ x₂, (x₁, x₂)))
  (λ x, by simp [return, pure])
begin
  obtain ⟨somec₁, somep₁, hsome₁⟩ := is_polytime_is_some α,
  obtain ⟨somec₂, somep₂, hsome₂⟩ := is_polytime_is_some β,
  obtain ⟨d₁, dp₁, hd₁⟩ := is_polytime_decode α,
  obtain ⟨d₂, dp₂, hd₂⟩ := is_polytime_decode β,
  simp only [encode_nat_id] at hd₁ hd₂,
  obtain ⟨e₁, ep₁, he₁⟩ := is_polytime_encode α,
  obtain ⟨e₂, ep₂, he₂⟩ := is_polytime_encode β,
  use (code.ite (somec₁.comp $ d₁.comp code.fst) zero $
      code.ite (somec₂.comp $ d₂.comp code.snd) zero $ 
      (code.bit tt).comp (code.pair (tail.comp $ d₁.comp code.fst) (tail.comp $ d₂.comp code.snd))),
  split,
  { have P₁ : polytime (d₁.comp code.fst) := polytime_comp dp₁ polytime_fst,
    have P₂ : polytime (d₂.comp code.snd) := polytime_comp dp₂ polytime_snd,
    exact (
      polytime_ite (polytime_comp somep₁ P₁) polytime_zero $
      polytime_ite (polytime_comp somep₂ P₂) polytime_zero $
      (polytime_comp (polytime_bit _) (polytime_pair (polytime_comp polytime_tail P₁) (polytime_comp polytime_tail P₂)))), },
  intro x,
  cases H₁ : decode α (nat.unpair' x).1, { simp [H₁, hd₁, hsome₁], refl, },
  cases H₂ : decode β (nat.unpair' x).2, { simp [H₁, hd₁, hsome₁, H₂, hd₂, hsome₂], refl, },
  simp [H₁, hd₁, hsome₁, H₂, hd₂, hsome₂], simp [polycodable.encode, nat.bit],
end

lemma polytime_prod_fst (α β : Type) [polycodable α] [polycodable β] : is_polytime (@prod.fst α β) :=
⟨code.fst, polytime_fst, λ x, by simp [polycodable.encode]⟩

lemma polytime_prod_snd (α β : Type) [polycodable α] [polycodable β] : is_polytime (@prod.snd α β) :=
⟨code.snd, polytime_snd, λ x, by simp [polycodable.encode]⟩

lemma prod_encode_def (x : α × β) : (encode x.1).mkpair' (encode x.2) = encode x := rfl

lemma is_polytime_pair {f : α → β} {g : α → γ} : is_polytime f → is_polytime g → is_polytime (λ x, (f x, g x))
| ⟨fc, fp, hf⟩ ⟨gc, gp, hg⟩ := ⟨code.pair fc gc, polytime_pair fp gp, λ x, by simp [hf, hg]⟩

def is_polytime₂ (f : α → β → γ) : Prop := is_polytime (function.uncurry f)

lemma is_polytime₂_comp {δ : Type} [polycodable δ] {f : α → β → γ} {g : δ → α} {h : δ → β} 
  (hf : is_polytime₂ f) (hg : is_polytime g) (hh : is_polytime h) :
  is_polytime (λ x, f (g x) (h x)) :=
is_polytime_comp hf (is_polytime_pair hg hh)

@[simp] lemma function.uncurry_prod_mk (α β : Type*) : function.uncurry (@prod.mk α β) = id :=
by ext x; cases x; simp

lemma is_polytime₂_ignore_fst {f : α → β} (h : is_polytime f) : is_polytime₂ (λ x : γ, f) :=
by { have := is_polytime_comp h (polytime_prod_snd _ _), exact this, }

lemma is_polytime_prod_mk : is_polytime₂ (@prod.mk α β) := ⟨code.id, polytime_id, λ x, by simp⟩

end prod

section bool

lemma is_polytime_band : is_polytime₂ band :=
begin
  convert_to is_polytime₂ (λ b₁ b₂, cond b₁ b₂ ff),
  { ext b₁ b₂, cases b₁; cases b₂; refl, },
  apply is_polytime_cond,
  exacts [polytime_prod_fst _ _, polytime_prod_snd _ _, is_polytime_const _ _],
end

lemma is_polytime_bor : is_polytime₂ bor :=
begin
  convert_to is_polytime₂ (λ b₁ b₂, cond b₁ tt b₂), { ext b₁ b₂, cases b₁; cases b₂; refl, },
  apply is_polytime_cond,
  exacts [polytime_prod_fst _ _,  is_polytime_const _ _, polytime_prod_snd _ _],
end

end bool

section option

lemma is_polytime_elim {g : α → option β} {f : α → β → γ} {df : α → γ} :
  is_polytime g → is_polytime₂ f → is_polytime df → is_polytime (λ x, (g x).elim (df x) (f x))
| ⟨gc, gp, hg⟩ ⟨fc, fp, hf⟩ ⟨dfc, dfp, hdf⟩ :=
⟨code.ite gc dfc (fc.comp $ code.pair code.id (tail.comp gc)), 
  polytime_ite gp dfp (polytime_comp fp $ polytime_pair polytime_id (polytime_comp polytime_tail gp)),
  λ x, 
begin
  simp only [← prod_encode_def] at hf,
  cases e : g x with v, { simp [hg, hdf, e, encode], }, { simp [hg, hdf, e, encode, hf (x, v)], }
end⟩

lemma is_polytime_some : is_polytime (@some α) :=
⟨code.bit tt, polytime_bit _, by simp [encode, nat.bit]⟩

lemma is_polytime_of_is_polytime_some {f : α → β} (hf : is_polytime (some ∘ f)) : is_polytime f :=
by { rcases hf with ⟨c, pc, hc⟩, use [tail.comp c, polytime_comp polytime_tail pc], intro x, simp [hc x, encode], }

lemma is_polytime_bind_option {f : α → option β} {g : α → β → option γ} (hf : is_polytime f) (hg : is_polytime₂ g) :
  is_polytime (λ x, (f x).bind (g x)) :=
begin
  convert_to is_polytime (λ x, (f x).elim none (g x)), { ext x : 1, cases f x; simp, },
  exact is_polytime_elim hf hg (is_polytime_const _ none),
end

lemma is_polytime_map_option {f : α → option β} {g : α → β → γ} (hf : is_polytime f) (hg : is_polytime₂ g) :
  is_polytime (λ x, (f x).map (g x)) :=
begin
  change is_polytime (λ x, (f x).bind (some ∘ (g x))), -- turns out, defeq !
  exact is_polytime_bind_option hf (is_polytime_comp is_polytime_some hg),
end

end option

section embedding

def polycodable_of_embedding {β : Type} (e : β → α) (f : α → option β)
  (h : ∀ x, f (e x) = some x) (poly : is_polytime (λ x, (f x).map e)) : polycodable β :=
polycodable.mk' 
(λ x, encode (e x))
(λ n, decode α n >>= f)
(λ x, by simp [h])
begin
  convert_to is_polytime (λ n, decode α n >>= (λ x, ((f x).map e).map encode)),
  { ext n : 1, cases decode α n; simp, },
  apply is_polytime_bind_option, { exact is_polytime_decode _, },
  apply is_polytime₂_ignore_fst, apply is_polytime_map_option poly,
  apply is_polytime₂_ignore_fst, apply is_polytime_encode,
end

lemma is_polytime_of_embedding_inclusion {β : Type} {e : β → α} {f : α → option β}
  {h : ∀ x, f (e x) = some x} {poly : is_polytime (λ x, (f x).map e)} : 
  by { haveI := polycodable_of_embedding e f h poly, exact (is_polytime e), } :=
by { use [code.id, polytime_id], intro, simp, }

lemma is_polytime_of_embedding_inverse {β : Type} {e : β → α} {f : α → option β}
  {h : ∀ x, f (e x) = some x} {poly : is_polytime (λ x, (f x).map e)} :
  by { haveI := polycodable_of_embedding e f h poly, exact (is_polytime f), } :=
by { rcases poly with ⟨c, pc, hc⟩, use [c, pc], intro x, simp [hc x, encode], refl, }

end embedding

section subtype

def is_polytime_pred (p : α → Prop) [decidable_pred p] : Prop :=
is_polytime (λ x : α, (p x : bool))

lemma is_polytime_ite {p : α → Prop} [decidable_pred p] (hp : is_polytime_pred p) {f g : α → β}
  (hf : is_polytime f) (hg : is_polytime g) : is_polytime (λ x, if p x then f x else g x) :=
begin
  convert_to is_polytime (λ x, cond (p x) (f x) (g x)), { ext x, split_ifs with h; simp [h], },
  apply is_polytime_cond; assumption,
end

def polycodable_subtype {p : α → Prop} [decidable_pred p] (hp : is_polytime_pred p) :
  polycodable {x // p x} :=
polycodable_of_embedding
  (λ x, (x : α))
  (λ x, if h : p x then some ⟨x, h⟩ else none) 
  (λ x, by simpa [imp_false] using subtype.prop x)
begin
  convert_to is_polytime (λ x, if p x then some x else none), { ext x : 1, split_ifs; simp, },
  exact is_polytime_ite hp is_polytime_some (is_polytime_const _ _),
end

end subtype

section sigma

private def sum_as_tuple : α ⊕ β → bool × ℕ
| (sum.inl a) := (ff, encode a)
| (sum.inr b) := (tt, encode b)

private def tuple_as_sum (n : bool × ℕ) : option (α ⊕ β) :=
cond n.1 ((decode β n.2).map sum.inr) ((decode α n.2).map sum.inl)

instance : polycodable (α ⊕ β) :=
polycodable_of_embedding sum_as_tuple tuple_as_sum
  (λ x, by cases x; simp [sum_as_tuple, tuple_as_sum])
begin
  convert_to is_polytime (λ n : bool × ℕ, cond n.1 ((decode β n.2).map (λ x, (tt, encode x)))
    ((decode α n.2).map (λ x, (ff, encode x)))),
  { ext n : 1, cases n with b v, cases b; simp [tuple_as_sum]; congr, },
  apply is_polytime_cond (polytime_prod_fst _ _),
  change is_polytime₂ (λ (b : bool) (n : ℕ), (decode β n).map (λ x, (tt, encode x))),
  { apply is_polytime₂_ignore_fst, apply is_polytime_map_option, apply is_polytime_decode, 
    apply is_polytime₂_ignore_fst, apply is_polytime₂_comp is_polytime_prod_mk, apply is_polytime_const,
    apply is_polytime_encode, },
  change is_polytime₂ (λ (b : bool) (n : ℕ), (decode α n).map (λ x, (ff, encode x))),
  { apply is_polytime₂_ignore_fst, apply is_polytime_map_option, apply is_polytime_decode, 
    apply is_polytime₂_ignore_fst, apply is_polytime₂_comp is_polytime_prod_mk, apply is_polytime_const,
    apply is_polytime_encode, },
end

private lemma is_polytime_sum_as_tuple : is_polytime (@sum_as_tuple α β _ _) := is_polytime_of_embedding_inclusion
private lemma is_polytime_tuple_as_sum : is_polytime (@tuple_as_sum α β _ _) := is_polytime_of_embedding_inverse

lemma is_polytime_sum_inl : is_polytime (@sum.inl α β) :=
begin
  apply is_polytime_of_is_polytime_some,
  convert_to is_polytime (λ a : α, (tuple_as_sum (ff, encode a) : option (α ⊕ β)) ),
  { ext a : 1, simp [tuple_as_sum], },
  apply is_polytime_comp is_polytime_tuple_as_sum,
  apply is_polytime₂_comp is_polytime_prod_mk, { apply is_polytime_const, }, apply is_polytime_encode,
end

lemma is_polytime_sum_inr : is_polytime (@sum.inr α β) :=
begin
  apply is_polytime_of_is_polytime_some,
  convert_to is_polytime (λ b : β, (tuple_as_sum (tt, encode b) : option (α ⊕ β)) ),
  { ext b : 1, simp [tuple_as_sum], },
  apply is_polytime_comp is_polytime_tuple_as_sum,
  apply is_polytime₂_comp is_polytime_prod_mk, { apply is_polytime_const, }, apply is_polytime_encode,
end

lemma is_polytime_sum_elim {δ : Type} [polycodable δ] {f : δ → α → γ} (g : δ → β → γ) {h : δ → α ⊕ β } 
  (hf : is_polytime₂ f) (hg : is_polytime₂ g) (hh : is_polytime h) :
  is_polytime (λ x, (h x).elim (f x) (g x)) :=
begin
  apply is_polytime_of_is_polytime_some,
  convert_to is_polytime (λ x : δ, cond (sum_as_tuple $ h x).1 ((decode β $ (sum_as_tuple $ h x).2).map (g x)) 
    ((decode α $ (sum_as_tuple $ h x).2).map (f x))),
  { ext x : 1, simp only [function.comp_app], cases h x; simp [sum_as_tuple], },
  apply is_polytime_cond, { apply is_polytime_comp (polytime_prod_fst _ _), apply is_polytime_comp is_polytime_sum_as_tuple hh, },
  { apply is_polytime_map_option, apply is_polytime_comp (is_polytime_decode _), apply is_polytime_comp (polytime_prod_snd _ _),
    apply is_polytime_comp is_polytime_sum_as_tuple hh, exact hg, },
  apply is_polytime_map_option, apply is_polytime_comp (is_polytime_decode _), apply is_polytime_comp (polytime_prod_snd _ _),
  apply is_polytime_comp is_polytime_sum_as_tuple hh, exact hf,
end

end sigma

section list

def mklist (ls : list ℕ) : ℕ := ls.foldr nat.mkpair' 0
def unlist : ℕ → list ℕ
| 0 := []
| (nat.succ n) := have wf : (nat.unpair' n.succ).2 < n.succ := nat.unpair'_snd_lt n,
              (nat.unpair' n.succ).1 :: (unlist (nat.unpair' n.succ).2)

@[simp] lemma unlist_mklist (ls : list ℕ) : unlist (mklist ls) = ls :=
begin
  induction ls with h t ih, { simp [mklist, unlist], },
  simp only [mklist, list.foldr],
  cases e : nat.mkpair' h _, { cases nat.mkpair'_ne_zero _ _ e, },
  simp only [unlist], rw ← e,
  split; simp, exact ih,
end

section recursion



end recursion


end list