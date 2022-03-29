import data.part
import data.pfun

/-! Random lemmas, some may already be in mathlib -/


namespace part


@[simp] lemma mk_none {α : Type*} {dom : Prop} (v : dom → α) (h : ¬dom) :
  mk dom v = none := eq_none_iff'.mpr h

@[simp] lemma mk_some {α : Type*} {dom : Prop} (v : dom → α) (h : dom) :
  mk dom v = some (v h) := get_eq_iff_eq_some.mp rfl

/-- TODO: why is this not marked simp? Does something break? -/
attribute [simp] bind_some_eq_map

end part

namespace pfun

lemma fix_diverge {α β : Type*} {f : α →. β ⊕ α} (a : α) (ha : ¬(f a).dom) : f.fix a = part.none :=
by { rw part.eq_none_iff, intros b hb, exact ha (dom_of_mem_fix hb), }

lemma fix_iterate' {α β : Type*} {f : α →. β ⊕ α} (a : α) (a' : part α) (ha' : f a = a'.map sum.inr) :
  f.fix a = a' >>= λ r, f.fix r :=
begin
  cases a' with d₁ v₁, by_cases h₁ : d₁,
  { simp only [h₁, part.mk_some] at ⊢ ha', rw fix_fwd a (v₁ h₁), { simp, }, simpa [part.eq_some_iff] using ha', },
  rw fix_diverge, { simp [h₁], }, simpa [h₁, part.eq_none_iff'] using ha',
end


end pfun