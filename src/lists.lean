import tactic
import data.list.basic

namespace list
variables {α : Type*}

@[simp] theorem append_inj'_iff (s₁ s₂ : list α) {t₁ t₂ : list α} (hl : length t₁ = length t₂) :
  s₁ ++ t₁ = s₂ ++ t₂ ↔ s₁ = s₂ ∧ t₁ = t₂ :=
⟨λ h, append_inj' h hl, by cc⟩


@[simp] theorem init_nil : (@list.nil α).init = [] := rfl

@[simp] theorem init_singleton (x : α) : [x].init = [] := rfl


@[simp] lemma last'_reverse {α : Type*} (xs : list α) : xs.reverse.last' = xs.head' :=
by cases xs; simp

lemma last'_eq_head'_reverse {α : Type*} (xs : list α) : xs.last' = xs.reverse.head' :=
by simpa using xs.reverse.last'_reverse

/-- Take cases on the last element of the list. Like `reverse_rec_on`, this can be used
for constructing data as well. -/
def reverse_cases_on {α : Type*} {C : list α → Sort*} (l : list α) (h₀ : C [])
  (case : ∀ st lt, C (st ++ [lt])) : C l :=
by { induction l using list.reverse_rec_on, { exact h₀, }, { apply case, } }

/-! ### after -/
section after

lemma after_spec {α : Type*} (p : α → Prop) [decidable_pred p]
  (as : list α) (x : α) (xs : list α) (has : ∀ a ∈ as, ¬p a) (hx : p x) :
  (as ++ x :: xs).after p = xs :=
begin
  induction as with hd tl ih, { simp [after, hx], },
  simp [after, has hd, ih (λ a ha, has a (or.inr ha))],
end

lemma after_sublist {α : Type*} (p : α → Prop) [decidable_pred p] (xs : list α) :
  xs.after p <+ xs :=
begin
  induction xs, { refl, },
  simp only [after], split_ifs; apply sublist.cons, { refl, }, { assumption, }
end

lemma after_sublist_strict {α : Type*} (p : α → Prop) [decidable_pred p] (x : α) (xs : list α) :
  (x :: xs).after p <+ xs :=
by { simp only [after], split_ifs, { refl, }, { apply after_sublist, } }

lemma after_length_lt {α : Type*} (p : α → Prop) [decidable_pred p] {xs : list α} :
  (xs.after p).length < xs.length ↔ 0 < xs.length :=
⟨pos_of_gt, begin
  cases xs, { simp, },
  intro, simpa [nat.lt_succ_iff] using length_le_of_sublist (after_sublist_strict p _ _),
end⟩


end after

/-! ### take_while -/
section take_while

lemma take_while_spec {α : Type*} (p : α → Prop) [decidable_pred p]
  (as : list α) (x : α) (xs : list α) (has : ∀ a ∈ as, p a) (hx : ¬ p x) :
  (as ++ x :: xs).take_while p = as :=
begin
  induction as with hd tl ih, { simp [take_while, hx], },
  simp [take_while, has hd, ih (λ a ha, has a (or.inr ha))],
end

end take_while

end list