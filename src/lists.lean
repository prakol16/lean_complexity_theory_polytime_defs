import tactic

namespace list
/- These are just a few misc lemmas (might already be in mathlib even)
  about lists -/

lemma after_spec {α : Type*} (p : α → Prop) [decidable_pred p]
  (as : list α) (x : α) (xs : list α) (has : ∀ a ∈ as, ¬ p a) (hx : p x) :
  (as ++ x :: xs).after p = xs :=
begin
  induction as with hd tl ih, { simp [list.after, hx], },
  simp [list.after, has hd, ih (λ a ha, has a (or.inr ha))],
end

lemma take_while_spec {α : Type*} (p : α → Prop) [decidable_pred p]
  (as : list α) (x : α) (xs : list α) (has : ∀ a ∈ as, p a) (hx : ¬ p x) :
  (as ++ x :: xs).take_while p = as :=
begin
  induction as with hd tl ih, { simp [list.take_while, hx], },
  simp [list.take_while, has hd, ih (λ a ha, has a (or.inr ha))],
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
begin
  split, { exact pos_of_gt, },
  cases xs, { simp, },
  exact (λ _, nat.lt_succ_iff.mpr (length_le_of_sublist (after_sublist_strict _ _ _))),
end

lemma empty_ff_iff_neq_nil {α : Type*} {ls : list α} : ls.empty = ff ↔ ls ≠ [] :=
by { convert not_congr (@empty_iff_eq_nil _ ls), simp, }

@[simp] lemma append_singleton' {α : Type*} (x : α) : append [x] = cons x :=
by { ext : 1, simp, }

/-- Really annoying, I couldn't get the standard `cases_on` types to work -/
@[simp] def cases_on' {α β : Type*} (ls : list α) (start : β) (step : α → list α → β) : β :=
@list.cases_on _ (λ _, β) ls start step

@[simp] lemma foldl_of_cons {α : Type*} (ls : list α) :
  ls.foldl (flip list.cons) [] = ls.reverse :=
begin
  suffices : ∀ b, ls.foldl (flip list.cons) b = ls.reverse ++ b,
  { simpa using this [], },
  induction ls with hd tl ih, { simp, },
  intro b, simp [ih], refl,
end

end list
