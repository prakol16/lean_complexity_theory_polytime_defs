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

@[simp] lemma last_eq_none_iff {α : Type*} (ls : list α) :
  ls.last' = none ↔ ls = [] :=
begin
  split, swap, { intro h, rw h, refl, },
  contrapose, induction ls with hd tl ih, { simp, },
  intro, cases tl, { simp, }, simpa using ih,
end

@[simp] lemma last'_cons {α : Type*} (hd : α) (tl : list α) (ht : tl ≠ []) :
  (hd :: tl).last' = tl.last' :=
by { induction tl, { cases ht rfl, }, simp, }

lemma last'_of_tail {α : Type*} {l : list α} {x : α} (hx : x ∈ l.tail.last') : x ∈ l.last' :=
by { cases l with hd tl, { simp at hx, contradiction, }, cases tl, { simp at hx, contradiction, }, simpa using hx, } 

lemma last_cons_is_some {α : Type*} (hd : α) (tl : list α) :
  (hd :: tl).last'.is_some := by induction tl; simp [*]

@[simp] lemma drop_last {α : Type*} (ls : list α) (n : ℕ) (hn : n < ls.length) :
  (ls.drop n).last' = ls.last' :=
begin
  induction ls with hd tl ih generalizing n, { simp, },
  cases n, { simp, },
  specialize ih n _, { simpa [nat.succ_eq_add_one] using hn, },
  have : tl ≠ [], { intro h, subst h, simpa using hn, },
  simp [this, ih],
end

example {α: Type} (hd : α) (tl : list α) (x : α) (hx : x ∈ tl.last') : x ∈ (hd :: tl).last' := mem_last'_cons hx

lemma after_last {α : Type*} (ls : list α) (p : α → Prop) [decidable_pred p] :
  ∀ x ∈ (ls.after p).last', x ∈ ls.last' :=
begin
  induction ls with hd tl ih, { simp [after], },
  intros x hx,
  by_cases h : p hd,
  { simp [h, after, ← option.mem_def] at ⊢ hx, apply mem_last'_cons hx, },
  specialize ih x _,
  { simp [h, after] at hx, exact hx, },
  apply mem_last'_cons ih,
end

end list
