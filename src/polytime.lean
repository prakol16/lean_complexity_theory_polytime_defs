import data.polynomial.eval
import time_bound

def polytime (c : code) : Prop :=
∃ (p : polynomial ℕ), time_bound c (λ n, p.eval n)

lemma polytime_fst : polytime code.fst :=
by { use (polynomial.monomial 1 1) + 1, simpa using time_bound_fst, }

lemma polytime_snd : polytime code.snd :=
by { use (polynomial.monomial 1 1) + 1, simpa using time_bound_snd, }

lemma polytime_bit (b : bool) : polytime (code.bit b) :=
by { use (polynomial.monomial 1 1) + 1, simpa using time_bound_bit b, }

lemma polytime_pair {c₁ c₂ : code} : polytime c₁ → polytime c₂ → polytime (code.pair c₁ c₂)
| ⟨p₁, e₁⟩ ⟨p₂, e₂⟩ := by { use p₁ + p₂ + 3, convert time_bound_pair e₁ e₂, simp, }

lemma polytime_comp {c₁ c₂ : code} : polytime c₁ → polytime c₂ → polytime (code.comp c₁ c₂)
| ⟨p₁, e₁⟩ ⟨p₂, e₂⟩ := by { use p₂ + (p₁.comp (p₂^2 + 1)) + 1, convert time_bound_comp e₁ e₂, simp, }

lemma polytime_case {c₁ c₂ c₃ : code} : polytime c₁ → polytime c₂ → polytime c₃ → polytime (code.case c₁ c₂ c₃)
| ⟨p₁, e₁⟩ ⟨p₂, e₂⟩ ⟨p₃, e₃⟩ := by { use p₁ + p₂ + (p₃.eval 0) + 1, convert time_bound_case' e₁ e₂ e₃, simp, }

lemma polytime_zero : polytime zero :=
by { apply polytime_comp, apply polytime_fst, apply polytime_bit, }

lemma polytime_tail : polytime tail :=
polytime_comp polytime_snd (polytime_comp (polytime_bit _) (polytime_comp (polytime_bit _) (polytime_bit _)))

lemma polytime_id : polytime code.id :=
polytime_comp polytime_snd (polytime_bit _)

lemma polytime_append_const (bs : list bool) : polytime (append_const bs) :=
by { induction bs, { exact polytime_id, }, apply polytime_comp (polytime_bit _), assumption, }

lemma polytime_const (n : ℕ) : polytime (code.const n) :=
polytime_comp (polytime_append_const _) polytime_zero