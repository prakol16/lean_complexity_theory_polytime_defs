import code
import frespects_pfun

/-! This code is adapted from Bolton Bailey's PR: https://github.com/leanprover-community/mathlib/pull/11046 -/

open boolcodeable (encode decode)

local attribute [reducible] bitstring

def time {ι : Type} (impl : ι → bitstring → bitstring) : code ι → bitstring →. ℕ
| (code.oracle i) := λ b, pure 1
| (code.pair c₁ c₂) := λ v, (+1) <$> (time c₁ v) + (time c₂ v)
| (code.comp c₁ c₂) := λ v, (+1) <$> (time c₂ v) + (c₂.eval impl v >>= time c₁)
| (code.case c₁ c₂) := λ v, (+1) <$> (if v.head = ff then time c₁ v.tail else time c₂ v.tail)
| (code.fix f) := λ v₀, (@pfun.fix (bitstring × ℕ) ℕ $ 
  λ vt, (time f vt.1) >>= λ t',
    (f.eval impl vt.1).map (λ v' : bitstring,
      if v'.head = ff then sum.inl (vt.2+t')
      else sum.inr (v'.tail, vt.2+t'))
  ) (v₀, 0)

variables {ι : Type} (impl : ι → bitstring → bitstring)

lemma time_dom_iff_eval_dom (c : code ι) (b : bitstring) : (time impl c b).dom ↔ (c.eval impl b).dom :=
begin
  induction c generalizing b,
  case code.oracle { simp [time], refl, },
  case code.pair : c₁ c₂ c₁ih c₂ih { simp only [time, code.eval, (+), (<*>)], simp [c₁ih, c₂ih], },
  case code.comp : c₁ c₂ c₁ih c₂ih { simp only [time, code.eval, (+), (<*>)], simp [c₁ih, c₂ih], tauto, },
  case code.case : c₁ c₂ c₁ih c₂ih { simp only [time, code.eval], split_ifs; simp [c₁ih, c₂ih], },
  case code.fix : f ih
  { simp only [time, code.eval], refine pfun.eq_dom_of_frespects_once prod.fst _ _,
    intro a, split,
    { simp [ih], }, split,
    { intro a',
      simp only [part.bind_eq_bind, part.mem_bind_iff, part.mem_map_iff, exists_prop, forall_exists_index, and_imp],
      intros n hn e he h, use e, refine ⟨he, _⟩,
      split_ifs at h, { contradiction, },
      rw ← h, split_ifs; refl,  },
    simp only [part.bind_eq_bind, part.mem_bind_iff, part.mem_map_iff, exists_prop, forall_exists_index, and_imp],
    intros n₁ n₂ hn₂ b hb h,
    refine ⟨b.tail, b, hb, _⟩,
    split_ifs at h ⊢, { refl, }, { contradiction, }, }
end

variables (c : code ι) (bound : ℕ → ℕ)
def time_bound : Prop :=
∀ (b : bitstring) (l : ℕ), b.sizeof ≤ l → ∃ t ∈ time impl c b, t ≤ bound l

variables {impl c bound}
lemma total_of_time_bound (H : time_bound impl c bound)
  (b : bitstring) : (c.eval impl b).dom :=
begin
  rw ← time_dom_iff_eval_dom,
  obtain ⟨n, t, _⟩ := H b b.sizeof (by refl),
  rw part.dom_iff_mem, use n, assumption,
end

lemma time_bound_oracle (i : ι) :
  time_bound impl (code.oracle i) 1 :=
by { intros _ _ _, refine ⟨1, _, (by refl)⟩, simp [time], }


lemma time_bound_pair (c₁ c₂ : code ι) {b₁ b₂ : ℕ → ℕ} (hb₁ : time_bound impl c₁ b₁) (hb₂ : time_bound impl c₂ b₂) :
  time_bound impl (code.pair c₁ c₂) (λ n, b₁ n + b₂ n + 1) :=
begin
  intros b l hb, simp only [time],
  obtain ⟨t₁, ht₁, t₁_le⟩ := hb₁ b l hb,
  obtain ⟨t₂, ht₂, t₂_le⟩ := hb₂ b l hb,
  use t₁ + t₂ + 1, split, swap, { linarith, },
  simp only [part.eq_some_iff.mpr ht₁, part.eq_some_iff.mpr ht₂, (+), (<*>)], simp, ring,
end


