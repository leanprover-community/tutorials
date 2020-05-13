import data.real.basic

open_locale classical

/-
Theoretical negations.

This file is for people interested in logic who want to fully understand
negations.

Here we don't use `contrapose` or `push_neg`. The goal is to prove lemmas
that are used by those tactics. Of course we can use
`exfalso`, `by_contradiction` and `by_cases`.

If this doesn't sound like fun then skip ahead to the next file.
-/

section negation_prop

variables P Q : Prop

-- 0055
example : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  -- sorry
  split,
  { intros h hnQ hP,
    exact hnQ (h hP) },
  { intros h hP,
    by_contradiction hnQ,
    exact h hnQ hP },
  -- sorry
end

-- 0056
lemma non_imp (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q :=
begin
  -- sorry
  split,
  { intro h,
    by_contradiction H,
    apply h,
    intro hP,
    by_contradiction H',
    apply H,
    exact ⟨hP, H'⟩ },
  { intros h h',
    cases h with hP hnQ,
    exact hnQ (h' hP) },
  -- sorry
end

-- In the next one, let's use the axiom
-- propext {P Q : Prop} : (P ↔ Q) → P = Q

-- 0057
example (P : Prop) : ¬ P ↔ P = false :=
begin
  -- sorry
  split,
  { intro h,
    apply propext,
    split,
    { intro h',
      exact h h' },
    { intro h,
      exfalso,
      exact h } },
  { intro h,
    rw h,
    exact id },
  -- sorry
end

end negation_prop

section negation_quantifiers
variables (X : Type) (P : X → Prop)

-- 0058
example : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x :=
begin
  -- sorry
  split,
  { intro h,
    by_contradiction H,
    apply h,
    intros x,
    by_contradiction H',
    apply H,
    use [x, H'] },
  { rintros ⟨x, hx⟩ h',
    exact hx (h' x) },
  -- sorry
end

-- 0059
example : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x :=
begin
  -- sorry
  split,
  { intros h x h',
    apply h,
    use [x, h'] },
  { rintros h ⟨x, hx⟩,
    exact h x hx },
  -- sorry
end

-- 0060
example (P : ℝ → Prop) : ¬ (∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬ P ε :=
begin
  -- sorry
  split,
  { intros h ε ε_pos hP,
    apply h,
    use [ε, ε_pos, hP] },
  { rintros h ⟨ε, ε_pos, hP⟩,
    exact h ε ε_pos hP },
  -- sorry
end

-- 0061
example (P : ℝ → Prop) : ¬ (∀ x > 0, P x) ↔ ∃ x > 0, ¬ P x :=
begin
  -- sorry
  split,
  { intros h,
    by_contradiction H,
    apply h,
    intros x x_pos,
    by_contradiction HP,
    apply H,
    use [x, x_pos, HP] },
  { rintros ⟨x, xpos, hx⟩ h',
    exact hx (h' x xpos) },
  -- sorry
end

end negation_quantifiers
