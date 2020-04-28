import ..untranslated.my_lib

/-
Théorie de la négation.

Dans cette série, on n'utilisera ni contrapose ni push_neg, le but est
de démontrer des lemmes utilisés automatiquement par ces commandes.
On pourra bien sûr utiliser exfalso, by_contradiction et by_cases.

Cette série est *facultative*. Elle s'adresse aux étudiants voulant étudier
à fond le mécanisme de la négation d'énoncés.
-/

section negation_enonces

variables P Q : Prop

example : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  -- sorry
  split,
    intros h hnQ hP,
    exact hnQ (h hP),
  intros h hP,
  by_contradiction hnQ,
  exact h hnQ hP,
  -- sorry
end

lemma non_imp (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q :=
begin
  -- sorry
  split,
    intro h,
    by_contradiction H,
    apply h,
    intro hP,
    by_contradiction H',
    apply H,
    exact ⟨hP, H'⟩,
  intros h h',
  cases h with hP hnQ,
  exact hnQ (h' hP),
  -- sorry
end

-- Dans l'exercice suivant, on pourra utiliser l'axiome :
-- propext {P Q : Prop} : (P ↔ Q) → P = Q

example (P : Prop) : ¬ P ↔ P = false :=
begin
  -- sorry
  split,
  intro h,
  apply propext,
  split,
  intro h',
  exact h h',
  intro h,
  exfalso, exact h,
  intro h,
  rw h,
  exact id,
  -- sorry
end

end negation_enonces

section negation_quantificateurs
variables (X : Type) (P : X → Prop)

example : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x :=
begin
  -- sorry
  split,
    intro h,
    by_contradiction H,
    apply h,
    intros x,
    by_contradiction H',
    apply H,
    use [x, H'],
  intros h h',
  cases h with x hx,
  specialize h' x,
  exact hx h',
  -- sorry
end

example : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x :=
begin
  -- sorry
  split,
    intros h x h',
    apply h,
    use [x, h'],
  intros h h',
  cases h' with x hx,
  exact h x hx,
  -- sorry
end


example (P : ℝ → Prop) : ¬ (∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬ P ε :=
begin
  -- sorry
  split,
    intros h ε ε_pos hP,
    apply h,
    use [ε, ε_pos, hP],
  intros h H,
  cases H with ε H,
  cases H with ε_pos hP,
  exact h ε ε_pos hP,
  -- sorry
end

example (P : ℝ → Prop) : ¬ (∀ x > 0, P x) ↔ ∃ x > 0, ¬ P x :=
begin
  -- sorry
  split,
    intros h,
    by_contradiction H,
    apply h,
    intros x x_pos,
    by_contradiction HP,
    apply H,
    use [x, x_pos, HP],
  intros h h',
  cases h with x h,
  cases h with xpos hx,
  exact hx (h' x xpos),
  -- sorry
end

end negation_quantificateurs
