import data.real.basic
import data.int.parity

attribute [instance] classical.prop_decidable

/- 
Lemmas from that file were hidden in my course, or restating things which
were proved without name in previous files.
-/

notation `|`x`|` := abs x

-- The mathlib version is unusable because it is stated in terms of ≤
lemma superieur_max_ssi {α : Type*} [decidable_linear_order α] (p q r : α) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

/- No idea why this is not in mathlib-/
lemma egal_si_abs_eps (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y :=
begin
  intro h, 
  apply  decidable_linear_ordered_add_comm_group.eq_of_abs_sub_nonpos,
  by_contradiction H,
  push_neg at H,
  specialize h ( |x-y|/2) (by linarith),
  linarith,
end

def limite_suite (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

lemma unicite_limite {u l l'} : limite_suite u l → limite_suite u l' → l = l' :=
begin
  intros hl hl',
  apply egal_si_abs_eps,
  intros ε ε_pos,
  specialize hl (ε/2) (by linarith),
  cases hl with N hN,
  specialize hl' (ε/2) (by linarith),
  cases hl' with N' hN',
  specialize hN (max N N') (le_max_left _ _),
  specialize hN' (max N N') (le_max_right _ _),
  calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')| : by ring
  ... ≤ |l - u (max N N')| + |u (max N N') - l'| : by apply abs_add
  ... =  |u (max N N') - l| + |u (max N N') - l'| : by rw abs_sub
  ... ≤ ε/2 + ε/2 : by linarith
  ... = ε : by ring,
end

def pair (n : ℤ) := ∃ k, n = 2*k

def impair (n : ℤ) := ∃ k, n = 2*k + 1

lemma pair_ou_impair (n : ℤ) : pair n ∨ impair n :=
by by_cases h : n % 2 = 0 ; [left, {right ; rw int.mod_two_ne_zero at h}] ;
  rw [← int.mod_add_div n 2, h] ; use n/2 ; simp [add_comm]

lemma non_pair_et_impair (n : ℤ) : ¬ (pair n ∧ impair n) :=
begin
  rintro ⟨h, h'⟩,
  change int.even n at h,
  rw int.even_iff at h,
  rcases h' with ⟨k, rfl⟩,
  simp only [int.add_mul_mod_self_left, add_comm, euclidean_domain.mod_eq_zero] at h,
  cases h with l hl,
  rw eq_comm at hl,
  have := int.eq_one_of_mul_eq_one_right (by linarith) hl,
  linarith,
end


namespace tactic.interactive
open tactic

meta def verifie : tactic unit :=
`[ { repeat { unfold limite_suite},
   repeat { unfold continue_en },
   push_neg,
   try { simp only [exists_prop] },
   try { exact iff.rfl },
   done } <|> fail "Ce n'est pas cela. Essayez encore." ]

end tactic.interactive