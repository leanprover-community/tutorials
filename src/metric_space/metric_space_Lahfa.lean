import data.set
import data.set.finite
import data.real.basic
import data.finset
import order.conditionally_complete_lattice

noncomputable theory
open_locale classical
open set

class metric_space (X : Type) :=
(d : X → X → ℝ)
(d_pos : ∀ x y, d x y ≥ 0)
(presep : ∀ x y, x = y → d x y = 0)
(sep : ∀ x y, d x y = 0 →  x = y)
(sym : ∀ x y, d x y = d y x)
(triangle : ∀ x y z, d x z ≤ d x y + d y z)

variables {X:Type} [metric_space X]

open metric_space

instance real.metric_space : metric_space ℝ :=
{ d                  := λx y, abs (x - y),
  d_pos              := by simp [abs_nonneg],
  presep             := begin simp, apply sub_eq_zero_of_eq end,
  sep                := begin simp, apply eq_of_sub_eq_zero end,
  sym                := assume x y, abs_sub _ _,
  triangle           := assume x y z, abs_sub_le _ _ _ }

theorem real.dist_eq (x y : ℝ) : d x y = abs (x - y) := rfl

theorem real.dist_0_eq_abs (x : ℝ) : d x 0 = abs x :=
by simp [real.dist_eq]

def converge (x: ℕ → X) (l : X) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, ((d l (x n))  < ε)

lemma real.sup_sub_lt_eps {S: set ℝ}: ∀ ε > 0, ∃ x ∈ S, Sup S - x < ε := sorry
lemma real.sup_dist_lt_eps {S: set ℝ}: ∀ ε > 0, ∃ x ∈ S, d (Sup S) x < ε := begin
  intros ε hε,
  obtain ⟨ x, hx, hs_lt ⟩ := real.sup_sub_lt_eps ε hε,
  use x,
  split,
  exact hx,
  rw real.dist_eq,
  apply abs_lt_of_lt_of_neg_lt,
  exact hs_lt,
  sorry,
end

lemma converge_of_dist_lt_one_div_succ {x: ℕ → ℝ} {l: ℝ}: (∀ n, d l (x n) ≤ 1 / (n + 1)) → converge x l := begin
intro H,
intros ε hε,
obtain ⟨ N, hN ⟩ := exists_nat_one_div_lt hε,
use N,
intros n hn,
calc d l (x n) ≤ 1 / (n + 1) : H n
    ... ≤ 1 / (N + 1) : nat.one_div_le_one_div hn
    ... < ε : hN
end

lemma sup_is_a_cv_seq (S: set ℝ):
  S.nonempty → bdd_above S → ∃ (x: ℕ → ℝ), (∀ n, x n ∈ S) ∧ converge x (Sup S) := begin
  intros hnn hbdd,
  have: ∀ (N: ℕ), ∃ x ∈ S, d (Sup S) x < 1/(N + 1) := begin
  intro N,
  apply real.sup_dist_lt_eps,
  apply nat.one_div_pos_of_nat,
  end,
  choose x hrange h using this,
  use x,
  split,
  exact hrange,
  exact converge_of_dist_lt_one_div_succ h, -- this line should work (?)
  end

#exit
But, I have some issue regarding the types, here is the state at the last step:

type mismatch at application
  converge_of_dist_lt_one_div_succ h
term
  h
has type
  ∀ (N : ℕ), d (Sup S) (x N) < 1 / (↑N + 1)
but is expected to have type
  ∀ (n : ℕ), d (Sup S) (x n) ≤ 1 / (↑n + 1)
state:
S : set ℝ,
hnn : set.nonempty S,
hbdd : bdd_above S,
x : ℕ → ℝ,
hrange : ∀ (N : ℕ), x N ∈ S,
h : ∀ (N : ℕ), d (Sup S) (x N) < 1 / (↑N + 1)
⊢ converge x (Sup S)
