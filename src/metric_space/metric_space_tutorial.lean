--import data.set
--import data.set.finite
import data.real.basic
--import data.finset
--import order.conditionally_complete_lattice
import topology.opens -- remove when finished checking types of things.
-- note: we don't import topology.metric_space.basic, which is
-- mathlib's version of metric spaces

/-! -/
--open_locale classical

open set


/-- A metric space is a set/type X equipped with a real-valued distance function
    satisfying the usual axioms -/
class metric_space (X : Type) :=
(dist : X → X → ℝ)
(dist_self : ∀ x : X, dist x x = 0)
(eq_of_dist_eq_zero : ∀ {x y : X}, dist x y = 0 → x = y)
(dist_comm : ∀ x y : X, dist x y = dist y x)
(dist_triangle : ∀ x y z : X, dist x z ≤ dist x y + dist y z)

-- Exercise: compare with the definition in all the maths books.
-- Did we leave something out?

-- theorems that we are about to prove about metric spaces go in the metric space namespace
namespace metric_space

-- let X be a metric space
variables {X : Type} [metric_space X]

/-! # Learning to use `linarith`

We left out the axiom that ∀ x y : X, dist x y ≥ 0 in our metric space,
because it can be deduced from the triangle inequality and symmetry!
Let's prove it now, using `linarith`. The `linarith` tactic proves
many "obvious" results involving inequalities as long as the expressions
involved have degree 1. It looks at the hypotheses and tries to prove
the goal. For example if `h : 0 ≤ a + a` is a hypothesis, and the goal
is `⊢ 0 ≤ a`, then `linarith` will close the goal.

Other useful tactics :

`have h := dist_triangle x y x` will create a new hypothesis `h`.

`push_neg` will move `¬` as far to the right as it can, and possibly
remove it. For example if `h : ¬ (a ≤ b)` then `push_neg at h` will change `h` to `b < a`.

`by_contra h` will create a hypothesis `h` saying that the goal is false, and
will replace the goal with `false`. Note that `linarith` can even prove a goal `false` if
the hypotheses are contradictory.

Let's prove some basic things about distances using `linarith`.

-/

theorem dist_nonneg : ∀ (x y : X), 0 ≤ dist x y :=
begin
  --replace with sorry in tutorial
  intros x y,
  have h := dist_triangle x y x,
  rw dist_self at h,
  rw dist_comm y x at h,
  linarith,
end

theorem dist_le_zero {x y : X} : dist x y ≤ 0 ↔ x = y :=
begin
  --replace with sorry in tutorial
  split,
  { intro h,
    have h2 := dist_nonneg x y,
    apply eq_of_dist_eq_zero,
    linarith,
  },
  { intro h,
    rw h,
    rw dist_self,
  }
end

theorem dist_pos {x y : X} : 0 < dist x y ↔ x ≠ y :=
begin
  --replace with sorry in tutorial
  split,
  { intro h,
    intro hxy,
    rw ←dist_le_zero at hxy,
    linarith,
  },
  { intro h,
    by_contra h2,
    push_neg at h2,
    rw dist_le_zero at h2,
    contradiction,

  }
end

/-! ### Open balls

We define `ball x ε` to be the open ball centre `x` and radius `ε`. Note that we do not
require `ε > 0`! That hypothesis shows up later in the theorems, not in the definition.


-/

variables {x y z : X} {ε ε₁ ε₂ : ℝ} {s : set X}

/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
def ball (x : X) (ε : ℝ) : set X := {y | dist y x < ε}

-- Let's tag this lemma with the `simp` tag, so the `simp` tactic will use it.
@[simp] theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε := iff.rfl -- true by definition

-- Now we get this proof for free:
theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε :=
begin
  simp [dist_comm]
end

-- Let's tag `dist_self` with the `simp` tag too:

attribute [simp] dist_self

-- Can you find a proof of this? And then can you find a one-line proof using `simp`?
theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε :=
begin
  --replace with sorry
  rw mem_ball,
  rw dist_self,
  exact h,
end

/- Top tip: `rw mem_ball at hy ⊢` will rewrite `mem_ball` at both the hypothesis `hy` and the goal.
  Get `⊢` in VS Code with `\|-`

-/
theorem ball_mono (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ :=
begin
  -- delete me
  intros y hy,
  rw mem_ball at hy ⊢,
  linarith,
end


/-! # Open sets.

A subset of a metric space is open if for every element `s` in the subset, there's some open
ball `ball s ε`, with ε > 0, entirely contained with `S`.
-/

/-- A subset U of a metric space is open if every s ∈ U there's an open ball centre s within U -/
def is_open (U : set X) := ∀ s ∈ U, ∃ (ε : ℝ) (hε : 0 < ε), ball s ε ⊆ U

-- Note that `is_open` is a Proposition. Things like `is_open_Union` below are proofs.

-- Let's start with two easy facts about open sets -- the empty set and the whole space is open.
theorem is_open_empty : is_open (∅ : set X) :=
begin
  intro x,
  intro hx,
  cases hx,-- too hard for a beginner. Need to get a contradiction from `h : x ∈ ∅`
end

theorem is_open_univ : is_open (univ : set X) :=
begin
  intro x,
  intro hx,
  use 37,
  split,
    norm_num,
  -- need subset_univ
  simp,
end

-- An arbitrary union of open sets is open. The union is indexed over an auxiliary type ι

-- TODO: I don't think this is any good, people need to know about set.subset.trans,
-- set.subset.Union etc. Should do something on sets first?

theorem is_open_Union (ι : Type) (f : ι → set X) (hf : ∀ (i : ι), is_open (f i)) :
  is_open (⋃ (i : ι), f i) :=
begin
  intro x,
  intro hx,
  rcases hx with ⟨U, ⟨i, rfl⟩, hxU⟩,
  have h := hf i x hxU,
  rcases h with ⟨ε, hε, hxε⟩,
  use ε,
  split, use hε,
  refine set.subset.trans hxε _,
  apply set.subset_Union,
end

theorem is_open_inter {U V : set X}  (hU : is_open U) (hV : is_open V) : is_open (U ∩ V) := sorry




/- A subset S of a metric space is closed if its complement is open -/
def is_closed (S : set X) := is_open (-S)

end metric_space

#exit

-- the lemmas from 274 to 300:
theorem closed_ball_subset_closed_ball {α : Type u} [metric_space α] {ε₁ ε₂ : ℝ} {x : α} (h : ε₁ ≤ ε₂) :
  closed_ball x ε₁ ⊆ closed_ball x ε₂ :=
λ y (yx : _ ≤ ε₁), le_trans yx h

theorem ball_disjoint (h : ε₁ + ε₂ ≤ dist x y) : ball x ε₁ ∩ ball y ε₂ = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ z ⟨h₁, h₂⟩,
not_lt_of_le (dist_triangle_left x y z)
  (lt_of_lt_of_le (add_lt_add h₁ h₂) h)

theorem ball_disjoint_same (h : ε ≤ dist x y / 2) : ball x ε ∩ ball y ε = ∅ :=
ball_disjoint $ by rwa [← two_mul, ← le_div_iff' two_pos]

theorem ball_subset (h : dist x y ≤ ε₂ - ε₁) : ball x ε₁ ⊆ ball y ε₂ :=
λ z zx, by rw ← add_sub_cancel'_right ε₁ ε₂; exact
lt_of_le_of_lt (dist_triangle z x y) (add_lt_add_of_lt_of_le zx h)

theorem ball_half_subset (y) (h : y ∈ ball x (ε / 2)) : ball y (ε / 2) ⊆ ball x ε :=
ball_subset $ by rw sub_self_div_two; exact le_of_lt h

theorem exists_ball_subset_ball (h : y ∈ ball x ε) : ∃ ε' > 0, ball y ε' ⊆ ball x ε :=
⟨_, sub_pos.2 h, ball_subset $ by rw sub_sub_self⟩

theorem ball_eq_empty_iff_nonpos : ε ≤ 0 ↔ ball x ε = ∅ :=
(eq_empty_iff_forall_not_mem.trans
⟨λ h, le_of_not_gt $ λ ε0, h _ $ mem_ball_self ε0,
 λ ε0 y h, not_lt_of_le ε0 $ pos_of_mem_ball h⟩).symm

@[simp] lemma ball_zero : ball x 0 = ∅ :=
by rw [← metric.ball_eq_empty_iff_nonpos]

--

-- Do we want this?
theorem eq_of_forall_dist_le {x y : α} (h : ∀ε, ε > 0 → dist x y ≤ ε) : x = y :=
eq_of_dist_eq_zero (eq_of_le_of_forall_le_of_dense dist_nonneg h)

/-- The triangle (polygon) inequality for sequences of points; `finset.range` version. -/
lemma dist_le_range_sum_dist (f : ℕ → α) (n : ℕ) :
  dist (f 0) (f n) ≤ (finset.range n).sum (λ i, dist (f i) (f (i + 1))) :=
finset.Ico.zero_bot n ▸ dist_le_Ico_sum_dist f (nat.zero_le n)

-- From mathlib
https://github.com/leanprover-community/mathlib/blob/17632202cdf9682cea972e86437d32ac20c91b06/src/topology/basic.lean#L262-L319

def closure (s : set α) : set α := ⋂₀ {t | is_closed t ∧ s ⊆ t}
