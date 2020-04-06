import data.real.basic
import data.set
import analysis.normed_space.basic

/- Kevin Doran effort -/
-- Q0. Notation for absolute. Should I reuse this from somewhere in Lean or mathlib?
local notation `|`x`|` := abs x

def is_adherent (x : ℝ) (X : set ℝ) : Prop :=
∀ ε > 0, ∃y ∈ X, |x - y| ≤ ε

infix `is_adherent_to` :55 := is_adherent

def closure' (X : set ℝ) : set ℝ :=
{x : ℝ | x is_adherent_to X }

-- closure_mono term proof

/-- If $$X\subseteq Y$$ then $$\overline{X}\subseteq\overline{Y}$$ -/
theorem closure'_mono {X Y : set ℝ} (hXY : X ⊆ Y) : closure' X ⊆ closure' Y :=
λ a haX ε hε, let ⟨x, haX', h⟩ := haX ε hε in ⟨x, hXY haX', h⟩

-- closure_mono tactic proof
example {X Y : set ℝ} (hXY : X ⊆ Y) : closure' X ⊆ closure' Y :=
begin
  -- Say a is in the closure of X. We want to show a is in the closure of Y.
  -- So say ε > 0. We want to find y ∈ Y such that |a - y| ≤ ε.
  intros a haX ε hε,
  -- By definition of closure of X, there's x ∈ X with |a - x| ≤ ε.
  rcases haX ε hε with ⟨x, haX', h⟩,
  -- So let y be x.
  use x,
  -- Remark:
  split,
  { -- x is in Y because it's in X and X ⊆ Y
    exact hXY haX', -- hXY is actually a function!
  },
  -- oh but now one of our assumptions is the conclusion
  assumption
end

-- subset_closure term proof

/-- For all subsets $$X$$ of $$\mathbb{R}$$, we have $$X\subseteq\overline{X}$$ -/
lemma subset_closure' {X : set ℝ} : X ⊆ closure' X :=
λ x hx ε hε, ⟨x, hx, le_of_lt (by rwa [sub_self, abs_zero])⟩

-- tactic proof

example {X : set ℝ} : X ⊆ closure' X :=
begin
  -- Say x ∈ X and ε > 0.
  intros x hx ε hε,
  -- We need to find y ∈ X with |x - y| ≤ ε. Just use x.
  use x,
  -- Remark: x ∈ X
  split, exact hx,
  -- Note also that |x - x| is obviously zero
  simp,
  -- and because ε > 0 we're done
  exact le_of_lt hε
  -- Note that that last bit would have been better if your definition of closure'
  -- had used < and not ≤
end

-- closure_closure

-- Note: for some reason this is not formalaised as `closure ∘ closure = closure`
-- I don't know why we have this convention

-- tactic mode proof

/-- The closure of $$\overline{X}$$ is $$\overline{X}$$ again -/
lemma closure'_closure' (X : set ℝ) : closure' (closure' X) = closure' X := --
begin
  -- We prove inclusions in both directions
  ext a,
  split,
  --
  { -- ⊆ : say $$a$$ is in the closure of $$\overline{X}$$.
    intro ha,
    -- We want to show it's in $$\overline{X}$$ so say ε > 0, and we want x with |x-a| ≤ ε
    intros ε hε,
    -- By definition of a, there's some elements $$b\in\overline{X}$$
    -- with |a - b| ≤ ε/2
    rcases ha (ε/2) (by linarith) with ⟨b, hb, hab⟩,
    -- and by definition of b there's some x ∈ X with |b - x| ≤ ε/2
    rcases hb (ε/2) (by linarith) with ⟨x, hx, hbx⟩,
    -- Let's use this x
    use x,
    -- Note it's obviously in X
    split, exact hx,
    -- and now |a - x| = |(a - b) + (b - x)|
    calc |a - x| = |(a - b) + (b - x)| : by ring
                   -- ≤ ε/2 + ε/2 = ε
    ...          ≤ |a - b| + |b - x|   : by apply abs_add
    ...          ≤ ε : by linarith
  },
  { -- ⊇ : follows immediately from subset_closure'
    intro h, apply subset_closure' h,
  }
end

-- closure_squeeze term mode proof
lemma closure'_squeeze {X Y : set ℝ} (h₁ : X ⊆ Y) (h₂ : Y ⊆ closure'(X)) :
  closure'(X) = closure'(Y) :=
set.subset.antisymm (closure'_mono h₁) $ by rw ←closure'_closure' X; apply closure'_mono h₂

-- tactic mode proof
example {X Y : set ℝ} (h₁ : X ⊆ Y) (h₂ : Y ⊆ closure'(X)) :
  closure'(X) = closure'(Y) :=
begin
  -- We prove inclusions in both directions
  apply set.subset.antisymm,
  { -- ⊆ is just closure'_mono
    apply closure'_mono h₁},
  { -- ⊇ -- first use closure'_closure'
    rw ←closure'_closure' X,
    -- and then it follows from closure'_mono
    apply closure'_mono h₂},
end

lemma closure_monotone : monotone closure' :=
λ X Y H a ha ε hε, let ⟨p, hpx, hapε⟩ := ha ε hε in ⟨p, H hpx, hapε⟩

lemma closure_inter_subset_inter_closure' (X Y : set ℝ) :
closure' (X ∩ Y) ⊆ closure' X ∩ closure' Y :=
(closure_monotone).map_inf_le _ _
