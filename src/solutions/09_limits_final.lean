import tuto_lib

set_option pp.beta true
set_option pp.coercions false

/-
This is the final file in the series. Here we use everything covered
in previous files to prove a couple of famous theorems from 
elementary real analysis. Of course they all have more general versions
in mathlib.

As usual, keep in mind the following:

  abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

  ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

  le_max_left p q : p ≤ max p q

  le_max_right p q : q ≤ max p q

as well as a lemma from the previous file:

  le_of_le_add_all : (∀ ε > 0, y ≤ x + ε) →  y ≤ x

Let's start with a variation on a known exercise.
-/

-- 0071
lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : seq_limit u x)
  (ineg : ∃ N, ∀ n ≥ N, y ≤ u n) : y ≤ x :=
begin
  -- sorry
  apply le_of_le_add_all,
  intros ε ε_pos,
  cases hu ε ε_pos with N hN,
  cases ineg with N' hN',
  let N₀ := max N N',
  specialize hN N₀ (le_max_left N N'),
  specialize hN' N₀ (le_max_right N N'),
  rw abs_le at hN,
  linarith,
  -- sorry
end

/-
Let's now return to the result proved in the `00_` file of this series, 
and prove again the sequential characterization of upper bounds (with a slighly
different proof).

For this, and other exercises below, we'll need many things that we proved in previous files,
and a couple of extras.

From the 5th file:

  limit_const (x : ℝ) : seq_limit (λ n, x) x


  squeeze (lim_u : seq_limit u l) (lim_w : seq_limit w l)
    (hu : ∀ n, u n ≤ v n) (hw : ∀ n, v n ≤ w n)  : seq_limit v l

From the 8th:

  def upper_bound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x

  def is_sup (A : set ℝ) (x : ℝ) := upper_bound A x ∧ ∀ y, upper_bound A y → x ≤ y

  lt_sup (hx : is_sup A x) : ∀ y, y < x → ∃ a ∈ A, y < a :=

You can also use:

  nat.one_div_pos_of_nat {n : ℕ} : 0 < 1 / (n + 1 : ℝ)

  inv_succ_le_all :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε

and their easy consequences:

  limit_of_sub_le_inv_succ (h : ∀ n, |u n - x| ≤ 1/(n+1)) : seq_limit u x

  limit_const_add_inv_succ (x : ℝ) : seq_limit (λ n, x + 1/(n+1)) x

  limit_const_sub_inv_succ (x : ℝ) : seq_limit (λ n, x - 1/(n+1)) x

The structure of the proof is offered. It features a new tactic: 
`choose` which invokes the axiom of choice (observing the tactic state before and
after using it should be enough to understand everything). 
-/

-- 0072
lemma is_sup_iff (A : set ℝ) (x : ℝ) :
(is_sup A x) ↔ (upper_bound A x ∧ ∃ u : ℕ → ℝ, seq_limit u x ∧ ∀ n, u n ∈ A ) :=
begin
  split,
  { intro h,
    split,
    {
      -- sorry
      exact h.left,
      -- sorry
    },
    { have : ∀ n : ℕ, ∃ a ∈ A, x - 1/(n+1) < a,
      { intros n,
        have : 1/(n+1 : ℝ) > 0,
          exact nat.one_div_pos_of_nat,
        -- sorry
        exact lt_sup h _ (by linarith),
        -- sorry
      },
      choose u hu using this,
      -- sorry
      use u,
      split,
      { apply squeeze (limit_const_sub_inv_succ x) (limit_const x),
        { intros n,
          exact le_of_lt (hu n).2, },
        { intro n,
          exact h.1 _ (hu n).left, } },
      { intro n,
        exact (hu n).left },
      -- sorry
  } },
  { rintro ⟨maj, u, limu, u_in⟩, 
    -- sorry
    split,
    { exact maj },
    { intros y ymaj,
      apply lim_le limu,
      intro n,
      apply ymaj,
      apply u_in },
    -- sorry
  },
end

/-- Continuity of a function at a point  -/
def continuous_at_pt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

variables {f : ℝ → ℝ} {x₀ : ℝ} {u : ℕ → ℝ}

-- 0073
lemma seq_continuous_of_continuous (hf : continuous_at_pt f x₀)
  (hu : seq_limit u x₀) : seq_limit (f ∘ u) (f x₀) :=
begin
  -- sorry
  intros ε ε_pos,
  rcases hf ε ε_pos with ⟨δ, δ_pos, hδ⟩,
  cases hu δ δ_pos with N hN,
  use N,
  intros n hn,
  apply hδ,
  exact hN n hn,
  -- sorry
end

-- 0074
example :
  (∀ u : ℕ → ℝ, seq_limit u x₀ → seq_limit (f ∘ u) (f x₀)) →
  continuous_at_pt f x₀ :=
begin
  -- sorry
  contrapose!,
  intro hf,
  unfold continuous_at_pt at hf,
  push_neg at hf,
  cases hf with ε h,
  cases h with ε_pos hf,
  have H : ∀ n : ℕ, ∃ x, |x - x₀| ≤ 1/(n+1) ∧ ε < |f x - f x₀|,
    intro n,
    apply hf,
    exact nat.one_div_pos_of_nat,
  clear hf,
  choose u hu using H,
  use u,
  split,
    intros η η_pos,
    have fait : ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → 1 / (↑n + 1) ≤ η,
      exact inv_succ_le_all η η_pos,
    cases fait with N hN,
    use N,
    intros n hn,
    calc |u n - x₀| ≤ 1/(n+1) : (hu n).left
                ... ≤ η       : hN n hn,
  unfold seq_limit,
  push_neg,
  use [ε, ε_pos],
  intro N,
  use N,
  split,
  linarith,
  exact (hu N).right,
  -- sorry
end

/-
Recall from the 6th file:


  def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

  def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
    ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a


  id_le_extraction : extraction φ → ∀ n, n ≤ φ n

and from the 8th file:

  def tendsto_infinity (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

  not_seq_limit_of_tendstoinfinity : tendsto_infinity u → ∀ l, ¬ seq_limit u l
-/

variables {φ : ℕ → ℕ}


-- 0075
lemma subseq_tendstoinfinity
  (h : tendsto_infinity u) (hφ : extraction φ) :
tendsto_infinity (u ∘ φ) :=
begin
  -- sorry
  intros A,
  cases h A with N hN,
  use N,
  intros n hn,
  apply hN,
  calc N ≤ n   : hn
     ... ≤ φ n : id_le_extraction hφ n,
  -- sorry
end

-- 0076
lemma squeeze_infinity {u v : ℕ → ℝ} (hu : tendsto_infinity u)
(huv : ∀ n, u n ≤ v n) : tendsto_infinity v :=
begin
  -- sorry
  intros A,
  cases hu A with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  specialize huv n,
  linarith,
  -- sorry
end

/-
We will use segments: Icc a b := { x | a ≤ x ∧ x ≤ b }
The notation stands for Interval-closed-closed. Variations exist with
o or i instead of c, where o stands for open and i for infinity.

We will use the following version of Bolzano-Weierstrass

  bolzano_weierstrass (h : ∀ n, u n ∈ [a, b]) :
    ∃ c ∈ [a, b], cluster_point u c

as well as the obvious

  seq_limit_id : tendsto_infinity (λ n, n)
-/
open set


-- 0077
lemma bdd_above_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, continuous_at_pt f x) :
∃ M, ∀ x ∈ Icc a b, f x ≤ M :=
begin
  -- sorry
  by_contradiction H,
  push_neg at H,
  have clef : ∀ n : ℕ, ∃ x, x ∈ Icc a b ∧ f x > n,
    intro n, apply H, clear H,
  choose u hu using clef,
  have lim_infinie : tendsto_infinity (f ∘ u),
    apply squeeze_infinity (seq_limit_id),
    intros n,
    specialize hu n,
    linarith,
  have bornes : ∀ n, u n ∈ Icc a b,
    intro n, exact (hu n).left,
  rcases bolzano_weierstrass bornes with ⟨c, c_dans, φ, φ_extr, lim⟩,
  have lim_infinie_extr : tendsto_infinity (f ∘ (u ∘ φ)),
    exact subseq_tendstoinfinity lim_infinie φ_extr,
  have lim_extr : seq_limit (f ∘ (u ∘ φ)) (f c),
    exact seq_continuous_of_continuous (hf c c_dans) lim,
  exact not_seq_limit_of_tendstoinfinity  lim_infinie_extr (f c) lim_extr,
  -- sorry
end

/-
In the next exercise, we can use:

  abs_neg x : |-x| = |x|
-/

-- 0078
lemma continuous_opposite {f : ℝ → ℝ} {x₀ : ℝ} (h : continuous_at_pt f x₀) :
  continuous_at_pt (λ x, -f x) x₀ :=
begin
  -- sorry
  intros ε ε_pos,
  cases h ε ε_pos with δ h,
  cases h with δ_pos h,
  use [δ, δ_pos],
  intros y hy,
  have :  -f y - -f x₀ = -(f y - f x₀), ring,
  rw [this, abs_neg],
  exact h y hy,
  -- sorry
end

/-
Now let's combine the two exercises above
-/

-- 0079
lemma bdd_below_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, continuous_at_pt f x) :
∃ m, ∀ x ∈ Icc a b, m ≤ f x :=
begin
  -- sorry
  have : ∃ M, ∀ x ∈ Icc a b, -f x ≤ M,
  { apply bdd_above_segment,
    intros x x_dans,
    exact continuous_opposite (hf x x_dans), },
  cases this with M hM,
  use -M,
  intros x x_dans,
  specialize hM x x_dans,
  linarith,
  -- sorry
end

/-
Remember from the 5th file:

 unique_limit : seq_limit u l → seq_limit u l' → l = l'

and from the 6th one:

  subseq_tendsto_of_tendsto (h : seq_limit u l) (hφ : extraction φ) :
    seq_limit (u ∘ φ) l

We now admit the following version of the least upper bound theorem
(that cannot be proved without discussing the construction of real numbers
or admitting another strong theorem).

sup_segment {a b : ℝ} {A : set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ Icc a b) :
  ∃ x ∈ Icc a b, is_sup A x

In the next exercise, it can be useful to prove inclusions of sets of real number.
By definition, A ⊆ B means : ∀ x, x ∈ A → x ∈ B.
Hence one can start a proof of A ⊆ B by `intros x x_in`,
which brings `x : ℝ` and `x_in : x ∈ A` in the local context,
and then prove `x ∈ B`.

Note also the use of 
  {x | P x}
which denotes the set of x satisfying predicate P.

Hence `x' ∈ { x | P x} ↔ P x'`, by definition.
-/

-- 0080
example {a b : ℝ} (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, continuous_at_pt f x) :
∃ x₀ ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f x₀ :=
begin
  -- sorry
  cases bdd_below_segment hf with m hm,
  cases bdd_above_segment hf with M hM,
  let A := {y | ∃ x ∈ Icc a b, y = f x},
  obtain ⟨y₀, y_dans, y_sup⟩ : ∃ y₀ ∈ Icc m M, is_sup A y₀,
  { apply sup_segment,
    { use [f a, a, by linarith, hab, by ring], },
    { rintros y ⟨x, x_in, rfl⟩,
      exact ⟨hm x x_in, hM x x_in⟩ } }, 
  rw is_sup_iff at y_sup,
  rcases y_sup with ⟨y_maj, u, lim_u, u_dans⟩,
  choose v hv using u_dans,
  cases forall_and_distrib.mp hv with v_dans hufv,
  replace hufv : u = f ∘ v := funext hufv,
  rcases bolzano_weierstrass v_dans with ⟨x₀, x₀_in, φ, φ_extr, lim_vφ⟩,
  use [x₀, x₀_in],
  intros x x_dans,
  have lim : seq_limit (f ∘ v ∘ φ) (f x₀),
  { apply seq_continuous_of_continuous,
    exact hf x₀ x₀_in,
    exact lim_vφ },
  have unique : f x₀ = y₀,
  { apply unique_limit lim,
    rw hufv at lim_u,
    exact subseq_tendsto_of_tendsto lim_u φ_extr },
  rw unique,
  apply y_maj,
  use [x, x_dans],
  -- sorry
end

lemma stupid {a b x : ℝ} (h : x ∈ Icc a b) (h' : x ≠ b) : x < b :=
lt_of_le_of_ne h.right h'

/-
And now the final boss...
-/

def I := (Icc 0 1 : set ℝ) -- the type ascription makes sure 0 and 1 are real numbers here

-- 0081
example (f : ℝ → ℝ) (hf : ∀ x, continuous_at_pt f x) (h₀ : f 0 < 0) (h₁ : f 1 > 0) :
∃ x₀ ∈ I, f x₀ = 0 :=
begin
  let A := { x | x ∈ I ∧ f x < 0},
  have ex_x₀ : ∃ x₀ ∈ I, is_sup A x₀,
  {
    -- sorry
    apply sup_segment,
      use 0,
      split,
        split, linarith, linarith,
      exact h₀,
    intros x hx,
    exact hx.left
    -- sorry
  },
  rcases ex_x₀ with ⟨x₀, x₀_in, x₀_sup⟩,
  use [x₀, x₀_in],
  have : f x₀ ≤ 0,
  {
    -- sorry
    rw is_sup_iff at x₀_sup,
    rcases x₀_sup with ⟨maj_x₀, u, lim_u, u_dans⟩,
    have : seq_limit (f ∘ u) (f x₀),
      exact seq_continuous_of_continuous (hf x₀) lim_u,
    apply lim_le this,
    intros n,
    have : f (u n) < 0,
      exact (u_dans n).right,
    linarith
    -- sorry
  },
  have x₀_1: x₀ < 1,
  {
    -- sorry
    apply stupid x₀_in,
    intro h,
    rw ← h at h₁,
    linarith
    -- sorry
  },
  have : f x₀ ≥ 0,
  { have in_I : ∃ N : ℕ, ∀ n ≥ N, x₀ + 1/(n+1) ∈ I,
    { have : ∃ N : ℕ, ∀ n≥ N, 1/(n+1 : ℝ) ≤ 1-x₀,
      {
        -- sorry
        apply inv_succ_le_all,
        linarith,
        -- sorry
      },
      -- sorry
      cases this with N hN,
      use N,
      intros n hn,
      specialize hN n hn,
      have : 1/(n+1 : ℝ) > 0,
        exact nat.one_div_pos_of_nat,
      change 0 ≤ x₀ ∧ x₀ ≤ 1 at x₀_in,
      split ; linarith,
      -- sorry
    },
    have not_in : ∀ n : ℕ, x₀ + 1/(n+1) ∉ A,
    -- By definition, x ∉ A means ¬ (x ∈ A).
    {
      -- sorry
      intros n hn,
      cases x₀_sup with x₀_maj _,
      specialize x₀_maj _ hn,
      have : 1/(n+1 : ℝ) > 0,
        from nat.one_div_pos_of_nat,
      linarith,
      -- sorry
    },
    dsimp [A] at not_in, 
    -- sorry
    push_neg at not_in,
    have lim : seq_limit (λ n, f(x₀ + 1/(n+1))) (f x₀),
    { apply seq_continuous_of_continuous (hf x₀),
      apply limit_const_add_inv_succ },
    apply le_lim lim,
    cases in_I with N hN,
    use N,
    intros n hn,
    exact not_in n (hN n hn),
    -- sorry
  },
  linarith,
end
