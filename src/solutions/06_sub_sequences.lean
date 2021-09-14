import tuto_lib
/-
This file continues the elementary study of limits of sequences. 
It can be skipped if the previous file was too easy, it won't introduce
any new tactic or trick.

Remember useful lemmas:

abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_sub_comm (x y : ℝ) : |x - y| = |y - x|

ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

and the definition:

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

You can also use a property proved in the previous file:

unique_limit : seq_limit u l → seq_limit u l' → l = l'

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m
-/


variable { φ : ℕ → ℕ}

/-
The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete 
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n :=
begin
  intros hyp n,
  induction n with n hn,
  { exact nat.zero_le _ },
  { exact nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)]) },
end

/-- Extractions take arbitrarily large values for arbitrarily large 
inputs. -/
-- 0039
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  -- sorry
  intros h N N',
  use max N N',
  split,
  apply le_max_right,
  calc
    N ≤ max N N'     : by apply le_max_left
  ... ≤ φ (max N N') : by apply id_le_extraction' h
  -- sorry
end

/-- A real number `a` is a cluster point of a sequence `u` 
if `u` has a subsequence converging to `a`. 

def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a
-/

variables {u : ℕ → ℝ} {a l : ℝ}

/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
Lean can read this abbreviation, but displays it as the confusing:
`∃ (n : ℕ) (H : n ≥ N)`
One gets used to it. Alternatively, one can get rid of it using the lemma
  exists_prop {p q : Prop} : (∃ (h : p), q) ↔ p ∧ q
-/

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
-- 0040
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  -- sorry
  intros hyp ε ε_pos N,
  rcases hyp with ⟨φ, φ_extr, hφ⟩,
  cases hφ ε ε_pos with N' hN',
  rcases extraction_ge φ_extr N N' with ⟨q, hq, hq'⟩,
  exact ⟨φ q, hq', hN' _ hq⟩,
  -- sorry
end

/-
The above exercice can be done in five lines. 
Hint: you can use the anonymous constructor syntax when proving
existential statements.
-/

/-- If `u` tends to `l` then its subsequences tend to `l`. -/
-- 0041
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l :=
begin
  -- sorry
  intros ε ε_pos,
  cases h ε ε_pos with N hN,
  use N,
  intros n hn,
  apply hN,
  calc N ≤ n   : hn 
     ... ≤ φ n : id_le_extraction' hφ n, 
  -- sorry
end

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
-- 0042
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l :=
begin
  -- sorry
  rcases ha with ⟨φ, φ_extr, lim_u_φ⟩,
  have lim_u_φ' : seq_limit (u ∘ φ) l,
    from subseq_tendsto_of_tendsto' hl φ_extr,
  exact unique_limit lim_u_φ lim_u_φ',
  -- sorry
end

/-- Cauchy_sequence sequence -/
def cauchy_sequence (u : ℕ → ℝ) := ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

-- 0043
example : (∃ l, seq_limit u l) → cauchy_sequence u :=
begin
  -- sorry
  intro hyp,
  cases hyp with l hl,
  intros ε ε_pos,
  cases hl (ε/2) (by linarith) with N hN,
  use N,
  intros p q hp hq,
  calc |u p - u q| = |(u p - l) + (l - u q)| : by ring_nf
  ... ≤ |u p - l| + |l - u q| : by apply abs_add
  ... =  |u p - l| + |u q - l| : by rw abs_sub_comm (u q) l
  ... ≤ ε : by linarith [hN p hp, hN q hq],
  -- sorry
end


/- 
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/
-- 0044
example (hu : cauchy_sequence u) (hl : cluster_point u l) : seq_limit u l :=
begin
  -- sorry
  intros ε ε_pos,
  cases hu (ε/2) (by linarith) with N hN,
  use N,
  have clef : ∃ N' ≥ N, |u N' - l| ≤ ε/2,
    apply near_cluster hl (ε/2) (by linarith),
  cases clef with N' h,
  cases h with hNN' hN',
  intros n hn,
  calc |u n - l| = |(u n - u N') + (u N' - l)| : by ring
  ... ≤ |u n - u N'| + |u N' - l| : by apply abs_add
  ... ≤ ε : by linarith [hN n N' (by linarith) hNN'],
  -- sorry
end
