import analysis.specific_limits.basic
import data.int.parity
import topology.sequences

attribute [instance] classical.prop_decidable

/- 
Lemmas from that file were hidden in my course, or restating things which
were proved without name in previous files.
-/

notation `|`x`|` := abs x

-- The mathlib version is unusable because it is stated in terms of ≤
lemma ge_max_iff {α : Type*} [linear_order α] {p q r : α} : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

/- No idea why this is not in mathlib-/
lemma eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y :=
begin
  intro h, 
  apply eq_of_abs_sub_nonpos,
  by_contradiction H,
  push_neg at H,
  specialize h ( |x-y|/2) (by linarith),
  linarith,
end

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

lemma unique_limit {u l l'} : seq_limit u l → seq_limit u l' → l = l' :=
begin
  intros hl hl',
  apply eq_of_abs_sub_le_all,
  intros ε ε_pos,
  specialize hl (ε/2) (by linarith),
  cases hl with N hN,
  specialize hl' (ε/2) (by linarith),
  cases hl' with N' hN',
  specialize hN (max N N') (le_max_left _ _),
  specialize hN' (max N N') (le_max_right _ _),
  calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')| : by ring_nf
  ... ≤ |l - u (max N N')| + |u (max N N') - l'| : by apply abs_add
  ... = |u (max N N') - l| + |u (max N N') - l'| : by rw abs_sub_comm
  ... ≤ ε/2 + ε/2 : by linarith
  ... = ε : by ring,
end

lemma le_of_le_add_all {x y : ℝ} :
  (∀ ε > 0, y ≤ x + ε) →  y ≤ x :=
begin
  contrapose!,
  intro h,
  use (y-x)/2,
  split ; linarith,
end

def upper_bound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x

def is_sup (A : set ℝ) (x : ℝ) := upper_bound A x ∧ ∀ y, upper_bound A y → x ≤ y

lemma lt_sup {A : set ℝ} {x : ℝ} (hx : is_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intro y,
  contrapose!,
  exact hx.right y,
end

lemma squeeze {u v w : ℕ → ℝ} {l} (hu : seq_limit u l) (hw : seq_limit w l)
(h : ∀ n, u n ≤ v n)
(h' : ∀ n, v n ≤ w n) : seq_limit v l :=
begin
  intros ε ε_pos,
  cases hu ε ε_pos with N hN,
  cases hw ε ε_pos with N' hN',
  use max N N',
  intros n hn,
  rw ge_max_iff at hn,
  specialize hN n (by linarith),
  specialize hN' n (by linarith),
  specialize h n,
  specialize h' n,
  rw abs_le at *,
  split ; linarith
end

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

def tendsto_infinity (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

lemma lim_le {x y : ℝ} {u : ℕ → ℝ} (hu : seq_limit u x)
  (ineg : ∀ n, u n ≤ y) : x ≤ y :=
begin
  apply le_of_le_add_all,
  intros ε ε_pos,
  cases hu ε ε_pos with N hN,
  specialize hN N (by linarith),
  specialize ineg N,
  rw abs_le at hN,
  linarith,
end

lemma inv_succ_le_all :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε :=
begin
  convert metric.tendsto_at_top.mp (tendsto_one_div_add_at_top_nhds_0_nat),
  apply propext,
  simp only [real.dist_eq, sub_zero],
  split,
    intros h ε ε_pos,
    cases h (ε/2) (by linarith) with N hN,
    use N,
    intros n hn,
    rw abs_of_pos (nat.one_div_pos_of_nat : 1/(n+1 : ℝ) > 0),
    specialize hN n hn,
    linarith,
  intros h ε ε_pos,
  cases h ε (by linarith) with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  rw abs_of_pos (@nat.one_div_pos_of_nat ℝ _ n) at hN,
  linarith,
end

lemma limit_const (x : ℝ) : seq_limit (λ n, x) x :=
λ ε ε_pos, ⟨0, λ _ _, by simp [le_of_lt ε_pos]⟩

lemma limit_of_sub_le_inv_succ {u : ℕ → ℝ} {x : ℝ} (h : ∀ n, |u n - x| ≤ 1/(n+1)) :
seq_limit u x :=
begin
  intros ε ε_pos,
  rcases inv_succ_le_all ε ε_pos with ⟨N, hN⟩,
  use N,
  intros n hn,
  specialize h n,
  specialize hN n hn,
  linarith,
end

lemma limit_const_add_inv_succ (x : ℝ) : seq_limit (λ n, x + 1/(n+1)) x :=
limit_of_sub_le_inv_succ (λ n, by rw abs_of_pos ; linarith [@nat.one_div_pos_of_nat ℝ _ n])

lemma limit_const_sub_inv_succ (x : ℝ) : seq_limit (λ n, x - 1/(n+1)) x :=
begin
  refine limit_of_sub_le_inv_succ (λ n, _),
  rw [show x - 1 / (n + 1) - x = -(1/(n+1)), by ring, abs_neg,  abs_of_pos],
  linarith [@nat.one_div_pos_of_nat ℝ _ n]
end

lemma id_le_extraction {φ}: extraction φ → ∀ n, n ≤ φ n :=
begin
  intros hyp n,
  induction n with n hn,
  { exact nat.zero_le _ },
  { exact nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)]) },
end

lemma seq_limit_id : tendsto_infinity (λ n, n) :=
begin
  intros A,
  cases exists_nat_gt A with N hN,
  use N,
  intros n hn,
  have : (n : ℝ) ≥ N, exact_mod_cast hn, 
  linarith,
end

variables {u : ℕ → ℝ} {l : ℝ} {φ : ℕ → ℕ}

open set filter

def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

lemma bolzano_weierstrass {a b : ℝ} {u : ℕ → ℝ} (h : ∀ n, u n ∈ Icc a b) :
∃ c ∈ Icc a b, cluster_point u c :=
begin
  rcases (is_compact_Icc : is_compact (Icc a b)).tendsto_subseq h with ⟨c, c_in, φ, hφ, lim⟩,
  use [c, c_in, φ, hφ],
  simp_rw [metric.tendsto_nhds, eventually_at_top, real.dist_eq] at lim,
  intros ε ε_pos,
  rcases lim ε ε_pos with ⟨N, hN⟩,
  use N,
  intros n hn,
  exact le_of_lt (hN n hn)
end

lemma not_seq_limit_of_tendstoinfinity {u : ℕ → ℝ} :
  tendsto_infinity u → ∀ x, ¬ seq_limit u x :=
begin
  intros lim_infinie x lim_x,
  cases lim_x 1 (by linarith) with N hN,
  cases lim_infinie (x+2) with N' hN',
  let N₀ := max N N',
  specialize hN N₀ (le_max_left _ _),
  specialize hN' N₀ (le_max_right _ _),
  rw abs_le at hN,
  linarith,
end

open real 

lemma sup_segment {a b : ℝ} {A : set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ Icc a b) :
  ∃ x ∈ Icc a b, is_sup A x :=
begin
  have b_maj :  ∀ (y : ℝ), y ∈ A → y ≤ b,
    from λ y y_in, (h y_in).2,
  have Sup_maj : upper_bound A (Sup A),
  { intro x,
    apply le_cSup,
    use [b, b_maj] } ,
  refine ⟨Sup A, _, _⟩,
  { split,
    { cases hnonvide with x x_in,
      exact le_trans (h x_in).1 (Sup_maj _ x_in) },
    { apply cSup_le hnonvide b_maj } },
  { exact ⟨Sup_maj, λ y, cSup_le hnonvide⟩ },
end

lemma subseq_tendsto_of_tendsto (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l :=
begin
  intros ε ε_pos,
  cases h ε ε_pos with N hN,
  use N,
  intros n hn,
  apply hN,
  calc N ≤ n   : hn 
     ... ≤ φ n : id_le_extraction hφ n, 
end
namespace tactic.interactive
open tactic

meta def check_me : tactic unit :=
`[ { repeat { unfold seq_limit},
   repeat { unfold continue_en },
   push_neg,
   try { simp only [exists_prop] },
   try { exact iff.rfl },
   done } <|> fail "That's not quite right. Please try again." ]

end tactic.interactive
