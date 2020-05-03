import analysis.specific_limits
import data.int.parity

attribute [instance] classical.prop_decidable

/- 
Lemmas from that file were hidden in my course, or restating things which
were proved without name in previous files.
-/

notation `|`x`|` := abs x

-- The mathlib version is unusable because it is stated in terms of ≤
lemma ge_max_iff {α : Type*} [decidable_linear_order α] {p q r : α} : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

/- No idea why this is not in mathlib-/
lemma eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y :=
begin
  intro h, 
  apply  decidable_linear_ordered_add_comm_group.eq_of_abs_sub_nonpos,
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
  calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')| : by ring
  ... ≤ |l - u (max N N')| + |u (max N N') - l'| : by apply abs_add
  ... =  |u (max N N') - l| + |u (max N N') - l'| : by rw abs_sub
  ... ≤ ε/2 + ε/2 : by linarith
  ... = ε : by ring,
end

def pair (n : ℤ) := ∃ k, n = 2*k

def int.odd (n : ℤ) := ∃ k, n = 2*k + 1

lemma int.not_even_iff_odd {n : ℤ} : ¬ int.even n ↔ int.odd n :=
begin
  rw int.not_even_iff,
  split ; intro h,
  use n/2,
  conv_rhs { rw add_comm, congr, rw ← h },
  exact (int.mod_add_div n 2).symm,
  rcases h with ⟨k, rfl⟩,
  simp [add_comm],
  refl,
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

/- 
lemma limite_infinie_pas_finie {u : ℕ → ℝ} :
  limite_infinie_suite u → ∀ x, ¬ seq_limit u x :=
begin
  -- sorry
  intros lim_infinie x lim_x,
  cases lim_x 1 (by linarith) with N hN,
  cases lim_infinie (x+2) with N' hN',
  let N₀ := max N N',
  specialize hN N₀ (inferieur_max_gauche _ _),
  specialize hN' N₀ (inferieur_max_droite _ _),
  rw abs_inferieur_ssi at hN,
  linarith',
  -- sorry
end -/

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

lemma extraction_machine (ψ : ℕ → ℕ) (hψ : ∀ n, ψ n ≥ n) : ∃ f : ℕ → ℕ, extraction (ψ ∘ f) ∧ ∀ n, f n ≥ n :=
begin
  refine ⟨λ n, nat.rec_on n 0 (λ n ih, ψ ih + 1), λ m n h, _, λ n, _⟩,
  { induction h; dsimp [(∘)],
    { exact hψ _ },
    { exact lt_trans h_ih (hψ _) } },
  { induction n, {apply le_refl},
    exact nat.succ_le_succ (le_trans n_ih (hψ _)) }
end

variables {u : ℕ → ℝ} {l : ℝ} {φ : ℕ → ℕ}

lemma limite_extraction_si_limite (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l :=
begin
  -- sorry
  intros ε ε_pos,
  cases h ε ε_pos with N hN,
  use N,
  intros n hn,
  apply hN,
  calc N ≤ n   : hn 
     ... ≤ φ n : id_le_extraction hφ n, 
  -- sorry
end

def segment (a b : ℝ) := {x | a ≤ x ∧ x ≤ b}

open set filter

def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a

lemma bolzano_weierstrass {a b : ℝ} {u : ℕ → ℝ} (h : ∀ n, u n ∈ Icc a b) :
∃ c ∈ Icc a b, cluster_point u c :=
begin
  have cpct : compact (Icc a b),
    exact compact_Icc,
  have :  map u at_top ≤ principal (Icc a b),
  { change tendsto u _ _,
    rw tendsto_principal,
    filter_upwards [univ_mem_sets],
    intros n hn,
    exact h n },
  rcases cpct (map u at_top) (map_ne_bot at_top_ne_bot) this with ⟨c, h, h'⟩,
  clear this,
  use [c, h],
  unfold cluster_point,
  have : ∀ N, ∃ n ≥ N, |u n -c| ≤ 1/(N+1),
    intro N,
    rw ← forall_sets_nonempty_iff_ne_bot at h',
    specialize h' (u '' {n | n ≥ N} ∩ {x | |x-c| ≤ 1/(N+1)}) _,
    { simp only [set.nonempty,
                set.mem_image,
                set.mem_inter_eq,
                ne.def,
                set.mem_set_of_eq] at h',
      rcases h' with ⟨_, ⟨n, ⟨hn, rfl⟩⟩, ineg⟩,
      use [n, hn, ineg] },
    { apply inter_mem_inf_sets,
      { apply image_mem_map,
        apply mem_at_top },
      { have fact: (0 : ℝ) < 1/(N+2),
          exact_mod_cast (nat.one_div_pos_of_nat : 1/((N+1 : ℕ) + 1 : ℝ) > 0),
        apply mem_sets_of_superset (metric.ball_mem_nhds c fact),
        intros x x_in,
        rw [metric.mem_ball, real.dist_eq] at x_in,
        exact le_of_lt (
          calc |x - c| < 1 / (N + 2) : x_in
                   ... = 1/((N+1)+1) : by { congr' 1, norm_cast }
                   ... ≤ 1 / (N + 1) : nat.one_div_le_one_div (nat.le_succ N)),

       } },
  choose ψ hψ using this,
  cases forall_and_distrib.mp hψ with hψ_id hψ', clear hψ,
  rcases extraction_machine ψ hψ_id with ⟨f, hf, hf'⟩,
  use [ψ ∘ f, hf],
  apply limit_of_sub_le_inv_succ,
  intros n,
  transitivity 1/(f n + 1 : ℝ),
  apply hψ',
  exact nat.one_div_le_one_div (hf' n),
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
    apply real.le_Sup,
    use [b, b_maj] } ,
  refine ⟨Sup A, _, _⟩,
  { split,
    { cases hnonvide with x x_in,
      exact le_trans (h x_in).1 (Sup_maj _ x_in) },
    { apply Sup_le_ub A hnonvide b_maj } },
  { use Sup_maj,
    intros y y_in,
    rwa real.Sup_le _ hnonvide ⟨b, b_maj⟩ },
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
   done } <|> fail "Ce n'est pas cela. Essayez encore." ]

end tactic.interactive