import ..untranslated.my_lib
import algebra.pi_instances
import algebra.ordered_group

/-
Ce fichier concerne la définition de limite d'une suite (de nombres réels).
Une suite u est une fonction de ℕ dans ℝ, Lean écrit donc u : ℕ → ℝ
-/


/-
On notera dans la définition ci-dessus l'utilisation de « ∀ ε > 0, ... »
qui est une abbréviation de « ∀ ε, ε > 0 → ... ».

En particulier un énoncé de la forme « h : ∀ ε > 0, ... » se spécialise à
un ε₀ fixé par la commande « specialize h ε₀ hε₀ » où hε₀ est une démonstration
de ε₀ > 0.

Astuce : partout où Lean attend une hypothèse, on peut commencer une
démonstration à l'aide du mot clef « by », suivie de la démonstration (entourée
d'accolades si elle comporte plusieurs commandes).
Par exemple, si le contexte contient

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, ...

on peut spécialiser l'énoncé quantifié h au réel δ/2 en tapant
specialize h (δ/2) (by linarith)
où « by linarith » fournit la démonstration de δ/2 > 0 attendue par Lean.
-/

-- Dans toute la suite, u, v et w sont des suites tandis que l et l' sont des
-- nombres réels
variables (u v w : ℕ → ℝ) (l l' : ℝ)

-- Si u est constante de valeur l, alors u tend vers l
example : (∀ n, u n = l) → limite_suite u l :=
begin
  -- sorry
  intros h ε ε_pos,
  use 0,
  intros n hn,
  rw h,
  simp,
  linarith,
  -- sorry
end

/- Concernant les valeurs absolues, on pourra utiliser les lemmes

abs_le (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_sub (x y : ℝ) : |x - y| = |y - x|

Il est conseillé de noter ces lemmes sur une feuille car ils
peuvent être utiles dans chaque exercice.
-/

-- Si u tend vers l strictement positif, alors u n ≥ l/2 pour n assez grand.
example (hl : l > 0) : limite_suite u l → ∃ N, ∀ n ≥ N, u n ≥ l/2 :=
begin
  -- sorry
  -- Supposons que u tend vers l
  intro h,
  -- Comme l/2 > 0, on obtient N tel que  ∀ n ≥ N, |u n - l| ≤ l / 2
  cases h (l/2) (by linarith) with N hN,
  -- Montrons que ce N convient.
  use N,
  -- Soit n un entier supérieur à N,
  intros n hn,
  -- de sorte que |u n - l| ≤ l/2,
  specialize hN n hn,
  -- c'est à dire -(l/2) ≤ u n - l  ≤ l/2.
  rw abs_le at hN,
  linarith,
  -- sorry
end

/- Concernant le maximum de deux nombres, on pourra utiliser les lemmes

superieur_max_ssi (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

Il est conseillé de noter ces lemmes sur une feuille car ils
peuvent être utiles dans chaque exercice.
-/


-- Si u tend vers l et v tend vers l' alors u+v tend vers l+l'
example (hu : limite_suite u l) (hv : limite_suite v l') :
limite_suite (u + v) (l + l') :=
begin
  -- Soit ε un réel strictement positif
  intros ε ε_pos,
  -- L'hypothèse de limite sur u, appliquée au réel strictement positif ε/2,
  -- fournit un entier N₁ tel ∀ n ≥ N₁, |u n - l| ≤ ε / 2
  cases hu (ε/2) (by linarith) with N₁ hN₁,
  -- L'hypothèse de limite sur v, appliquée au réel strictement positif ε/2,
  -- fournit un entier N₂ tel ∀ n ≥ N₂, |v n - l| ≤ ε / 2
  cases hv (ε/2) (by linarith) with N₂ hN₂,
  -- On veut un entier N tel que ∀ n ≥ N, |(u+v) n - (l+l')| ≤ ε
  -- Montrons que max N₁ N₂ convient.
  use max N₁ N₂,
  -- Soit n ≥ max N₁ N₂
  intros n hn,
  -- Par définition du max, n ≥ N₁ et n ≥ N₂
  rw superieur_max_ssi at hn,
  cases hn with hn₁ hn₂,
  -- Donc |u n - l| ≤ ε/2
  have fait₁ : |u n - l| ≤ ε/2,
    apply hN₁,
    linarith,
  -- et |v n - l| ≤ ε/2
  have fait₂ : |v n - l'| ≤ ε/2,
    exact hN₂ n (by linarith),  -- Notez la variante Lean par rapport à fait₁
  -- On peut alors calculer.
  calc
  |(u + v) n - (l + l')| = |(u n -l) + (v n -l')| : by abel
                     ... ≤ |u n - l| + |v n - l'| : by apply abs_add
                     ... ≤  ε/2 + ε/2             : by linarith
                     ... =  ε                     : by ring,
end

example (hu : limite_suite u l) (hw : limite_suite w l)
(h : ∀ n, u n ≤ v n)
(h' : ∀ n, v n ≤ w n) : limite_suite v l :=
begin
  -- sorry
  intros ε ε_pos,
  cases hu ε ε_pos with N hN,
  cases hw ε ε_pos with N' hN',
  use max N N',
  intros n hn,
  rw superieur_max_ssi at hn,
  cases hn with hn hn',
  specialize hN n (by linarith),
  specialize hN' n (by linarith),
  specialize h n,
  specialize h' n,
  rw abs_le at *,
  cases hN with hNl hNd,
  cases hN' with hN'l hN'd,
  split,
  -- Ici linarith peut finir, mais sur papier on écrirait
  calc -ε ≤ u n - l : by linarith
      ... ≤ v n - l : by linarith,
  calc v n - l ≤ w n - l : by linarith
      ... ≤ ε : by linarith,
  -- sorry

end

-- La dernière inégalité dans la définition de limite peut être remplacée par
-- une inégalité stricte.
example (u l) : limite_suite u l ↔
 ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε :=
begin
  -- sorry
  split,
    intros hyp ε ε_pos,
    cases hyp (ε/2) (by linarith) with N hN,
    use N,
    intros n hn,
    calc |u n - l| ≤ ε/2 : by exact hN n hn
              ...  < ε   : by linarith,

  intros hyp ε ε_pos,
  cases hyp ε ε_pos with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  linarith,
  -- sorry
end

/- Dans l'exercice suivant, on pourra utiliser le lemme

egal_si_abs_eps (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y
-/

-- Une suite u admet au plus une limite
example : limite_suite u l → limite_suite u l' → l = l' :=
begin
  -- sorry
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
  /- Alternative en faisant disparaître les valeurs absolues
  rw abs_le at *,
  cases hN, cases hN',
  split,
  linarith,
  linarith, -/
  -- sorry
end

-- Définition de « la suite u est croissante »
def croissante (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

-- Définition de « M est borne supérieure des termes de la suite u  »
def est_borne_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

-- Toute suite croissante ayant une borne supérieure tend vers cette borne
example (M : ℝ) (h : est_borne_sup M u) (h' : croissante u) :
limite_suite u M :=
begin
  -- sorry
  intros ε ε_pos,
  cases h with inf_M sup_M_ep,
  cases sup_M_ep ε ε_pos with n₀ hn₀,
  use n₀,
  intros n hn,
  specialize inf_M n,
  specialize h' n₀ n hn,
  rw abs_le,
  split,
  linarith,
  linarith,
  -- sorry
end
