import ..untranslated.my_lib

/-
Cette feuille continue l'étude du chapitre 2 du cours de math 101, en abordant
les suites extraites, les valeurs d'adhérence et les suites de Cauchy.
Il n'y a aucun nouvelle commande Lean à apprendre. Cependant les
exercices sont globalement un peu plus difficiles mathématiquement que dans
la feuille 5. Il est donc inutile de travailler cette feuille si la
feuille 5 n'est pas solidement comprise.

On rappelle des lemmes potentiellement utiles :

abs_le (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_sub (x y : ℝ) : |x - y| = |y - x|

superieur_max_ssi (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

On rappelle aussi la définition de « u tend vers l »
def limite_suite (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

et le lemme d'unicité de la limite démontré dans la feuille 5 :

unicite_limite : limite_suite u l → limite_suite u l' → l = l'
-/

/-- Une fonction `φ : ℕ → ℕ` est une extraction si elle est
strictement croissante. -/
def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

-- Dans la suite, φ désignera toujours une fonction de ℕ dans ℕ
variable { φ : ℕ → ℕ}

/-
On pourra utiliser le lemme suivant dont la démonstration est une récurrence
immédiate (mais nous n'avons pas encore vu comment faire des démonstrations
par récurrence avec Lean).
-/

/-- Toute extraction est supérieure à l'identité. -/
lemma extraction_superieur_id : extraction φ → ∀ n, n ≤ φ n :=
begin
  intros hyp n,
  induction n with n hn,
    exact nat.zero_le _,
  exact nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)]),
end

/-- Si `φ` est une extraction alors elle prend des valeurs
 arbitrairement grandes pour des indices arbitrairement grands. -/
lemma extraction_superieur : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  -- sorry
  intros h N N',
  use max N N',
  split,
  apply le_max_right,
  calc
    N ≤ max N N'     : by apply le_max_left
  ... ≤ φ (max N N') : by apply extraction_superieur_id h
  -- sorry
end

/-- Un réel `a` est valeur d'adhérence d'une suite `u` s'il
existe une suite extraite de `u` qui tend vers `a`. -/
def valeur_adherence (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ limite_suite (u ∘ φ) a

-- Dans la suite u désigne une suite de réels, et a et l sont des réels
variables {u : ℕ → ℝ} {a l : ℝ}

/-
Dans l'exercice suivant, on note l'utilisation de l'abréviation
« ∃ n ≥ N, ... » qui signifie « ∃ n, n ≥ N et ...».
Lean lit très bien cette abbréviation mais à tendence à l'afficher
sous la forme « ∃ (n : ℕ) (H : n ≥ N) » qui est un peu perturbante
au début, il faut s'y habituer.
-/

/-- Si `a` est valeur d'adhérence de `u` alors il existe des valeurs
de `u` aussi proche qu'on veut de `a` pour des indices aussi grands qu'on veut. -/
lemma valeur_proche_adherence :
  valeur_adherence u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  -- sorry
  intros hyp ε ε_pos N,
  cases hyp with φ h,
  cases h with φ_extr hφ,
  cases hφ ε ε_pos with N' hN',
  cases extraction_superieur φ_extr N N' with q hq,
  cases hq with hq hq',
  use φ q,
  split,
    exact hq',
  apply hN',
  exact hq,
  -- sorry
end

/-- Si `u` tend vers `l` alors toutes ses suites extraites tendent vers `l`. -/
lemma limite_extraction_si_limite (h : limite_suite u l) (hφ : extraction φ) :
limite_suite (u ∘ φ) l :=
begin
  -- sorry
  intros ε ε_pos,
  cases h ε ε_pos with N hN,
  use N,
  intros n hn,
  apply hN,
  calc N ≤ n   : hn -- on peut écrire « by exact hn » si on a un clavier solide
     ... ≤ φ n : extraction_superieur_id hφ n, -- idem
  -- sorry
end

/-- Si une suite `u` qui tend vers `l` alors elle n'a pas d'autre valeur
d'adhérence que `l`. -/
lemma val_adh_lim (hl : limite_suite u l) (ha : valeur_adherence u a) : a = l :=
begin
  -- sorry
  cases ha with φ h,
  cases h with φ_extr lim_u_φ,
  have lim_u_φ' : limite_suite (u ∘ φ) l,
    exact limite_extraction_si_limite hl φ_extr,
  exact unicite_limite lim_u_φ lim_u_φ',
  /- Variante avec apply.
  Difficulté : après le apply, Lean ne sait pas à quelle suite on veut appliquer
  le lemme d'unicité (comment saurait-il ?). Il crée donc un trou ?m_1
  et demande deux hypothèses de limite, en gardant le bouchage du trou pour la
  fin, dans le secret espoir de l'avoir bouché par unification entre temps.
  C'est effectivement ce qui se passe dès la ligne suivante.

  cases ha with φ h,
  cases h with φ_extr lim_u_φ,
  apply unicite_limite,
  exact lim_u_φ,
  exact limite_extraction_si_limite hl φ_extr,
  -/
  -- sorry
end

/-- Une suite `u` est de Cauchy si ses termes sont aussi proches qu'on
veut pour des indices assez grands. -/
def cauchy (u : ℕ → ℝ) := ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

/-- Si une suite `u` converge alors elle est de Cauchy. -/
lemma cauchy_si_converge : (∃ l, limite_suite u l) → cauchy u :=
begin
  -- sorry
  intro hyp,
  cases hyp with l hl,
  intros ε ε_pos,
  cases hl (ε/2) (by linarith) with N hN,
  use N,
  intros p q hp hq,
  have hup : |u p - l| ≤ ε/2,
    exact hN p hp,
  have huq : |u q - l| ≤ ε/2,
    exact hN q hq,
  calc |u p - u q| = |(u p - l) + (l - u q)| : by ring
  ... ≤ |u p - l| + |l - u q| : by apply abs_add
  ... =  |u p - l| + |u q - l| : by rw abs_sub (u q) l
  ... ≤ ε/2 + ε/2 : by linarith
  ... = ε : by ring,
  -- sorry
end


/- Dans l'exercice suivant, on pourra utiliser valeur_proche_adherence
  démontré plus haut et dont on rappelle l'énoncé :

valeur_adherence u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

/-- Si une suite de Cauchy `u` admet une valeur d'adhérence `l` alors elle
converge vers `l`. -/
example (hu : cauchy u) (hl : valeur_adherence u l) : limite_suite u l :=
begin
  -- sorry
  intros ε ε_pos,
  cases hu (ε/2) (by linarith) with N hN,
  use N,
  have clef : ∃ N' ≥ N, |u N' - l| ≤ ε/2,
    apply valeur_proche_adherence hl (ε/2) (by linarith),
  cases clef with N' h,
  cases h with hNN' hN',
  intros n hn,
  specialize hN n N' (by linarith) hNN',
  calc |u n - l| = |(u n - u N') + (u N' - l)| : by ring
  ... ≤ |u n - u N'| + |u N' - l| : by apply abs_add
  ... ≤ ε/2 + ε/2 : by linarith
  ... = ε : by ring,
  -- sorry
end
