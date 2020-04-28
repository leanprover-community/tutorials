import ..untranslated.my_lib

set_option pp.beta true
set_option pp.coercions false

/-
Le bouquet final

Cette feuille utilise tout le cours de Math 114 pour démontrer de nombreux
théorèmes parmi les plus subtils de Math 101 : la caractérisation
séquentielle des bornes supérieures, l'équivalence entre continuité
séquentielle et continuité, le fait que toute fonction continue sur un segment
est majorée et atteint son maximum, et enfin le théorème des valeurs
intermédiaires.

Il est inutile d'aborder cette feuille sans être à l'aise avec les feuilles
précédentes (à l'exception de la feuille 7bis facultative). Réviser les
feuilles précédentes et poser des questions est toujours une bonne idée.

On commence par un échauffement, une variante du

  lim_le (hu : limite_suite u x) (ineg : ∀ n, u n ≤ y) : x ≤ y

de la feuille 8, avec l'autre inégalité et seulement à partir d'un certain rang.

On rappelle qu'on a la commande linarith' qui est une version légèrement
améliorée de linarith (cf. feuille 8).

On pourra aussi utiliser les lemmes habituels :

  abs_le (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

  superieur_max_ssi (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

  le_max_left p q : p ≤ max p q

  le_max_right p q : q ≤ max p q

ainsi que le lemme

  inferieur_si_inferieur_plus_eps : (∀ ε > 0, y ≤ x + ε) →  y ≤ x

démontré dans la feuille 8
-/

-- Si u tend vers x et y ≤ u_n pour n assez grand n alors y ≤ x.
lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : limite_suite u x)
  (ineg : ∃ N, ∀ n ≥ N, y ≤ u n) : y ≤ x :=
begin
  -- sorry
  apply inferieur_si_inferieur_plus_eps,
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
Le premier objectif sérieux de cette feuille est de démontrer la caractérisation
séquentielle des bornes supérieures. Pour cela, et pour les objectifs suivants,
nous aurons besoin de pas mal de choses des feuilles précédentes, et de
quelques extras.

Nous avons démontré dans la feuille 5 qu'une suite constante converge vers
sa valeur :

  lim_constante (x : ℝ) : limite_suite (λ n, x) x

et le théorème des gendarmes :

  gendarmes (lim_u : limite_suite u l) (lim_w : limite_suite w l)
    (hu : ∀ n, u n ≤ v n) (hw : ∀ n, v n ≤ w n)  : limite_suite v l

Dans la feuille 8, nous avons introduit les deux définitions :

  Le réel x est un majorant de l'ensemble de réels A :
  def majorant (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x

  Le réel x est une  borne supérieure de l'ensemble de réels A :
  def borne_sup (A : set ℝ) (x : ℝ) := majorant A x ∧ ∀ y, majorant A y → x ≤ y

et montré que si un réel x est borne supérieure d'un ensemble de réels A alors,
pour tout y, si y < x alors il existe a dans A strictement plus grand que y.

  lt_sup (hx : borne_sup A x) : ∀ y, y < x → ∃ a ∈ A, y < a :=

Dans les exercices suivants, on pourra aussi utiliser les lemmes

  inv_succ_pos : ∀ n : ℕ, 1/(n + 1 : ℝ) > 0

  limite_inv_succ :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε

et les conséquences faciles suivantes de limite_inv_succ :

  limite_si_inferieur_un_sur (h : ∀ n, |u n - x| ≤ 1/(n+1)) : limite_suite u x

  lim_plus_un_sur (x : ℝ) : limite_suite (λ n, x + 1/(n+1)) x

  lim_moins_un_sur (x : ℝ) : limite_suite (λ n, x - 1/(n+1)) x

La structure de la démonstration est offerte. Les accolades servent à
délimiter les objectifs intermédiaires, tout en faisant provisoirement
disparaître l'affichage des objectifs en attente. Il ne faut surtout pas
les supprimer, sous peine de se perdre irrémédiablement.

Enfin on notera l'apparition dans la structure de démonstration ci-dessous
de la commande « choose ». Cette commande est décrite dans la dernière section
du chapitre 3 du cours, intitulée « Utilisation d'un ∀x, ∃y et axiome du choix »
(qu'il convient donc de relire ou de lire), mais n'était pas encore apparue
dans les exercices.
-/

-- Un réel x est borne supérieure d'un ensemble de réels A ssi il est
-- majorant de A et il existe une suite d'éléments de A qui tend vers x.
lemma borne_sup_ssi (A : set ℝ) (x : ℝ) :
(borne_sup A x) ↔ (majorant A x ∧ ∃ u : ℕ → ℝ, limite_suite u x ∧ ∀ n, u n ∈ A ) :=
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
          exact inv_succ_pos n,
        -- sorry
        exact lt_sup h _ (by linarith),
        -- sorry
      },
      choose u hu using this,
      -- sorry
      use u,
      split,
      { apply gendarmes (lim_moins_un_sur x) (lim_constante x),
        { intros n,
          exact le_of_lt (hu n).2, },
        { intro n,
          exact h.1 _ (hu n).left, } },
      { intro n,
        exact (hu n).left },
      -- sorry
  } },
  { rintro ⟨maj, u, limu, u_in⟩, -- Cette syntaxe regroupe intro et trois cases :
  -- intro h, cases h with maj min, cases min with u hu, cases hu with limu u_in,
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

/-
Les autres exercices de cette feuille utiliseront la définition de la
continuité d'une fonction de ℝ dans ℝ en un point de ℝ.
-/

/-- La fonction `f` est continue en `x₀`. -/
def continue_en (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

-- Dans la suite, f désignera une fonction de ℝ dans ℝ, x₀ un réel et u
-- une suite de réels
variables {f : ℝ → ℝ} {x₀ : ℝ} {u : ℕ → ℝ}

/-
On commence par un échauffement concernant définition de la continuité.
-/

/-- Une fonction continue en x₀ est séquentiellement continue en x₀ -/
lemma seq_continue_si_continue (hf : continue_en f x₀)
  (hu : limite_suite u x₀) : limite_suite (f ∘ u) (f x₀) :=
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

/-
La réciproque de du lemme précédent est vraie aussi :
La continuité séquentielle en x₀ implique la continuité en x₀.
Mais la démonstration est moins courte. On pourra s'inspirer de
la démonstration de borne_sup_ssi (et du poly de math 101 !).
-/
example :
  (∀ u : ℕ → ℝ, limite_suite u x₀ → limite_suite (f ∘ u) (f x₀)) →
  continue_en f x₀ :=
begin
  -- sorry
  contrapose!,
  intro hf,
  unfold continue_en at hf,
  push_neg at hf,
  cases hf with ε h,
  cases h with ε_pos hf,
  have H : ∀ n : ℕ, ∃ x, |x - x₀| ≤ 1/(n+1) ∧ ε < |f x - f x₀|,
    intro n,
    apply hf,
    exact inv_succ_pos n,
  clear hf,
  choose u hu using H,
  use u,
  split,
    intros η η_pos,
    have fait : ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → 1 / (↑n + 1) ≤ η,
      exact limite_inv_succ η η_pos,
    cases fait with N hN,
    use N,
    intros n hn,
    calc |u n - x₀| ≤ 1/(n+1) : (hu n).left
                ... ≤ η       : hN n hn,
  unfold limite_suite,
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
Dans la suite, étant donnés deux réels,
on utilise la notation habituelle [a, b] pour désigner le segment [a, b].
Attention, si par malheur b < a alors ce segment est vide. C'est un peu
une question de convention, mais notre définition d'un segment assure le
lemme suivant (dont l'utilisation est rarement nécessaire vu qu'il ne fait que
déplier une définition).
-/

lemma dans_segment {a b x : ℝ}  : x ∈ [a, b] ↔ a ≤ x ∧ x ≤ b :=
iff.rfl -- cette ligne signifie : « C'est équivalent par définition. »

/-
Nous avons vu dans la feuille 6 les définitions et le lemme :

Une extraction est une fonction strictement croissante de ℕ dans ℕ :

  def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

Un réel a est valeur d'adhérence d'une suite u s'il
existe une suite extraite de u qui tend vers a.

  def valeur_adherence (u : ℕ → ℝ) (a : ℝ) :=
    ∃ φ, extraction φ ∧ limite_suite (u ∘ φ) a

Toute extraction est supérieure à l'identité :

  extraction_superieur_id : extraction φ → ∀ n, n ≤ φ n

Et dans la feuille 8 la définition et le lemme :

La suite u tend vers +∞.

  def limite_infinie_suite (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

Si u tend vers +∞ alors u ne tend vers aucune limite finie

  limite_infinie_pas_finie : limite_infinie_suite u → ∀ l, ¬ limite_suite u l
-/

-- Dans la suite, φ sera une fonction de ℕ dans ℕ
variables {φ : ℕ → ℕ}


/-- Si `u` tend vers `+∞` alors toutes ses suites extraites tendent vers `+∞`. -/
lemma limite_infinie_extraction_si_limite
  (h : limite_infinie_suite u) (hφ : extraction φ) :
limite_infinie_suite (u ∘ φ) :=
begin
  -- sorry
  intros A,
  cases h A with N hN,
  use N,
  intros n hn,
  apply hN,
  calc N ≤ n   : hn
     ... ≤ φ n : extraction_superieur_id hφ n,
  -- sorry
end

lemma limite_infinie_gendarme {u v : ℕ → ℝ} (hu : limite_infinie_suite u)
(huv : ∀ n, u n ≤ v n) : limite_infinie_suite v :=
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
Dans la suite, on pourra aussi utiliser le théorème de Bolzano-Weirstrass :

Toute suite à valeur dans un segment [a, b] admet une valeur d'adhérence
dans [a, b].

  bolzano_weierstrass (h : ∀ n, u n ∈ [a, b]) :
    ∃ c ∈ [a, b], valeur_adherence u c

Ce théorème se démontre à partir du théorème de la borne supérieure, mais il
faut construire une suite par récurrence, ce que nous n'avons pas appris à
faire dans Lean.

On pourra utiliser aussi le lemme suivant, qui lui est évident

  limite_suite_id : limite_infinie_suite (λ n, n)
-/

-- Toute fonction continue sur un segment y est majorée.
lemma majoree_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ [a, b], continue_en f x) :
∃ M, ∀ x ∈ [a, b], f x ≤ M :=
begin
  -- sorry
  by_contradiction H,
  push_neg at H,
  have clef : ∀ n : ℕ, ∃ x, x ∈ [a, b] ∧ f x > n,
    intro n, apply H, clear H,
  choose u hu using clef,
  have lim_infinie : limite_infinie_suite (f ∘ u),
    apply limite_infinie_gendarme (limite_suite_id),
    intros n,
    specialize hu n,
    linarith,
  have bornes : ∀ n, u n ∈ [a, b],
    intro n, exact (hu n).left,
  rcases bolzano_weierstrass bornes with ⟨c, c_dans, φ, φ_extr, lim⟩,
  have lim_infinie_extr : limite_infinie_suite (f ∘ (u ∘ φ)),
    exact limite_infinie_extraction_si_limite lim_infinie φ_extr,
  have lim_extr : limite_suite (f ∘ (u ∘ φ)) (f c),
    exact seq_continue_si_continue (hf c c_dans) lim,
  exact limite_infinie_pas_finie lim_infinie_extr (f c) lim_extr,
  -- sorry
end

/-
Pour l'exercice suivant, on pourra utiliser le lemme

  abs_neg x : |-x| = |x|
-/

-- Si f est continue en x₀ alors -f est aussi continue en x₀
lemma continue_opposee {f : ℝ → ℝ} {x₀ : ℝ} (h : continue_en f x₀) :
  continue_en (λ x, -f x) x₀ :=
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

-- Toute fonction continue sur un segment y est minorée.
lemma minoree_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ [a, b], continue_en f x) :
∃ m, ∀ x ∈ [a, b], m ≤ f x :=
begin
  have : ∃ M, ∀ x ∈ [a, b], -f x ≤ M,
  {
    -- sorry
    apply majoree_segment,
    intros x x_dans,
    exact continue_opposee (hf x x_dans),
    -- sorry
  },
  -- sorry
  cases this with M hM,
  use -M,
  intros x x_dans,
  specialize hM x x_dans,
  linarith,
  -- sorry
end

/-
Nous avons démontré dans la feuille 5 qu'une suite a au plus une limite :

 unicite_limite : limite_suite u l → limite_suite u l' → l = l'

et démontré dans la feuille 6 que,si u tend vers l alors toutes ses suites
extraites tendent vers l :

  limite_extraction_si_limite (h : limite_suite u l) (hφ : extraction φ) :
    limite_suite (u ∘ φ) l

On admet une version du théorème de la borne supérieure (qu'on ne peut pas
démontrer sans construire les nombres réels ou admettre un autre théorème
aussi fort) :

sup_segment {a b : ℝ} {A : set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ [a, b]) :
  ∃ x ∈ [a, b], borne_sup A x

Dans l'exercice suivant, il peut être utile de démontrer une inclusion
entre ensembles A et B de nombres réels.
Par définition, A ⊆ B signifie : ∀ x, x ∈ A → x ∈ B.
On peut donc commencer la démonstration de A ⊆ B par « intros x x_dans_A »
qui fait apparaître « x : ℝ » et « x_dans_A : x ∈ A  » dans le contexte,
puis démontrer x ∈ B.

On remarquera aussi l'utilisation de la notation
  {x | P x}
qui désigne l'ensemble des x vérifiant le prédicat P.
Par exemple, la définition du segment [a, b] est :
[a, b] = { x | a ≤ x ∧ x ≤ b }

Ainsi l'énoncé x' ∈ { x | P x} signifie P x', par définition.

La structure de la démonstration suivante vous est offerte. On notera aussi
au passage (mais sans nécessairement essayer de les retenir) l'apparition
de plusieurs commandes Lean permettant de rassembler en une ligne une
fastidieuse série de intros et cases. Toutes ces démonstrations peuvent
se faire sans commande nouvelle, mais leur complexité justifie d'investir
dans des raccourcis.
-/

/-- Toute fonction continue sur un segment non vide y admet un maximum. -/
example {a b : ℝ} (hab : a ≤ b) (hf : ∀ x ∈ [a, b], continue_en f x) :
∃ x₀ ∈ [a, b], ∀ x ∈ [a, b], f x ≤ f x₀ :=
begin
  cases minoree_segment hf with m hm,
  cases majoree_segment hf with M hM,
  let A := {y | ∃ x ∈ [a, b], y = f x}, -- A est l'image de [a, b] par f
  -- La commande obtain n'est pas à retenir, c'est un raccourci
  -- pour un have et deux cases
  obtain ⟨y₀, y_dans, y_sup⟩ : ∃ y₀ ∈ [m, M], borne_sup A y₀,
  {
    -- sorry
    apply sup_segment,
    { use f a,
      use a,
      split,
      split,
      linarith,
      exact hab,
      ring, },
    { intros y y_dans,
      cases y_dans with x hx,
      cases hx with x_dans hxy,
      rw hxy,
      split,
      exact hm x x_dans,
      exact hM x x_dans }
    -- sorry
  }, -- Bien observer le contexte après ce obtain
  rw borne_sup_ssi at y_sup,
  -- encore un raccourci pour remplacer trois cases
  rcases y_sup with ⟨y_maj, u, lim_u, u_dans⟩,
  choose v hv using u_dans,
  -- Et un dernier raccourci pour la route
  cases forall_and_distrib.mp hv with v_dans hufv,
  -- On reformule l'hypothèse hufv par une dernière commande exotique
  replace hufv : u = f ∘ v := funext hufv,
  -- sorry
  rcases bolzano_weierstrass v_dans with ⟨x₀, x₀_dans, φ, φ_extr, lim_vφ⟩,
  use [x₀, x₀_dans],
  intros x x_dans,
  have lim : limite_suite (f ∘ v ∘ φ) (f x₀),
  { apply seq_continue_si_continue,
    exact hf x₀ x₀_dans,
    exact lim_vφ },
  have unique : f x₀ = y₀,
  { apply unicite_limite lim,
    rw hufv at lim_u,
    exact limite_extraction_si_limite lim_u φ_extr },
  rw unique,
  apply y_maj,
  use [x, x_dans],
  -- sorry
end

-- Malheureusement linarith ne fait pas tout seul le lemme suivant
lemma stupide {a b x : ℝ} (h : x ∈ [a, b]) (h' : x ≠ b) : x < b :=
lt_of_le_of_ne h.right h'

/-
Et maintenant le boss final...
-/

/-- Le théorème des valeurs intermédiaires -/
example (f : ℝ → ℝ) (hf : ∀ x, continue_en f x) (h₀ : f 0 < 0) (h₁ : f 1 > 0) :
∃ x₀ ∈ [0, 1], f x₀ = 0 :=
begin
  let A := { x | x ∈ [0, 1] ∧ f x < 0},
  have ex_x₀ : ∃ x₀ ∈ [0, 1], borne_sup A x₀,
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
  rcases ex_x₀ with ⟨x₀, x₀_dans, x₀_sup⟩,
  use [x₀, x₀_dans],
  have : f x₀ ≤ 0,
  {
    -- sorry
    rw borne_sup_ssi at x₀_sup,
    rcases x₀_sup with ⟨maj_x₀, u, lim_u, u_dans⟩,
    have : limite_suite (f ∘ u) (f x₀),
      exact seq_continue_si_continue (hf x₀) lim_u,
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
    apply stupide x₀_dans,
    intro h,
    rw ← h at h₁,
    linarith
    -- sorry
  },
  have : f x₀ ≥ 0,
  { have dans : ∃ N : ℕ, ∀ n ≥ N, x₀ + 1/(n+1) ∈ [0, 1],
    { have : ∃ N : ℕ, ∀ n≥ N, 1/(n+1 : ℝ) ≤ 1-x₀,
      {
        -- sorry
        apply limite_inv_succ,
        linarith,
        -- sorry
      },
      -- sorry
      cases this with N hN,
      use N,
      intros n hn,
      specialize hN n hn,
      have : 1/(n+1 : ℝ) > 0,
        exact inv_succ_pos n,
      split,
        change 0 ≤ x₀ ∧ x₀ ≤ 1 at x₀_dans,
        linarith,
      linarith
      -- sorry
    },
    have pas_dans : ∀ n : ℕ, x₀ + 1/(n+1) ∉ A,
    -- Par définition, x ∉ A signifie « non (x ∈ A) ».
    {
      -- sorry
      intros n hn,
      cases x₀_sup with x₀_maj _,
      specialize x₀_maj _ hn,
      have : 1/(n+1 : ℝ) > 0,
        exact inv_succ_pos n,
      linarith,
      -- sorry
    },
    dsimp [A] at pas_dans, -- il est inutile de retenir cette commande
    -- sorry
    push_neg at pas_dans,
    have lim : limite_suite (λ n, f(x₀ + 1/(n+1))) (f x₀),
    { apply seq_continue_si_continue (hf x₀),
      apply lim_plus_un_sur },
    apply le_lim lim,
    cases dans with N hN,
    use N,
    intros n hn,
    specialize pas_dans n,
    specialize hN n hn,
    cases pas_dans with H H,
    { exfalso,
      exact H hN },
    { exact H }
    -- sorry
  },
  linarith,
end
