import ..untranslated.my_lib
/-
Négations, raisonnements par l'absurde et contraposées.

Cette feuille introduit les principes logiques et commandes Lean liées
aux négations d'énoncés. Elle introduit de nombreuses nouvelles commandes :
exfalso, by_contradiction, contrapose, by_cases et push_neg.
Il est donc important de bien s'accrocher à son aide-mémoire Lean.

On introduit l'idée de contradiction mathématique ou absurdité mathématique,
sous la forme d'un énoncé spécial appelé « Faux » et noté false par Lean.
Par définition, cet énoncé n'a pas de démonstration.

Par conséquent, Faux entraîne n'importe quel autre énoncé : pour tout énoncé P,
« Faux ⇒ P » est vrai : « si Faux alors P » ne coûte rien puisque Faux n'est
pas vrai. Une autre façon d'y penser est de se dire, comme Lean le fait,
qu'une démonstration de « Faux ⇒ P » est une machine qui transforme toute
démonstration de Faux en démonstration de P, et la machine qui ne fait rien
convient car nous n'avons rien à lui donner en entrée.

Les logiciens aiment appeler cette implication de son nom latin
« ex falso quod libet » (du faux découle tout ce que l'on veut).
Lean a une commande pour invoquer ce principe : exfalso.
-/

-- Montrons que si Faux alors 0 = 1
example : false → 0 = 1 :=
begin
  -- Supposons Faux
  intro h,
  -- On veut montrer 0 = 1. Ex falso quod libet, donc il suffit de montrer Faux.
  exfalso,
  -- Or c'est ce que nous avons supposé.
  exact h,
end

/-
L'exemple précédent suggère que la définition de Faux n'est pas très utile.
Mais c'est sur elle que va s'appuyer la définition de la négation.
Si P est un énoncé, sa négation est l'énoncé « non P » défini comme
« P ⇒ Faux». Les logiciens et Lean le notent ¬ P (mais en maths quotidiennes
on n'utilise pas de notation ici).

Ainsi l'affirmation « non P » se lit : « Si P était vrai, on aurait une
contradiction ». Par exemple, la définition de « a ≠ b » est « non (a = b) ».

On peut montrer que « non P » est vrai si et seulement si « P ⇔ Faux » est vrai,
mais en pratique c'est vraiment la définition de « non P » qui est directement
utile.
-/

-- Soit x un réel. Montrons que « non x < x ».
lemma non_strictement_inferieur_soi {x : ℝ} : ¬ x < x :=
begin
  -- Suppons x < x et démontrons une contradiction.
  intro hyp,
  -- L'hypothèse x < x signifie que x ≤ x et x ≠ x
  rw lt_iff_le_and_ne at hyp,
  -- en particulier x ≠ x
  cases hyp with hyp_inf hyp_non,
  -- (l'autre condition ne servira pas).
  clear hyp_inf, -- La commande clear oublie une hypothèse, Lean n'en a pas
                 -- besoin, c'est juste pour nous clarifier les idées.
  -- Par définition de ≠, cette hypothèse signifie que, pour obtenir une
  -- contradiction, il suffit de montrer que x = x.
  change x = x → false at hyp_non,
  -- (La commande change transforme une hypothèse ou le but en un énoncé
  --  équivalent par définition, Lean n'en a pas besoin ici, c'est juste
  --  pour nous)
  apply hyp_non,
  -- Or cela découle de la réflexivité de l'égalité.
  reflexivity, -- ou bien « ring, »
end

-- Soit n un entier. On suppose que n est pair et que n n'est pas pair.
-- Montrons alors que 0 = 1.
example (n : ℤ) (h_pair : pair n) (h_non_pair : ¬ pair n) : 0 = 1 :=
begin
  -- sorry
  exfalso,
  exact h_non_pair h_pair,
  -- sorry
end

/-
Pour la suite, on rappelle les définitions suivantes :

def pair (n : ℤ) := ∃ k, n = 2*k
def impair (n : ℤ) := ∃ k, n = 2*k + 1

et on a les deux lemmes :

pair_ou_impair (n : ℤ) : pair n ∨ impair n
non_pair_et_impair (n : ℤ) : ¬ (pair n ∧ impair n)
-/

-- Sans utiliser la définition de pair et impair, mais en utilisant les
-- deux lemmes, montrons qu'un nombre n'est pas pair ssi il est impair.
lemma non_pair_ssi (n : ℤ) : ¬ pair n ↔ impair n :=
begin
  -- sorry
  split,
    intro hnonpair,
    cases pair_ou_impair n with hpair himpair,
      exfalso,
      exact hnonpair hpair,
    exact himpair,
  intros himpair hpair,
  apply non_pair_et_impair n,
  split,
    exact hpair,
  exact himpair,
  -- sorry
end

/-
Muni de la définition de la négation, on montre facilement que
tout énoncé P implique sa double négation « non non P ».

En rajoutant l'axiome du tiers exclu, qui affirme que « P ou non P » est vrai
pour tout énoncé P, on montre facilement la réciproque : « non non P »
implique P.

Au final on a alors l'équivalence entre « non non P » et P, une propriété
connue sous le nom de « principe d'élimination des doubles négations ».
Dans Lean cela correspond au lemme
not_not {P : Prop} : (¬ ¬ P) ↔ P
(on le rappelera si besoin).

L'implication « non non P ⇒ P » est la base du raisonnement par l'absurde :
pour montrer P, il suffit de montrer « non non P », c'est-à-dire
« non P ⇒ Faux » donc il suffit de supposer « non P » et de démontrer Faux.
En pratique on ne décompose pas ce petit raisonnement et on écrit directement
« Par l'absurde, supposons non P ». Dans Lean on écrit
by_contradiction Hyp,
qui transforme le but P en false et ajoute au contexte l'hypothèse Hyp : ¬ P.
-/

/-
Reprenons une démonstration de la feuille 5, l'unicité de la limite.
On ne peut pas démontrer ce résultat sans utiliser l'axiome du tiers exclu
quelque part. Dans la feuille 5, cette utilisation était cachée dans le lemme

egal_si_abs_eps (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y

(dont on démontrera une variante plus bas à l'aide du tiers exclu).
-/
example (u : ℕ → ℝ) (l l' : ℝ) : limite_suite u l → limite_suite u l' → l = l' :=
begin
  -- Supposons que u tende vers l et vers l'
  intros hl hl',
  -- Supposons par l'absurde que « non (l = l') », c'est à dire l ≠ l'.
  by_contradiction H,
  -- c'est à dire l ≠ l'
  change l ≠ l' at H, -- Cette ligne est inutile pour Lean, c'est pour nous.
  -- (en temps normal on écrirait directement : Supposons par l'absurde l ≠ l')
  -- En particulier |l-l'| > 0
  have ineg : |l-l'| > 0,
    -- (la démonstration ci-dessous n'est pas importante, il faut juste noter
    -- qu'elle fait bien intervenir l'hypothèse H)
    exact abs_pos_of_ne_zero (sub_ne_zero_of_ne H),
  -- On peut donc appliquer l'hypothèse de convergence vers l à ε = |l'-l|/4
  -- pour obtenir N tel que ∀ n ≥ N, |u n - l| ≤ |l - l'|/4.
  cases hl ( |l-l'|/4 ) (by linarith) with N hN,
  -- On obtient de même N' tel que ∀ n ≥ N', |u n - l'| ≤ |l - l'|/4.
  cases hl' ( |l-l'|/4 ) (by linarith) with N' hN',
  -- Ainsi, pour l'indice N₀ = max(N, N'), on a |u N₀ - l| ≤ |l - l'|/4
  let N₀ := max N N', -- la commande « let » n'est jamais indispensable
                      -- mais elle économise quelques caractères.
  specialize hN N₀ (le_max_left _ _),
  -- et |u N₀ - l'| ≤ |l - l'|/4.
  specialize hN' N₀ (le_max_right _ _),

  -- On démontre alors par calcul que |l-l'| < |l-l'|
  have clef : |l-l'| < |l-l'|,
    calc
    |l - l'| = |(l-u N₀) + (u N₀ -l')|   : by ring
         ... ≤ |l - u N₀| + |u N₀ - l'|  : by apply abs_add
         ... =  |u N₀ - l| + |u N₀ - l'| : by rw abs_sub
         ... ≤ |l-l'|/4 + |l-l'|/4       : by linarith
         ... = |l-l'|/2                  : by ring
         ... < |l-l'|                    : by linarith,
  -- ce qui est absurde.
  exact non_strictement_inferieur_soi clef,
end

/-
Une autre incarnation très utile de l'axiome du tiers exclu est le principe
de contraposition : pour démontrer « P ⇒ Q », il suffit de démontrer
« non Q ⇒ non P ».
-/

-- En utilisant un raisonnement par l'absurde, montrer le principe
-- de contraposition
example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q :=
begin
  -- sorry
  intro hP,
  by_contradiction hnQ,
  exact h hnQ hP,
  -- sorry
end

/-
En fait la réciproque du principe de contraposition est vraie aussi (et se
démontre sans même utiliser l'axiome du tiers exclu). On a donc
(P ⇒ Q) ⇔ (non Q ⇒ non P)

On prendra bien garde à ne pas confondre :
  * la contraposé de « P ⇒ Q » qui est « non Q ⇒ non P »
  * la réciproque de « P ⇒ Q » qui est « Q ⇒ P ».

En général la réciproque d'une implication n'a aucun lien logique avec
l'implication de départ.

Comme pour le raisonnement par l'absurde, le principe de contraposition n'est
pas redécomposé à chaque fois, on se contente d'écrire contrapose dans Lean
et « Montrons la contraposée » ou « Par contraposition, il suffit de montrer
que » ou quelque chose d'analogue sur papier.
-/

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q :=
begin
  contrapose,
  exact h,
end

-- Dans l'exercice suivant, on raisonnera par contraposition pour une
-- des implications, et on utilisera les définitions de pair et impair ainsi
-- que le lemme « non_pair_ssi (n : ℤ ): ¬ pair n ↔ impair n » démontré plus
-- haut.
example (n : ℤ) : pair (n^2) ↔ pair n :=
begin
  -- sorry
  split,
    contrapose,
    rw non_pair_ssi,
    rw non_pair_ssi,
    rintro ⟨k, hk⟩,
    rw hk,
    use 2*k*(k+1),
    ring,
  rintro ⟨k, hk⟩,
  use 2*k^2,
  rw hk,
  ring,
  -- sorry
end

/-
On termine ce tour d'horizon du tiers exclu en signalant que, particulièrement
dans les exercices de logique pure, il est parfois utile d'utiliser l'axiome
du tiers exclu sous sa forme d'origine : pour tout énoncé P, soit P est vrai
soit ¬ P est vrai. Plutôt que d'invoquer cet énoncé puis de faire une
disjonction de cas à l'aide de la commande `cases`, Lean introduit le raccourci

by_cases h : P,

qui combine les deux étapes et créé directement deux branches de la
démonstration : une dans laquelle on suppose h : P et l'autre dans laquelle
on suppose h : ¬ P.

Prenons comme exemple une reformulation du connecteur d'implication, qui
sert parfois de définition à l'implication, particulièrement dans les
présentations de la logique basées sur les tables de vérités
(ou le tiers exclu est donc présent de façon essentielle dès le début).
-/

-- Dans les deux exemples suivants, P et Q désignent des énoncés mathématiques.
variables (P Q : Prop)

example : (P → Q) ↔ (¬ P ∨ Q) :=
begin
  -- Montrons les deux implications
  split,
    -- Supposons d'abord que P implique Q,
    intro h,
    -- et discutons selon que P est vrai ou faux.
    by_cases hP : P,
      -- Si P est vrai, alors Q l'est aussi
      right,
      -- car on a supposé P et P ⇒ Q.
      exact h hP,
    -- Si au contraire P est faux alors on a directement l'alternative de
    -- gauche dans la disjonction.
    left,
    exact hP,
  -- Réciproquement, supposons non P ou Q.
  intros h,
  -- On doit montrer que P implique Q. Supposons donc P et montrons Q.
  intros hP,
  -- Pour cela, puisque nous avons supposé « non P ou Q » il y a deux
  -- cas possibles.
  cases h with hnP hQ,
    -- Si P est faux, alors les hypothèses sont contradictoires donc
    -- nous pouvons en déduire ce qu'on veut, en particulier Q.
    exfalso,
    -- En effet nous avons supposé à la fois non P et P.
    exact hnP hP,
  -- Dans l'autre cas, c'est Q qui est supposé vrai donc il n'y a plus rien
  -- à démontrer.
  exact hQ
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  -- sorry
  split,
    intro h,
    by_cases hP : P,
      right,
      intro hQ,
      exact h ⟨hP, hQ⟩,
    left,
    exact hP,
  intro h,
  intro hPQ,
  cases hPQ with hP hQ,
  cases h with hnP hnQ,
    exact hnP hP,
  exact hnQ hQ,
  -- sorry
end

/-
Il est crucial de comprendre les négations d'énoncés comportant des
quantificateurs. Les deux exercices suivants introduisent cela sur des exemples.
Dans le premier, on utilisera seulement la définition de la négation.
-/

example (n : ℤ) : ¬ (∃ k, n = 2*k) ↔ ∀ k, n ≠ 2*k :=
begin
  -- sorry
  split,
    intro hyp,
    intro k,
    intro hk,
    apply hyp,
    use k,
    exact hk,
  intro hyp,
  intro h,
  cases h with k hk,
  specialize hyp k,
  exact hyp hk,
  -- sorry
end


/-
Contrairement à la négation du quantificateur existentiel, la négation du
quantificateur universel nécessite le tiers exclu pour la première implication.
Pour cette implication, on utilisera au choix :
* un double raisonnement par l'absurde
* ou bien une contraposition, l'élimination des doubles négations
  (via le lemma not_not : (¬ ¬ P) ↔ P) et un raisonnement par l'absurde.
-/

def paire (f : ℝ → ℝ) := ∀ x, f (-x) = f x

example (f : ℝ → ℝ) : ¬ paire f ↔ ∃ x, f (-x) ≠ f x :=
begin
  -- sorry
  -- unfold paire,
  split,
    contrapose,
    intro h,
    rw not_not,
    intro x,
    by_contradiction H,
    apply h,
    use x,
    /- Version avec deux raisonnements par l'absurde.
    intro h,
    by_contradiction H,
    apply h,
    intro x,
    by_contradiction H',
    apply H,
    use x, -/
  intro h,
  cases h with x hx,
  intro h',
  specialize h' x,
  exact hx h',
  -- sorry
end

/-
En pratique on ne redémontre pas constamment ces règles de négation des énoncés
quantifiés (les démonstrations ne sont même pas si simples !), on  les connait
par cœur.
Dans Lean on utilise push_neg pour pousser les négations le plus
possible vers la droite (parfois elles disparaissent complètement
si l'énoncé le plus à droite a une négation qui s'exprime bien).
-/

-- Montrons que la fonction x ↦ 2x n'est pas paire.
example : ¬ paire (λ x, 2*x) :=
begin
  unfold paire, -- On notera que, pour une fois, cette ligne de dépliage
                -- est importante car push_neg ne déplie pas les définitions.
  push_neg,
  use 42,
  linarith,
end

example (f : ℝ → ℝ) : ¬ paire f ↔ ∃ x, f (-x) ≠ f x :=
begin
  -- sorry
  unfold paire,
  push_neg,
  -- sorry
end

def majoree (f : ℝ → ℝ) := ∃ M, ∀ x, f x ≤ M

-- La fonction identité, x ↦ x, n'est pas majorée.
example : ¬ majoree (λ x, x) :=
begin
  unfold majoree,
  push_neg,
  intro M,
  use M + 1,
  linarith,
end

-- Dans l'exercice suivant, on raisonnera par contraposition.
example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 :=
begin
  -- sorry
  contrapose,
  push_neg,
  intro h,
  use x/2,
  split,
    linarith,
  linarith,
  -- sorry
end

/-
Le combo « contrapose, push_neg » est tellement courant qu'on peut l'abréger
en « contrapose!, ». Cette abréviation est utilisable dès que vous serez
suffisamment habitués pour ne plus vouloir voir les deux étapes.

Dans l'exercice suivant, on pourra utiliser le lemme
eq_or_lt_of_le : a ≤ b → a = b ∨ a < b
-/

example (f : ℝ → ℝ) : (∀ x y, x < y → f x < f y) ↔ (∀ x y, (x ≤ y ↔ f x ≤ f y)) :=
begin
  -- sorry
  split,
  { intro hf,
    intros x y,
    split,
    { intros hxy,
      cases eq_or_lt_of_le hxy with hxy hxy,
      { rw hxy },
      { specialize hf x y hxy,
        linarith } },
    { contrapose!,
      apply hf } },
  { intros hf x y,
    contrapose!,
    intro h,
    rw hf,
    exact h }
  -- sorry
end
