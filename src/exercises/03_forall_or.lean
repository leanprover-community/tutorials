import data.real.basic
import algebra.group.pi

set_option pp.beta true

/-
In this file, we'll learn about the ∀ quantifier, and the disjunction 
operator ∨ (logical OR).

Let P be a predicate on a type X. This means for every mathematical
object x with type X, we get a mathematical statement P x. 
In Lean, P x has type Prop.

Lean sees a proof h of `∀ x, P x` as a function sending any `x : X` to
a proof `h x` of `P x`. 
This already explains the main way to use an assumption or lemma which
starts with a ∀. 

In order to prove `∀ x, P x`, we use `intros x` to fix an arbitrary object
with type X, and call it x.

Note also we don't need to give the type of x in the expression `∀ x, P x`
as long as the type of P is clear to Lean, which can then infer the type of x.

Let's define two predicates to play with ∀.
-/

def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

def odd_fun (f : ℝ → ℝ) := ∀ x, f (-x) = -f x

/-
In the next proof, we also take the opportunity to introduce the 
`unfold` tactic, which simply unfolds definitions. Here this is purely
for didactic reason, Lean doesn't need those `unfold` invocations. 
We will also use `rfl` which is a term proving equalities that are true 
by definition (in a very strong sense to be discussed later).
-/

example (f g : ℝ → ℝ) : even_fun f → even_fun g →  even_fun (f + g) :=
begin
  -- Assume f is even
  intros hf,
  -- which means ∀ x, f (-x) = f x
  unfold even_fun at hf,
  -- and the same for g
  intros hg,
  unfold even_fun at hg,
  -- We need to prove ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun,
  -- Let x be any real number
  intros x,
  -- and let's compute
  calc (f + g) (-x) = f (-x) + g (-x) : rfl
  ... = f x + g (-x) : by rw hf x 
  ... = f x + g x : by rw hg x 
  ... = (f + g) x : rfl
end

/-
In the preceding proof, all `unfold` lines are purely for
psychological comfort.

Sometimes unfolding is necessary because we want to apply a tactic
that operates purely on the syntactical level.
The main such tactic is `rw`.

The same property of `rw` explain why the first computation line
is necessary, although its proof is simply `rfl`.
Before that line, `rw hf x` won't find anything like `f (-x)` hence
will give up.
The last line is not necessary however, since it only proves 
something that is true by definition, and is not followed by
a `rw`.

Also, Lean doesn't need to be told that hf should be specialized to 
x before rewriting, exactly as in the first file 01_equality_rewriting.
We can also gather several rewrites using a list of expressions.

One last trick is that `rw` can take a list of expressions to use for
rewriting. For instance `rw [h₁, h₂, h₃]` is equivalent to three
lines `rw h₁`, `rw h₂` and `rw h₃`. Note that you can inspect the tactic
state between those rewrites when reading a proof using this syntax. You
simply need to move the cursor inside the list.

Hence we can compress the above proof to:
-/

example (f g : ℝ → ℝ) : even_fun f → even_fun g →  even_fun (f + g) :=
begin
  intros hf hg x,
  calc (f + g) (-x) = f (-x) + g (-x) : rfl
  ... = f x + g x : by rw [hf, hg] 
end

/-
Now let's practice. If you need to learn how to type a unicode symbol,
you can put your mouse cursor above the symbol and wait for one second.
-/

-- 0023
example (f g : ℝ → ℝ) : even_fun f → even_fun (g ∘ f) :=
begin
  sorry
end

-- 0024
example (f g : ℝ → ℝ) : odd_fun f → odd_fun g →  odd_fun (g ∘ f) :=
begin
  sorry
end

/-
Let's have more quantifiers, and play with forward and backward reasoning. 

In the next definitions, note how `∀ x₁, ∀ x₂` is abreviated to `∀ x₁ x₂`. 
-/

def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

/- Let's be very explicit and use forward reasoning first. -/
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) : non_decreasing (g ∘ f) :=
begin
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intros x₁ x₂ h,
  -- Since f is non-decreasing, f x₁ ≤ f x₂.
  have step₁ :  f x₁ ≤ f x₂,
    exact hf x₁ x₂ h,
  -- Since g is non-decreasing, we then get g (f x₁) ≤ g (f x₂).
  exact hg (f x₁) (f x₂) step₁,
end

/-
In the above proof, note how inconvenient it is to specify x₁ and x₂ in `hf x₁ x₂ h` since
they could be inferred from the type of h. 
We could have written `hf _ _ h` and Lean would have filled the holes denoted by _. 

Even better we could have written the definition
of `non_decreasing` as: ∀ {x₁ x₂}, x₁ ≤ x₂ → f x₁ ≤ f x₂, with curly braces to denote
implicit arguments.
 
But let's leave that aside for now. One possible variation on the above proof is to
use the `specialize` tactic to replace hf by its specialization to the relevant value.
 -/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) : non_decreasing (g ∘ f) :=
begin
  intros x₁ x₂ h,
  specialize hf x₁ x₂ h,
  exact hg (f x₁) (f x₂) hf,
end

/-
This `specialize` tactic is mostly useful for exploration, or in preparation for rewriting 
in the assumption. One can very often replace its use by using more complicated expressions
directly involving the original assumption, as in the next variation:
-/
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) : non_decreasing (g ∘ f) :=
begin
  intros x₁ x₂ h,
  exact hg (f x₁) (f x₂) (hf x₁ x₂ h),
end

/-
Since the above proof uses only `intros` and `exact`, we could very easily replace it by the
raw proof term:
-/
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) : non_decreasing (g ∘ f) :=
λ x₁ x₂ h, hg (f x₁) (f x₂) (hf x₁ x₂ h)

/-
Of course the above proof is difficult to decipher. The principle in mathlib is to use
such a proof when the result is obvious and you don't want to read the proof anyway. 

Instead of pursuing this style, let's see how backward reasoning would look like here.
As usual with this style, we use `apply` and enjoy Lean specializing assumptions for us
using unification.
-/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) : non_decreasing (g ∘ f) :=
begin
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intros x₁ x₂ h,
  -- We need to prove (g ∘ f) x₁ ≤ (g ∘ f) x₂.
  -- Since g is non-decreasing, it suffices to prove f x₁ ≤ f x₂
  apply hg,
  -- which follows from our assumption on f
  apply hf,
  -- and on x₁ and x₂
  exact h
end

-- 0025
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) : non_increasing (g ∘ f) :=
begin
  sorry
end

/-
Let's switch to disjunctions now. Lean denotes by ∨ the
logical OR operator.

In order to make use of an assumption
  hyp : P ∨ Q
we use the cases tactic:
  cases hyp with hP hQ
which creates two proof branches: one branch assuming hP : P,
and one branch assuming hQ : Q.

In order to directly prove a goal P ∨ Q,
we use either the `left` tactic and prove P or the `right`
tactic and prove Q.

In the next proof we use `ring` and `linarith` to get rid of 
easy computations or inequalities, as well as one lemma:

  mul_eq_zero : a*b = 0 ↔ a = 0 ∨ b = 0
-/

example (a b : ℝ) : a = a*b → a = 0 ∨ b = 1 :=
begin
  intro hyp,
  have H : a*(1 - b) = 0,
  { calc a*(1 - b) = a - a*b : by ring
               ... = 0       : by linarith, },
  rw mul_eq_zero at H,
  cases H with Ha Hb,
  { left,
    exact Ha, },
  { right,
    linarith, },
end

-- 0026
example (x y : ℝ) : x^2 = y^2 → x = y ∨ x = -y :=
begin
  sorry
end

/-
In the next exercise, we can use:
  eq_or_lt_of_le : x ≤ y → x = y ∨ x < y
-/

-- 0027
example (f : ℝ → ℝ) : non_decreasing f ↔ ∀ x y, x < y → f x ≤ f y :=
begin
  sorry
end

/-
In the next exercise, we can use:
  le_total x y : x ≤ y ∨ y ≤ x
-/

-- 0028
example (f : ℝ → ℝ) (h : non_decreasing f) (h' : ∀ x, f (f x) = x) : ∀ x, f x = x :=
begin
  sorry
end

