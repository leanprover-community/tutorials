import data.real.basic
import data.int.parity

/-  
In this file, we learn how to handle the ∃ quantifier.

In order to prove `∃ x, P x`, we give some x₀ using tactic `use x₀` and
then prove `P x₀`. This x₀ can be an object from the local context
or a more complicated expression.
-/
example : ∃ n : ℕ, 8 = 2*n :=
begin
  use 4,
  refl,  -- this is the tactic analogue of the rfl proof term
end

/-
In order to use `h : ∃ x, P x`, we use the `cases` tactic to fix 
one x₀ that works.

Again h can come straight from the local context or can be a more 
complicated expression.
-/
example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 :=
begin
  -- Let's fix k₀ such that n = k₀ + 1.
  cases h with k₀ hk₀,
  -- It now suffices to prove k₀ + 1 > 0.
  rw hk₀,
  -- and we have a lemma about this
  exact nat.succ_pos k₀,
end

/-
The next exercises use divisibility in ℤ (beware the ∣ symbol which is
not ASCII).

By definition, a ∣ b ↔ ∃ k, b = a*k, so you can prove a ∣ b using the
`use` tactic.
-/

-- Until the end of this file, a, b and c will denote integers, unless
-- explicitly stated otherwise
variables (a b c : ℤ)

-- 0029
example (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
begin
  sorry
end

/-
A very common pattern is to have an assumption or lemma asserting
  h : ∃ x, y = ...
and this is used through the combo:
  cases h with x hx,
  rw hx at ...
The tactic `rcases` allows us to do recursive `cases`, as indicated by its name,
and also simplifies the above combo when the name hx is replaced by the special
name `rfl`, as in the following example. 
It uses the anonymous constructor angle brackets syntax.
-/


example (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b+c :=
begin
  rcases h1 with ⟨k, rfl⟩,
  rcases h2 with ⟨l, rfl⟩,
  use k+l,
  ring,
end

/-
You can use the same `rfl` trick with the `rintros` tactic.
-/

example : a ∣ b → a ∣ c → a ∣ b+c :=
begin
  rintros ⟨k, rfl⟩ ⟨l, rfl⟩,
  use k+l,
  ring,
end

-- 0030
example : 0 ∣ a ↔ a = 0 :=
begin
  sorry
end

/-
We can now start combining quantifiers, using the definition

  surjective (f : X → Y) := ∀ y, ∃ x, f x = y

-/
open function

-- In the remaining of this file, f and g will denote functions from
-- ℝ to ℝ.
variables (f g : ℝ → ℝ)


-- 0031
example (h : surjective (g ∘ f)) : surjective g :=
begin
  sorry
end

/- 
The above exercise can be done in three lines. Try to do the
next exercise in four lines.
-/

-- 0032
example (hf : surjective f) (hg : surjective g) : surjective (g ∘ f) :=
begin
  sorry
end

