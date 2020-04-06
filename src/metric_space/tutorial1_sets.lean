/- This file is intended for beginner Lean users who know about tactics
  such as `intro`, `cases`, `exact`, `left`, `right`

-/

import data.set.basic

/-!

# Sets in Lean

In set theory it's convenient to allow all kinds of sets.
For example, a group can be formalised as an ordered quadruple
(G,*,1,⁻¹) satisfying some axioms, and there are several tricks
to make ordered quadruples out of sets.

In Lean, this heavy lifting is done by the theory of inductive types,
and we have no need for exotic ordered quadruples. However one certainly
needs a theory of sets -- one wants to take the intersection of two subgroups
of a group, or arbitrary unions of open sets in a metric space.

In particular one wants to work with *subsets* of a given set or type. Lean
has such functionality, and we explore it here, learning how to prove
basic statements such as S ⊆ S ∪ T, or ∅ ⊆ S, for S and T subsets of a fixed type X. 

## Introduction

Let `X` be a fixed type. This will be our "universe", and all sets in this
introduction will be subsets of `X`. Recall that because `X` is a type, it has
terms rather than elements, and we write `x : X` to mean that `x` is a term of type `X`.

The type of subsets of `X` is not called `subset X` but `set X`. So `S : set X` means
that `S` is a subset of `X`. If `x : X` then we can ask if `x ∈ S`, which is a true/false
statement. Hence any subset `S` of `X` gives rise to a function `X → Prop` (recall that
`Prop` is the universe of all true/false statements) sending `x : X` to the statement
`x ∈ S`. Conversely, given a function `f : X → Prop` we can form a subset of `X`
consisting of the `x : X` such that `f x` is true. The notation for this in Lean
is `{x : X | f x}`. Thus we have a correspondence between subsets `S : set X` and
functions `X → Prop`, and in fact internally a subset `S` of `X` is stored as a
function `S : X → Prop`, and `x ∈ S` is just notation for the true/false statement `S x`. 

For example if `X = ℝ` and `f : X → Prop` sends the term `x : X` to the statement
`x^2 = 4`, then the corresponding subset `S : set X` is the set `{x : X | x^2 = 4}`,
or in other words the subset `{2, -2}` of `ℝ`.

## Notation

Say `X` is a fixed type, and `S T : set X` are subsets.

`S ⊆ T` is defined to mean `∀ x : X, x ∈ S → x ∈ T`
`S ⊂ T` is defined to mean `S ⊆ T ∧ ¬ (T ⊆ S)`. 
`S ∩ T` is defined to mean the set `{x : X | x ∈ S ∧ x ∈ T}`, and in particular
  `x ∈ S ∩ T` is by definition equal to the statement `x ∈ S ∧ x ∈ T`. 
`S ∪ T` is the set `{x : X | x ∈ S ∨ x ∈ T}`. 
`∅ : set X` is the empty set. The corresponding function X → Prop sends `x : X` to
  the proposition `false`, a proposition with no proof. 
`univ : set X` is the whole type `X` considered as a set. Note that it does not
  make sense to say `univ = X` because they have different types: the type of `univ`
  is `set X` and the type of `X` is `Type`. The underlying function sends `x : X`
  to the proposition `true`, a proposition which can be proved with the tactic `trivial`.

-/

-- Let's prove some theorems about sets in Lean.

namespace tutorial

variables {X : Type} {S T U : set X}

example : S ∩ T ⊆ S :=
begin
  -- recall that (S ∩ T) ⊆ S is defined to mean ∀ x : X, x ∈ (S ∩ T) → x ∈ S,
  -- so we can start with `intro x`
  intro x,
  -- Assume x ∈ S ∩ T
  intro hxST,
  -- the hypothesis hxST is defined to mean `x ∈ S ∧ x ∈ T`, so we can
  -- do `cases` on `hxST` to get to these two simpler proofs.
  cases hxST with hxS hxT,
  -- but our goal is exactly hxS
  exact hxS
end

-- Exercise.
-- recall x ∈ S ∪ T *means* x ∈ S ∨ x ∈ T.
example : S ⊆ S ∪ T :=
begin
  sorry
end


#exit

P → Q
P ∧ Q
P ∨ Q
P ↔ Q
¬ P
∃ x : P x