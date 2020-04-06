import tactic
import topology.metric_space.basic
variables {X : Type*} [metric_space X]
variables {Y : Type*} [metric_space Y]

/-- Jason KY effort -/
/- Definition of an open ball -/
def open_ball (x₀ : X) (r : ℝ) := {x : X | dist x₀ x < r}

/- Definition of being open -/
def is_open' (S : set X) := ∀ s ∈ S, ∃ (ε : ℝ) (hε : 0 < ε), open_ball s ε ⊆ S

/- Definition of being closed -/
def is_closed' (S : set X) := is_open' $ -S

/- Definition of the set of limit points -/
def limit_points (S : set X) :=
    {x : X | ∀ (ε : ℝ) (hε : 0 < ε), ∃ (y ∈ S) (x ≠ y), y ∈ open_ball x ε}

/- Definition of closure -/
def closure' (S : set X) := ⋂ (T : set X) (h₀ : S ⊆ T) (h₁ : is_closed' T), T

attribute [reducible] open_ball is_open' is_closed'
limit_points

/- Defining the structure of a closed set -/
structure closed_set (X : Type*) [metric_space X] :=
(carrier : set X)
(is_closed : is_closed' carrier)

instance : has_coe (closed_set X) (set X) := ⟨closed_set.carrier⟩
instance : has_le (closed_set X) := ⟨λ α β, (α : set X) ⊆ (β : set X)⟩
instance : has_lt (closed_set X) := ⟨λ α β, (α : set X) ⊂ (β : set X)⟩

theorem ext' {S T : closed_set X} (h : (S : set X) = T) : S = T :=
by cases S; cases T; congr'

open set

def Closure (S : set X) : closed_set X :=
{ carrier := closure' S,
  is_closed := sorry }

/- The closure of a closed_set is itself -/
lemma Closure_self (T : closed_set X) : T = Closure T.1 := sorry

instance : partial_order (closed_set X) :=
{.. partial_order.lift (coe : closed_set X → set X) (λ a b, ext') (by apply_instance)}

/- The closure of a closed_set is itself -/
lemma Closure_self' (T : closed_set X) : T = Closure T.1 := sorry

/- A set is smaller than its closure -/
theorem subset_closure' (S : set X) : S ⊆ closure' S :=
set.subset_Inter $ λ _, set.subset_Inter $ λ h, set.subset_Inter $ λ _, h

/- The closure of a smaller set is smaller than closure -/
theorem closure_mono' {S T : set X} (h : S ⊆ T) : closure' S ⊆ closure' T := sorry

/- Closed sets form a Galois insertion -/
def gi : @galois_insertion (set X) (closed_set X) _ _ Closure closed_set.carrier :=
{ choice := λ S h, Closure S,
  gc := λ S T,
    ⟨λ h, set.subset.trans (subset_closure' S) h, λ h, by rw Closure_self T; from closure_mono' h⟩,
  le_l_u := λ S, subset_closure' S,
  choice_eq := λ _ _, rfl }

/- Closed sets form a complete lattice -/
instance : complete_lattice (closed_set X) :=
{ .. galois_insertion.lift_complete_lattice gi}

--set_option pp.notation false
example (A B : closed_set X) : A ⊔ B = A ⊓ B :=
begin
  show Closure (A.carrier ∪ B.carrier) = Closure (A.carrier ∩ B.carrier),
  sorry
end


#print galois_insertion.lift_complete_lattice
#print complete_lattice.sup
