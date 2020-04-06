# Basic tactic cheat sheet

| Term you want to use | If a hypothesis `h` | If the goal      |
| ----------|:-------------------:|:----------------:|
| P → Q     |   `apply h`         | `intro hP`       |
| P ∧ Q     |   `cases h`         | `split`          |
| P ∨ Q     |   `cases h`         | `left` or `right`|
| P = P     |   (useless)         | `refl`           |
| P = Q     |   `rw h`            |                  |
| P ↔ Q     | `rw h` or `cases h` | `split`          |
| false     |  `cases h`          |                  |
| ∃ x, P x  |  `cases h with x hx`| `use a`          |


## Other

`have h : (some true/false statement)` : use if you want to create a new hypothesis `h` and you know the proof. Lean will create a new goal.

`by_cases h : P` does a case split on whether `P` is true
or false. If Lean complains that it doesn't know that your
proposition is decidable, try the `classical` tactic
before running `by_cases`, or write `open_locale classical`
before you start your proof. 

If you think that a goal should be provable by pure logic,
given what you have, try `cc`, `tauto!`, `finish` or `simp`.
These tactics all do subtly different things, but it's
worth trying them all if you're stuck.

`exfalso` changes the goal to `false`. Can be useful if
your hypotheses are enough to prove a contradiction, and
one of them is `h : ¬ P` (which is notation for `h : P → false`).
After `exfalso` you can `apply P` and reduce your goal to `P`. 

