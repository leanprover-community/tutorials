# lean-tutorials

The goal of this project is to quickly teach you how to use Lean 3 for
mathematics using a very hands-on approach. It can be used alongside
[Theorem proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/)
or independently.
You can first play the 
[Natural number game](http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/)
first, but this is not mandatory.

Currently, those tutorials do no cover creating your own theories, only
proving things in elementary real analysis. All exercices are adapted
from a first year undergraduate course by Patrick Massot in Orsay,
adding only explanations about compressing proofs using slightly advanced
tactics like `rintros` and `rcases`.

What you do need first is to [install Lean 3](https://leanprover-community.github.io/get_started.html#regular-install) and [get this project](https://leanprover-community.github.io/install/project.html#working-on-an-existing-package) for local use by typing:
```
leanproject get tutorials
```

Then, in the `tutorials/src` folder, create a copy of the exercises folder for you work.
This way it won't be overwritten if you update the project to get new exercices. 
You can then open the tutorials folder in VS code.
For instance you can type:
```
cp -r tutorials/src/exercises tutorials/src/my_exercises
code tutorials
```
VSCode has a file explorer that you can open by clicking the top icon in 
the icon column on the left. In this explorer, you can navigate to
`src/my_exercises` and click on `00_first_proofs.lean`.
This file does not contain any exercise, it is meant as an
overview of the basics. You can skip it if you are really eager to start
coding, but this is not recommended. You don't need to understand
everything while reading this file, only try to get a feel for what it's
looking like, and maybe start picking up some key words.

There are solutions for all the exercises in `src/solutions`. If you
need help about any specific exercise. You can come on 
[Zulip](https://leanprover.zulipchat.com) in the "new members" stream
and look for a thread called "tutorials NNNN" where NNNN is the exercise
number. If no such thread exists, you can create one!
