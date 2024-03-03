# learning_lean

## Youtube channel for learning Lean 4

Here is a link of live proving tutorials from this repo: https://www.youtube.com/playlist?list=PLB3sDpSRdrOt68MTR6kdI0Jc85Uuw1YWV

## Setup

**Do not** run `install.sh` blindly. 
There is no guarantee it will work on your machine. 
Therefore, understand each command and only run the next command if the current one succeeded. 

## For developing Lean in this repo

If you git cloned this repo with say `git clone git@github.com:brando90/learning_lean.git` then you will have the lean project `lean_src_proj` folder and it won't have it's Lean depedencies e.g., Mathlib or the `.lake` folder will be missing. 

If that is the case, then you need to install mathlib for this project (note doing `lake +leanprover/lean4:nightly-2023-02-04 new my_project math` as suggested by the Lean [projects setup will fail](https://leanprover-community.github.io/install/project.html#creating-a-lean-project) does **not work**) with:
```bash
# go to root project/main repo
cd $HOME/learning_lean
git clone git@github.com:brando90/learning_lean.git
# go to lean proj
mkdir lean_src_proj
cd lean_src_proj
# set up lean4 & mathlib
##--> doesn't work here + it creates a .git folder that we don't want: lake +leanprover/lean4:nightly-2023-02-04 new my_project math (from Lean community)
lake update
lake exe cache get
code .
```

## Lean useful links

Lean manual: https://lean-lang.org/lean4/doc/ (similar to [Coq's awesome docs](https://coq.inria.fr/doc/V8.19.0/refman/language/core/inductive.html?highlight=inductive#coq:cmd.Inductive))
