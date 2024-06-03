# learning_lean

## Youtube channel for learning Lean 4

Here is a link of live proving tutorials from this repo: https://www.youtube.com/playlist?list=PLB3sDpSRdrOt68MTR6kdI0Jc85Uuw1YWV

## Setup

**Do not** run `install.sh` blindly. 
There is no guarantee it will work on your machine. 
Therefore, understand each command and only run the next command if the current one succeeded. 

## Main Concepts

- Lean 4 Project := Usually a Lean 4 project is the root of the github repo. It usually has the `lakefile.lean`, `lean-toolchain` files, `.lake`, `Folder_With_Lean_Code`, etc. 
In our case the root of the repo is not the Lean 4 project and instead with have a seperate folder for the Lean 4 source code (that will be the root of the Lean 4 project) at `learning_lean/lean_src_proj`. 
- Github project root := For pure Lean 4 Projects it's the same as the root of the Lean 4 project root. For that's not the case and there might be an additional `py_src` too. 

## For developing Lean in this repo

If you git cloned this repo with say `git clone git@github.com:brando90/learning_lean.git` then you will have the lean project `lean_src_proj` folder and it won't have it's Lean depedencies e.g., Mathlib or the `.lake` folder will be missing. 

If that is the case, then you need to install mathlib for this project (note doing `lake +leanprover/lean4:nightly-2023-02-04 new my_project math` as suggested by the Lean [projects setup will fail](https://leanprover-community.github.io/install/project.html#creating-a-lean-project) does **not work**) with:
```bash
# Go to root main github repo (in this case, it's not the Lean 4 project)
cd $HOME/learning_lean
git clone git@github.com:brando90/learning_lean.git
# Go to the Lean 4 proj path (at `learning_lean/lean_src_proj`)
cd lean_src_proj
# Set up Lean 4 & Mathlib
## Note: the official Lean 4 tutorial command `lake +leanprover/lean4:nightly-2023-02-04 new my_project math` doesn't work here + it creates a .git folder that we don't want
lake update
lake exe cache get
code .
```

## Lean useful links

Lean manual: https://lean-lang.org/lean4/doc/ (similar to [Coq's awesome docs](https://coq.inria.fr/doc/V8.19.0/refman/language/core/inductive.html?highlight=inductive#coq:cmd.Inductive))
