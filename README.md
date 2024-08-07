# learning_lean

## Youtube channel for learning Lean 4

Here is a link of live proving tutorials from this repo: https://www.youtube.com/playlist?list=PLB3sDpSRdrOt68MTR6kdI0Jc85Uuw1YWV

## Setting up Lean 4

To set up Lean 4 follow the following instructions:
```bash
# -- Setup our lean_src_proj Lean 4 project for the first time (ref: https://leanprover-community.github.io/install/project.html#lean-projects)
# - Go to a folder where you want to create a Lean 4 project (e.g., the root of this `learning_lean` git repo)
cd $HOME/learning_lean
# - Then create the Lean 4 project with the following options (note: usually a Lean 4 project's path **is** the same as the root of the github repo, but not for us)
# Option 1: setting up the Lean 4 project at `lean_src_proj`` for the first time (& installing Mathlib)
lake +leanprover/lean4:nightly-2023-02-04 new lean_src_proj math
# Option 2: set up Lean 4 project at `lean_src_proj` if the path `lean_src_proj` already exists but Mathlib has not been installed (e.g., after git cloning the root git repo `learning_lean`)
cd lean_src_proj
lake update
lake exe cache get
# if you get an error message saying lake is an unknown command and you have not logged in since you installed Lean, then you may need to first type 
# source ~/.profile or source ~/.bash_profile
# -- Go inside Lean 4 project dir and set it up 
# cd to the Lean 4 project folder
cd lean_src_proj
# Update the dependencies and fetch the latest versions specified in the lakefile (in your Lean 4 project's at `lean_src_proj`)
lake update 
# Retrieve the cached files to speed up subsequent builds and ensure the latest cached versions are used
lake exe cache get
# -- The Lean code *.lean for your Lean 4 project (located at `learning_lean/lean_src_proj`) should be at learning_lean/lean_src/MyProject/ or a subfolder thereof.
# - Go to root of Lean 4 project in this github repo
cd $HOME/learning_lean/learn_src_proj
# Create 1st folder with the Lean 4 src code will like for our Lean 4 project (at the path `learning_lean/learn_src_proj`)
mkdir MyLean4CodeFolder1
cd MyLean4CodeFolder1
echo 'import Mathlib.Topology.Basic\n\n#check TopologicalSpace' > Test.lean
# Create 2nd folder with the Lean 4 src code will like for our Lean 4 project (at the path `learning_lean/learn_src_proj`)
mkdir MyLean4CodeFolder2
cd MyLean4CodeFolder2
echo 'import Mathlib.Topology.Basic\n\n#check TopologicalSpace' > Test.lean
# Create 3rd folder with Lean 4 code
cd $HOME/learning_lean/lean_src_proj
mkdir AesopExample
cd AesopExample
echo -e 'import Aesop\n\nexample : α → α :=\n  by aesop' > AesopExample/aesop_example.lean
# Add Aesop dependency to lakefile.lean if not already present
if ! grep -q 'require aesop from git "https://github.com/JLimperg/aesop"' lakefile.lean; then
  echo 'require aesop from git "https://github.com/JLimperg/aesop"' >> lakefile.lean
  echo "Added Aesop dependency to lakefile.lean."
else
  echo "Aesop dependency already exists in lakefile.lean."
fi
# Recompile Lean 4 Project at `learning_lean/lean_src_proj`
cd $HOME/learning_lean/lean_src_proj
lake update
lake exe cache get
# lake build

# ...etc...
# Note: confusingly, the official tutorial for creating a Lean 4 project (which for them is usually the root of the git repo) has a folder named `my_project/MyProject/` 
# (or a subfolder thereof), for details see: https://leanprover-community.github.io/install/project.html
# but for us our Lean 4 project is not the root but instead is at `learning_lean/lean_src_proj` with folder with *.lean files in the subfolders there e.g., 
# `MyLean4CodeFolder1`, `MyLean4CodeFolder2`, ...etc... 
```

**Do not** run `install.sh` blindly. 
There is no guarantee it will work on your machine. 
Therefore, understand each command and only run the next command if the current one succeeded. 

## Main Concepts

- Lean 4 Project: Usually a Lean 4 project is the root of the github repo. It usually has the `lakefile.lean`, `lean-toolchain` files, `.lake`, `Folder_With_Lean_Code`, etc. 
In our case the root of the repo is not the Lean 4 project and instead with have a seperate folder for the Lean 4 source code (that will be the root of the Lean 4 project) at `learning_lean/lean_src_proj`. 
- Github project root: For pure Lean 4 Projects it's the same as the root of the Lean 4 project root. For that's not the case and there might be an additional `py_src` too. 

### Tools in a Lean 4 Project

- `elan`: (for the PL e.g., `Lean4` like something that would manage `python`)
  - `elan` is a version manager for the Lean programming language, similar to `pyenv` or `conda` for Python.
  - It allows users to install and manage multiple versions of Lean, ensuring that each project can use the specific version it requires.
  - `elan` reads the `lean-toolchain` file in a project to automatically switch to the correct Lean version when working on that project.

- `lake`: (for the pkg depedencies e.g., cmd similar for deps management for `conda` or `pip`)
  - `lake` is the package manager and build system for Lean 4, akin to `pip` and `poetry` for Python.
  - It manages project dependencies, configuration, and the build process, specified in the `lakefile.lean`.
  - `lake` facilitates the setup and compilation of Lean projects, ensuring all dependencies are resolved and build steps are executed as defined.

### Files in a Lean 4 Project
ref: https://chatgpt.com/g/g-689rdwbPb-dsp-for-lean4/c/9b13ceec-7fc8-4c29-b809-666145781b16

- `lean-toolchain`: 
  - This file specifies the version of the Lean programming language and any additional dependencies required for a Lean project (~ `conda`).
  - It ensures that all users of the project use the same Lean version for consistency and compatibility.
  - `elan` reads this file `lean-toolchain` to automatically set up the specified Lean version when working on the project, similar to how `conda` uses an `environment.yml` file to manage Python environment or
  `pyenv` uses `.python-version` to manage Python versions. 
  - Example content:
    ```
    leanprover/lean4:nightly-2022-09-22
    ```

- `lakefile.lean`: 
  - This file defines the configuration and dependencies for a Lean project using Lake, the Lean package manager and build system.
  - It includes settings such as package dependencies, build options, and project-specific commands or scripts.
  - `lakefile.lean` orchestrates the project's build process and manages external Lean libraries, similar to how `pyproject.toml` works for Python projects using Poetry.
  - Example content:
    ```lean
    import Lake
    open Lake DSL

    package myPackage {
      -- add package configuration options here
    }

    lean_lib MyLib {
      -- add library configuration options here
    }

    @[defaultTarget]
    lean_exe myExe {
      root := `Main
    }
    ```

Note: While `lean-toolchain` ensures that all users of the project use the same version of the Lean compiler for consistency, `lakefile.lean` manages the project's dependencies and build configuration, specifying additional Lean libraries and build scripts required for the project's development and build process; thus, `lean-toolchain` handles the core Lean compiler version, whereas `lakefile.lean` handles project-specific library dependencies (e.g., Mathlib, Aesop).


## For developing Lean in this repo
ref: https://chatgpt.com/c/8f00638c-0fe0-475d-8bad-51b0e6e0655a

If you git cloned this repo with say `git clone git@github.com:brando90/learning_lean.git` then you will have the lean project `lean_src_proj` folder and it won't have it's Lean depedencies e.g., Mathlib or the `.lake` folder will be missing. Thus, you should have `.lake` in your `.gitignore` file.

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


## Adding deps to Lean programmatically e.g., AESOP
ref: https://proofassistants.stackexchange.com/questions/4025/how-does-one-install-new-dependencies-to-a-lean-4-programatically-e-g-adding-a
