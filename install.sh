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