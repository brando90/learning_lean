# -- Setup our lean_src_proj project for the first time (ref: https://leanprover-community.github.io/install/project.html#lean-projects)
# - Go to a folder where you want to create a project in a subfolder lean_src, and type lake +leanprover/lean4:nightly-2023-02-04 new lean_src math
# go to root of project (not the lean project)
cd $HOME/learning_lean
# Option1: (from scratch) set up the main lean_src_proj project for the first time:
lake +leanprover/lean4:nightly-2023-02-04 new lean_src_proj math
# Option 2: (for cloning project) set up main lean_src_proj project if you did a git clone of root learning_lean (so depedencies, e.g., matblib need to be installed)
# mkdir lean_src_proj
cd lean_src_proj
lake update
lake exe cache get
# if you get an error message saying lake is an unknown command and you have not logged in since you installed Lean, then you may need to first type 
# source ~/.profile or source ~/.bash_profile
# -- Go inside the clean_src folder and type `lake update``, then `lake exe cache get`` and then `mkdir MyProject``
cd lean_src_proj
# optionally: rm -rf lean_src_proj/.git
lake update 
lake exe cache get
# -- Your Lean code should now be put inside files with extension .lean living in lean_src/MyProject/ or a subfolder thereof.
mkdir MyProject
cd MyProject
echo 'import Mathlib.Topology.Basic\n\n#check TopologicalSpace' > Test.lean