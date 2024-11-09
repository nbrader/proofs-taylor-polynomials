The aim of this project is to prove that a Taylor Polynomials must have their usual form if we specify the properties it should have.

Be aware, this project serves as a way for me to practice proving theorems in Coq.

For a much better library which proves Taylor's Theorem, see the following:
  http://coquelicot.saclay.inria.fr/html/Coquelicot.Derive.html

This project has a submodule. When first cloned, you may be required to run a "Submodule Update" such as when using the TortoiseGit context menu.

In order to view these files with the intended Coq parser, you should install:
- Visual Studio Code (1.94.2)
- VsCoq (v2.1.2)

You may find that Coq .v files can only be found by other Coq .v files when you've opened in Visual Studio Code the folder that directly contains that file (and not the parent folder) of multiple folders of .v files.

To build the project, locate the file called build_coq.sh and run it from the command line by typing "ctrl+'" and entering: ./build_coq.sh

Sometimes, the line endings aren't readable and you will first need to run: dos2unix build_coq.sh
