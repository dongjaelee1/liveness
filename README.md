### Installation (not tested)

1. Setup a new opam switch and switch to it:
  ```
  opam update
  opam switch create liris 5.2.1
  eval $(opam env)
  ```

2. Add the Coq opam repository (maybe also iris-dev): 
```
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```
3. (New) Install parametric Iris:
```
  git clone https://gitlab.mpi-sws.org/dongjae/iris.git
  cd iris
  git checkout dongjae/parametric-index
  make builddep
  make -j8
  make install
```
  Install transfinite Iris:
```
  git clone https://gitlab.mpi-sws.org/dongjae/transfinite-parametric-stepindex.git
  cd transfinite-parametric-stepindex
  git checkout dongjae/parametric-index
  make -j8
  make install
```
  Install additional libraries:
```
  ./configure
```

4. Run `make -jN` to build the full development, where `N` is the number of threads
   to use for the build process.

## Acknowledgements

Files in `cgraphs/` directory are modifications of files from https://github.com/julesjacobs/cgraphs.
The paper is available at:
* "Connectivity graphs: a method for proving deadlock freedom based on separation logic"
  by Jules Jacobs, Stephanie Balzer, and Robbert Krebbers, POPL 2022.
  See https://dl.acm.org/doi/abs/10.1145/3498662

(Transfinite Iris) The mechanization of set-theoretic ordinals and the underlying ZF model construction 
has been based on Coq code by Dominik Kirst and Gert Smolka, available at: 

* "Large Model Constructions for Second-Order ZF in Dependent Type Theory"
  by Dominik Kirst and Gert Smolka, CPP 2018
  See https://www.ps.uni-saarland.de/Publications/details/KirstSmolka:2017:Large-Model.html.
* "Formalised Set Theory: Well-Orderings and the Axiom of Choice", Dominik Kirst. 
  See https://www.ps.uni-saarland.de/~kirst/bachelor.php 
