### Installation (not tested)

The development depends on parametric Iris and transfinite Iris, whose sources
are bundled in this repository as `iris-parametric-index.zip` and
`transfinite-parametric-index.zip`.

1. Set up a new opam switch and switch to it:
  ```
  opam update
  opam switch create liris 5.2.1
  eval $(opam env)
  ```

2. Run the configure script:
  ```
  ./configure
  ```
  This adds the required opam repositories, installs the Ordinal library, and
  then unpacks the bundled zip files into `vendor/` and builds and installs
  parametric Iris and transfinite Iris from them. Set `NJOBS` to control build
  parallelism (default 8), e.g. `NJOBS=4 ./configure`.

3. Run `make -jN` to build the full development, where `N` is the number of
   threads to use for the build process.

## Acknowledgements

The `liris/ordinal/` directory is a copy of the Ordinal library, available at
https://github.com/snu-sf/Ordinal.

(Transfinite Iris) The mechanization of set-theoretic ordinals and the underlying ZF model construction 
has been based on Coq code by Dominik Kirst and Gert Smolka, available at: 

* "Large Model Constructions for Second-Order ZF in Dependent Type Theory"
  by Dominik Kirst and Gert Smolka, CPP 2018
  See https://www.ps.uni-saarland.de/Publications/details/KirstSmolka:2017:Large-Model.html.
* "Formalised Set Theory: Well-Orderings and the Axiom of Choice", Dominik Kirst. 
  See https://www.ps.uni-saarland.de/~kirst/bachelor.php 
