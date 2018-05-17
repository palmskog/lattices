# Lattice theory in Coq

Some simple lattice theory in Coq. Examples taken from chapter 2 of [_Ordered Sets and Complete Lattices_](http://profs.sci.univr.it/~giaco/paperi/lattices-for-CS.pdf).

### Requirements

* [Coq 8.7 or 8.8](https://coq.inria.fr)
* [Mathematical Components 1.6.4 or 1.7.0](http://math-comp.github.io/math-comp/) (`ssreflect`)
* [FCSL PCM library 1.0.0](https://github.com/imdea-software/fcsl-pcm)

### Building

We recommend installing the requirements via [OPAM](https://opam.ocaml.org/doc/Install.html):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect coq-fcsl-pcm
```

Then, run `make clean; make` from the root folder. This will build all
the libraries and check all the proofs.
