# Coherence via Focusing for Symmetric Skew Monoidal Categories

The symmetric skew monoidal categories of Bourke and Lack are a weakening of Mac Lane’s symmetric monoidal categories where: (i) the three structural laws of left and right unitality and associativity are not required to be invertible, they are merely natural transformations with a specific orientation; (ii) the structural law of symmetry is a natural isomorphism involving three objects rather than two. 
We study the structural proof theory of symmetric skew monoidal categories, progressing the project initiated by Uustalu et al. on deductive systems for categories with skew structure. We discuss three equivalent presentations of the free symmetric skew monoidal category on a set of generating objects: a Hilbert-style categorical calculus; a cut-free sequent calculus; a focused subsystem of derivations, corresponding to a sound and complete goal-directed proof search strategy for the cut-free sequent calculus. Focusing defines an effective normalization procedure for maps in the free symmetric skew monoidal category, as such solving
the coherence problem for symmetric skew monoidal categories.


The file [symmetric/Main.agda](https://github.com/niccoloveltri/coh-symmskewmon/blob/main/symmetric/Main.agda) for the whole development.

The [braided](https://github.com/niccoloveltri/coh-symmskewmon/tree/main/) directory contains proof systems for the free braided skew monoidal category (but not a focused sequent calculus).


The code typechecks using Agda version 2.6.2 and Agda standard library version 1.6-dev.
