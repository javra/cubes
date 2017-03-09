A Formalization of Cubical Sets in Lean
=======================================

Preliminaries:

* [fi](fi.lean): The inductive family of finite ordinal types

Basics of cubical sets:

* [cubes](cubes.lean): The cube category for arbitrary name systems
* [cubes_list](cubes_list.lean): The cube category for lists
* [cubes_fin](cubes_fin.lean): The cube category for finite types
* [cset](cset.lean): Declaration of cubical sets
* [kan](kan.lean): The uniform Kan condition on cubical sets

Constructions on Kan cubical sets:

* [sigma](sigma.lean): Kan cubical sets model sigma types
* [pi](pi.lean): Kan cubical sets model pi types

These constructions are loosely based on Simon Huber's version of cubical
sets as a model for Homotopy Type Theory, which you can find
[online](http://www.cse.chalmers.se/~simonhu/misc/lic.pdf).