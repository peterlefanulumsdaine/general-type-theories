# General type theories

A (formalised) general definition of type theories.

The formalization of the syntax of a general type theory proceeds in several stages:

1. We define *shape systems*, which serve as contexts, as well as binding "shapes" for
   quantifiers and abstractions.
2. The *raw level* of syntax in which we explain how to form and manipulate syntactic
   entities. This level takes care of the substitution and binding. It does not
   make sure that the syntactic entities or the rules of inference are well-typed.
3. TO BE CONTINUED.


## Code structure

* [`Auxiliary`](./Auxiliary) -- mathematical generalities
* [`Proto`](./Proto) -- shape systems
* [`Raw`](./Raw) -- raw syntax and type theories
* [`WellFormed`](./WellFormed) -- only Peter knows
* [`WellTyped`](./WellTyped) -- only Peter knows


## Authors

* Andrej Bauer
* Philipp Haselwarter
* Peter LeFanu Lumsdaine
