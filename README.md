# General type theories

A (formalised) general definition of type theories.

The formalization of the syntax of a general type theory proceeds in several stages:

1. We define *shape systems*, which serve as contexts, as well as binding "shapes" for
   quantifiers and abstractions.
2. The *raw level* of syntax in which we explain how to form and manipulate syntactic
   entities. This level takes care of the substitution and binding. It does not
   make sure that the syntactic entities or the rules of inference are well-typed.
3. TO BE CONTINUED.

## Naming conventions

We observe the following naming conventions.

### Use singular

All file names, section names, and identifiers which refer to a structure are in the
singular case. Thus it is `Theory.v` not `Theories.v`. An exceptions is `XYZExamples`.

### No abbreviations

We do *not* abbreviate any words without a written permission of all project members.

### Upper case `CamelCase` for files and sections

Names of files and sections should be written in the `CamelCase` style: each word is
capitalized, there are no underscores.

### Lower case with underscores for identifiers

All identifier names are in all lower letters, with underscores between words. Thus it is
`judgment_boundary` and *not* `JudgmentBdry` or `Judgment_Boundary`.

### Make definitions `Local`

In a file, use `Local Definition` rather than just `Definition` so that when we refer to
entities across files, we can tell which file we are referring to. For example, in
`Family.v` we place

    Local Definition fmap := ...

and then in some other file we refer to it with `Family.fmap`.

**Exception to the `Local` rule:** an identifiers such as `Family.family` can be defined
as non-local, provided that:

  * writing the fully qualified name looks redundant, e.g., `Family.family` and
  * it is highly unlikely that another file will contain the same identifier.

The following is *not* a valid reason for removing `Local`: *"But we use it very often."*

### Do not replicate the module name in the identifier

In a module `Foo`, do not define a `Local` identifier `foo_xyz`, instead define just
`xyz`. When we refer to `xyz` from outside the module it will look right `Foo.xyz`, and
you can live with the short name withing the module `Foo`.

Note that when `xyz` is declared global, e.g., it is the field name of a globally defined
`Record`, then it is ok to name it `foo_xyz`. (Example: field name `Family.family_index`.)


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
