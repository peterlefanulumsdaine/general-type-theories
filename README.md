# General type theories

A (formalised) general definition of type theories.

## What is a general type theory?

We consider general type theories of the *Martin-Löf style*. In this section we lay down
the basic concepts but do *not* discuss how they are formalized. You will find here the
*naive mathematical decscription* of the concepts we intend to formalize. For the purposes
of formalization we may introduce additional intermediate concepts (but it is better if we
do not have to, so eventually we should have a perfect match between the formalized
notions and the intended mathematical ones).

### Syntactic entities

There are two syntactic classes: **terms** and **types**. An expression can be one or the
other but not both. (In particular this means we shall have Tarski-style universes.) We
call these **raw** terms and types in order to emphasize that they are just syntactic
entities which need not be well-formed.

The theory is **dependent** (types depend on terms) and has **binding operators** (such as ∏, Σ,
λ). Therefore, we need to describe **shapes** of contexts and binding operators. Two
possibilities for shapes are *de Bruijn indices* and *named variables*, but these are not the
only ones. Thus we define a general abstract notion of shapes, which we then use to
express the structure of contexts and binding operators.

The raw syntax is generated from a **raw signature** (we use the qualifier "raw" to remind
ourselves that such a signature describes only the raw syntax, i.e., the syntactic classes
and the binding structure). The raw signature lists a number of term and type
constructors, together with their arities. An **arity** is a higher-order one, i.e., it
tells us not only how many arguments the constructor expects, but also how it binds
variables.

### Judgments

There are the following **judgment forms:**

1. `Γ ctx` – "`Γ` is a context"
2. `Γ ⊢ A type` – "`A` is type in context `Γ`"
3. `Γ ⊢ t : A` – "`t` is a term of type `A` in context `Γ`"
4. `Γ ⊢ A ≡ B` – "type `A` and `B` are equal in context `Γ`"
5. `Γ ⊢ s ≡ t : A` – "terms `s` and `t` of type `A` are equal in context `Γ`"

Each judgment has a **boundary**, which consists of several structurally smaller judgments (by
"structurally smaller" we mean that the syntactic entities appearing in the boundary are
subentities of the judgment). We say that a boundary is **well-formed** when the judgments in
its boundary are derivable. The boundaries are as follows:

1. the boundary of `Γ ctx` is empty
2. the boundary of `Γ ⊢ A type` is `Γ ctx`
3. the boundary of `Γ ⊢ t : A` is `Γ ⊢ A type`
4. the boundary of `Γ ⊢ A ≡ B` is ``Γ ctx``,  `Γ ⊢ A type`, and `Γ ⊢ B type`
5. the boundary of `Γ ⊢ s ≡ t : A` is ``Γ ctx``, `Γ ⊢ A type`, `Γ ⊢ s : A`, and `Γ ⊢ s : A`

### Rules

Given a raw signature `Σ`, we may form **(inference) rules**. Each inference rule consists
of two parts:

* the **raw rule** specifying a family of **premises** and a **conclusion**
* evidence that the **raw rule** is well-formed

The precise structure of a raw rule is as follows:

* A raw rule refers to a family **meta-variables**, each of which is either a **type
  meta-variable** or a **term meta-variable**.
* The premises and the conclusion are judgments over `Σ` that may refer to the
  meta-variables.

The evidence that a raw rule is well-formed consists of, for each premise and the
conclusion, a derivations witnessing the fact that the boundaries are well-formed, under
the hypotheses that the meta-variables signify well-formed terms and types.

#### Structural rules

There are rules which we insist on having, called the **structural rules**. These are:

* rules governing formation of contexts
* variable rules
* reflexivity, symmetry and transitivity of equality
* equality is a congruence with respect to all type and term formers

#### Rule instances

Given a rule, we may form a **rule instance** by replacing the meta-variables appearing in
it with suitable instances. Of course, when doing so, we need to provide evidence that the
instances are well-formed typed and terms.

### Derivations

A **general type theory** `T` is given by a shape `σ`, a signature `Σ` over `σ`, and a
family of inference rules over `Σ`.

A derivation of a judgment `J` from a family of rules `R` hypotheses `H` is an inductively
generated tree whose conclusion is `J`, the leaves are the elements of `H`, and the nodes
are rule instances from `R`.

### The interdependence of derivations and rules

While a shape `σ` and a raw signature `Σ` may be given without many complications, there
is considerable interdependence between inference rules because giving the evidence that a
rule is well-formed requires one to provide derivations, but to know what a derivation is,
we need to be given inference rules.



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
* [`Raw`](./Raw) -- raw syntax, raw rules, raw type theories
* [`Typed`](./Typed) -- typing derivations, (typed) type theories


## Authors

* Andrej Bauer
* Philipp Haselwarter
* Peter LeFanu Lumsdaine
