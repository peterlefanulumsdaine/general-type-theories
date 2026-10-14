# General type theories

A (formalised) general definition of type theories.

## Contributors

* Peter LeFanu Lumsdaine (lead author)
* Andrej Bauer
* Philip Haselwarter
* Théo Winterhalter

## Content

This repo contains a Coq formalisation of a general notion of dependent type theories, and the development of key metatheorems for this notion.

A human-readable presentation of the main notions can be found in Lumsdaine’s talk at HoTTEST Conference, 2020 [slides](https://www.uwo.ca/math/faculty/kapulkin/seminars/hottestfiles/Lumsdaine-2020-06-15-HoTTEST.pdf),
and an article presenting the work is in preparation.

## Development

The formalisation is under active development.

Some parts are fairly complete, while others are very much work in progress.

None of the formalisation should be considered stable.

## How to use this formalisation

The formalisation is written over [the HoTT library](https://github.com/HoTT/Coq-HoTT), and is currently tested with Rocq 9.1 and HoTT 9.1.

- Install Rocq and the HoTT library, e.g. via [opam](https://opam.ocaml.org).  We recommend doing this in a dedicated opam switch, since the HoTT library is tied closely to specific Rocq versions:

  ```
  opam switch create general-type-theories ocaml-base-compiler.5.3.0
  eval $(opam env --switch=general-type-theories)
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam install rocq-core.9.1.1 coq-hott.9.1
  opam switch set-invariant "rocq-core=9.1.1"   # optional: guards against accidental upgrades
  ```

- Invoke `make` from the base directory of this repository.

The build flags `-noinit` and `-indices-matter`, required by the HoTT library, are set in [`_CoqProject`](./_CoqProject).  Editors with Rocq support (Proof General, VsRocq, coq-lsp) pick them up from there automatically.

# Detailed overview

Note: the following overview is currently somewhat out of date.

## Directory overview

* [`Auxiliary`](./Auxiliary) -- mathematical generalities, not specifically about type theory
* [`Syntax`](./Syntax) -- raw syntax
* [`Typing`](./Typing) -- judgements, raw rules, raw type theories, typing derivations, presuppositions
* [`Presented`](./Presented) -- well-presented rules, type theories
* [`Metatheorem`](./Metatheorem) -- basic metatheorems about these type theories
* [`Example`](./Example) -- examples of scope systems, type theories, etc.

## Mathematical overview

We define a broad class of dependent type theories, which we call *Martin-Löf style*: roughly, theories with just the syntactic classes and judgement forms as Martin-Löf’s original, and arbitrary type- and term-formers, specified by rules that are *well-formed* in the generally-understood sense.

The main contribution is precisely codifying this traditional sense of **well-formed**.

This overview discusses the non-formalised mathematical intent. Some extra technical devices used in the formalisation are glossed over here.

### Variable-handling

We abstract variable-handling in terms of **scope systems**.  A scope specifies the variables of a context: so for de Bruijn indices it is just a number, the length; or for named variables, a finite set of identifiers.

Formally, a **system of scopes** is an indexed family of sets (typically but not necessarily finite) equipped with operations for sums and extension-by-one, and an empty scope.

### Syntactic entities

A type theory will be specified by **raw syntax** plus **typing rules**; we set up the raw syntax first, specified by a **signature**.

Our theories will include **binding operators** (such as ∏, Σ, λ); so signatures must be higher-order to specify the arities of these. 

Formally, there are two **syntactic classes**: **terms** and **types**. A **raw signature** consists of a collection of symbols, each with a class and an **arity** specifying its arguments and their bindings.

**Raw expressions** over a signature Σ are then defined as an inductive family, as usual, indexed by class and scope: for each scope γ, there are sets of (raw) **type expressions** and **term expressions** over  Σ in scope γ.  We call these **raw** terms and types to emphasise they need not be well-formed.

(The strict separation of syntactic classes mean in particular our theories can have Tarski-style universes, not Russell-style.) 

### Judgments

Well-formedness will be given by an inductively defined **derivability** relation on judgements.

There are four primary **judgment forms:**

1. `Γ ⊢ A type` – "`A` is type in context `Γ`"
2. `Γ ⊢ t : A` – "`t` is a term of type `A` in context `Γ`"
3. `Γ ⊢ A ≡ B` – "type `A` and `B` are equal in context `Γ`"
4. `Γ ⊢ s ≡ t : A` – "terms `s` and `t` of type `A` are equal in context `Γ`"

Other possible judgement forms — contexts and substitutions — will be defined afterwards from these, as **derived judgements**.

Each judgment has various **presuppositions**, which together form its **boundary**:

1. `Γ ⊢ A type` has no presuppositions
2. `Γ ⊢ t : A` has one presupposition, `Γ ⊢ A type`
3. `Γ ⊢ A ≡ B` has presuppositions `Γ ⊢ A type` and `Γ ⊢ B type`
4. `Γ ⊢ s ≡ t : A` has presuppositions `Γ ⊢ A type`, `Γ ⊢ s : A`, `Γ ⊢ s : A`

Less conventionally, we take `⊢ Γ context` to be an abbreviation for the judgements `Γ ⊢ A type`, for all types `A` of `Γ`.  So contexts are **flat** — no ordering is assumed, and well-formedness of their types is assumed just for the point of use.  Typically contexts will be built up sequentially as usual, but we don’t assume this.  Similary we define a derived judgement of **substitutions** between contexts.

### Rules

Given a raw signature `Σ`, we may form **(inference) rules**. Each inference rule consists of two parts:

* the **raw rule** specifying a family of **premises** and a **conclusion**
* evidence that the **raw rule** is well-formed

The precise structure of a raw rule is as follows:

* A raw rule refers to a family **meta-variables**, each of which is either a **type meta-variable** or a **term meta-variable**.
* The premises and the conclusion are judgments over `Σ` that may refer to the meta-variables.

The evidence that a raw rule is well-formed consists of, for each premise and the conclusion, a derivations witnessing the fact that the boundaries are well-formed, under the hypotheses that the meta-variables signify well-formed terms and types.

#### Structural rules

There are rules which we insist on having, called the **structural rules**. These are:

* rules governing formation of contexts
* variable rules
* reflexivity, symmetry and transitivity of equality
* equality is a congruence with respect to all type and term formers

#### Rule instances

Given a rule, we may form a **rule instance** by replacing the meta-variables appearing in it with suitable instances. Of course, when doing so, we need to provide evidence that the instances are well-formed typed and terms.

### Derivations

A **general type theory** `T` is given by a scope `σ`, a signature `Σ` over `σ`, and a family of inference rules over `Σ`.

A derivation of a judgment `J` from a family of rules `R` hypotheses `H` is an inductively generated tree whose conclusion is `J`, the leaves are the elements of `H`, and the nodes are rule instances from `R`.

### The interdependence of derivations and rules

While a scope `σ` and a raw signature `Σ` may be given without many complications, there is considerable interdependence between inference rules because giving the evidence that a rule is well-formed requires one to provide derivations, but to know what a derivation is, we need to be given inference rules.

## Coding conventions

We observe the following naming conventions.

### Use singular

All file names, section names, and identifiers which refer to a structure are in the singular case. Thus it is `Theory.v` not `Theories.v`. An exceptions is `XYZExamples`.

### No abbreviations

We do *not* abbreviate any words without a written permission of all project members.

### Upper case `CamelCase` for files and sections

Names of files and sections should be written in the `CamelCase` style: each word is capitalized, there are no underscores.

### Lower case with underscores for identifiers

All identifier names are in all lower letters, with underscores between words. Thus it is `judgment_boundary` and *not* `JudgmentBdry` or `Judgment_Boundary`.

### Make definitions `Local`

In a file, use `Local Definition` rather than just `Definition` so that when we refer to entities across files, we can tell which file we are referring to. For example, in `Family.v` we place

    Local Definition fmap := ...

and then in some other file we refer to it with `Family.fmap`.

**Exception to the `Local` rule:** an identifiers such as `Family.family` can be defined as non-local, provided that:

  * writing the fully qualified name looks redundant, e.g., `Family.family` and
  * it is highly unlikely that another file will contain the same identifier.

The following is *not* a valid reason for removing `Local`: *"But we use it very often."*

### Do not replicate the module name in the identifier

In a module `Foo`, do not define a `Local` identifier `foo_xyz`, instead define just `xyz`. When we refer to `xyz` from outside the module it will look right `Foo.xyz`, and you can live with the short name withing the module `Foo`.

Note that when `xyz` is declared global, e.g., it is the field name of a globally defined `Record`, then it is ok to name it `foo_xyz`. (Example: field name `Family.family_index`.)

### Boilerplate

Many key constructions have a lot of related boilerplate — typically some of the following:

- access functions
- coercion declarations
- equality lemmas (how to conveniently prove two widgets are equal; or, better, an equivalence between the equality type on widgets and some tractable type)
- functoriality lemmas (widgets are functorial in maps of some of their arguments)
- category structure (widgets form a category, or a displayed category over some of their arguments

Such boilerplate should typically be given straight after the definition of widgets, in roughly the above order, except when there are specific reasons to defer it.

See also “categories and functoriality” below.

### Categories and functoriality

Many constructions involved form categories, and/or are functorial/natural in some of their arguments, and keeping track of this systematically is crucial.

Functoriality of a construction `widget` should be given as a lemma `widget_fmap`, or if `widget` is the core notion of a modula `Widget`, as a local lemma `fmap`, exported as `Widget.fmap`.

If widgets are thought of as just forming a set/type, with no further category structure, then there should be further lemmas `Widget.fmap_idmap`, `Widget.fmap_compose` giving the functoriality laws up to equality, and these should all directly follow the definition of widgets.

When widgets form a *category* — or, more typically, a *fibration* or *displayed category* over some previously-defined category (e.g. families form a fibration over sets/types) — then their (displayed) maps and category structure should directly follow their definition, and their `fmap` lemma (i.e. the demonstration that the displayed category is a fibration) should follow these.

Maps of widgets should be defined as `Widget.map`, or `Widget.map_over` for displayed maps over some map(s) of the parameters, composition as `Widget.compose`, and so on.

### Kleisli-like categories

In some case, the main notion of map for some object is something like a Kleisli map: e.g. for type theories, a “map of type theories” may take a symbol of the source theory not just to an atomic symbol but more generally to any suitably-derivable *term* of the target theory.

However, setting up the category of such maps usually requires first developing the corresponding *simple maps*, e.g. where each symbol of the source theory is sent just to a suitable symbol of the target theory.

In this case, we distinguish the simple structure as e.g. `Widget.simple_map`, `Widget.simple_compose`, and so on; or when we wish to think of the simple notion as primary, we distinguish the Kleisli notions as `Widget.kleisli_map`, etc.

### Layout

- all code should be kept to line lengths ≤80 chars

- running text in comments should be either hard-wrapped to length ≤80 chars, or non-wrapped, with blank lines to separate paragraphs in either case.  (Please try not to hard-wrap text to longer line lengths; that becomes nasty to read in windows with shorter line lengths.) 

- indent in steps of 2 spaces

- symbols like `:`, `:=` that are high in the parse-tree of a declaration should go at the *beginning* of lines for quick visibility, not at the end of lines, where they get lost; so

    Definition idfun {X : Type}
      : X -> X
    := fun x => x.

- in short declarations they can be mid-line, e.g. 

    Definition idfun {X : Type} : X -> X := fun x => x.

- in tactic proofs, when a tactic spawns multiple subgoals, *always* use bullets or some other form of focusing to separate the proofs of the subgoals.  So never write

      destruct x as [ y | z ].
      tactic1.
      tactic2.
      tactic3.
    Qed.

but instead something like (A): 

      destruct x as [ y | z ].
      - tactic1.
      	tactic2.
      - tactic3.
    Qed.

or (B)

      destruct x as [ y | z ].
      2: { tactic3. }
      tactic1.
      tactic2.
    Qed.

- focusing with bullets as in (A) is usually better if both/most subproofs are long; brackets as in (B) are good when all subproofs except one are short (~one-liners), since they avoid extra indentation in this case.  (Most often relevant when composing a long chain of equalities or morphisms.)
