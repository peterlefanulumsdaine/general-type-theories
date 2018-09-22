Not as much large-scale reorganisation this time as in Andrej’s big sweep, but still a fair bit.

# Large changes:

## Functoriality/naturality lemmas:

- mostly, functoriality/naturality lemmas for a definition go directly after the definition, certainly in the same file (even if not needed until further downstream)

- exception: when instances of a definition form the objects of a fibered category (e.g. raw tt’s fibred over signatures); then the “functoriality” in base morphisms follows the def of the morphisms of the new objects (since it’s seen as showing that the new category really is a fibration over the old)

This greatly helps with keeping the organisation of lemmas consistent and comprehensible.

## Directory grouping

Very unsure what’s best here.  Trying out a new grouping:

- Raw: everything just about the raw syntax, before one considers it as a typed syntax at all.  Pretty much: stuff that might be provided by a library purely about untyped (or maybe multi-sorted) syntax-with-binding.
- Typing: everything involved in setting up the typing judgements.  Contexts, judgements, structural rules, flat rules and type theories, and derivations over these.
- Presented: well-presented rules and type theories.

# Specific spot notes

## Substitution/renaming:

I’ve moved `rename` into `Expression.v`, on grounds that it’s part of the functoriality of expressions (and its lemmas similarly).  Cost: the expository clarity of having it right next to substitution, so that the full def of substitution can be seen at a glance. But in most/all other ways this arrangement seems better.

## SyntaxLemmas.v

This file was a big mess; I’ve broken it up entirely, and moved all lemmas upstream to go with the things they’re about — e.g. the lemmas on substitution are with substitution, and so on.

## Context.map renamed to raw_context_map

The old name was slightly nicer; but in terms of actual mathematical content and dependencies, [raw_context_map] naturally belongs in [Substitution], since it’s needed there, and neither it nor any of its lemmas depend on anything about raw contexts; whereas raw contexts do make use of substitution.  So [raw_context_map] really seems to want to live upstream from the rest of [Context.v], in every respect except naming.

## Instantiation vs. Judgements/Contexts

Previously, `Metavariable.v` came after `Judgement.v`, `Context.v`; now it comes before.  This allows definitions like instantiation of judgements to go with judgements, not with instantiation, fitting the general placement of functoriality-type statements.

# Still to do:

General functoriality/categorical conventions:

- pass through all files to generally get functoriality lemma placement consistent
- ditto to make functoriality section naming consistent
- consider organisation of categorical structure in [FlatTypeTheory].

Contexts and judgements:

- in Context.v: perhaps make (simple) context maps over shape maps more explicit/methodical (and same with judgements)?
- organisation in Judgement.v: quite complex, consider it!
- refactor judgements so that shape parameter less deeply nested

Utility derivations, flat rules, etc:

- move utility derivations upstream of flat type theories (both UtilityDerivations.v and the section currently in FlatTypeTheory.v) 
- export these utility derivs in a form that works immediately over any flat tt (coming from internal form working over just structural rules)

Presented rules, type theories

- try to unify the files for raw/typed versions of alg exts, presented rules, TT’s (there’s no obvious dependency reason not to).