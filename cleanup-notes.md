Not as much large-scale reorganisation this time as in Andrej’s big sweep, but still a fair bit.

# Large changes:

## Functoriality/naturality lemmas:

- mostly, functoriality/naturality lemmas for a definition go directly after the definition, certainly in the same file (even if not needed until further downstream)

- exception: when instances of a definition form the objects of a fibered category (e.g. raw tt’s fibred over signatures); then the “functoriality” in base morphisms follows the def of the morphisms of the new objects (since it’s seen as showing that the new category really is a fibration over the old)

This greatly helps with keeping the organisation of lemmas consistent and comprehensible.

## Directory grouping

Very unsure what’s best here.

# Specific spot notes

## Substitution/renaming:

I’ve moved `rename` into `Expression.v`, on grounds that it’s part of the functoriality of expressions (and its lemmas similarly).  Cost: the expository clarity of having it right next to substitution, so that the full def of substitution can be seen at a glance. But in most/all other ways this arrangement seems better.

## SyntaxLemmas.v

This file was a big mess; I’ve broken it up entirely, and moved all lemmas upstream to go with the things they’re about — e.g. the lemmas on substitution are with substitution, and so on.

## Context.map renamed to raw_context_map

The old name was slightly nicer; but in terms of actual mathematical content and dependencies, [raw_context_map] naturally belongs in [Substitution], since it’s needed there, and neither it nor any of its lemmas depend on anything about raw contexts; whereas raw contexts do make use of substitution.  So [raw_context_map] really seems to want to live upstream from the rest of [Context.v], in every respect except naming.

## Instantiation vs. Judgements/Contexts

Previously, `Metavariable.v` came after `Judgement.v`, `Context.v`; now it comes before.  This allows definitions like instantiation of judgements to go with judgements, not with instantiation, fitting the general placement of functoriality-type statements.

STILL TODO:

- go through all files to generally get functoriality lemma placement consistent
- organisation in Judgement.v: quite complex, consider it!
- refactor judgements so that shape parameter less deeply nested
