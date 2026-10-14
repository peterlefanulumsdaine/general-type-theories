# Status: anomaly MWE

Done. `anomaly_mwe.v` (35 lines incl. comments, no dependencies, plain
`rocq compile`) reproduces the anomaly from `Typing/Presuppositions.v:232`
with the same backtrace, on 9.1.1 and on master (rocq-local switch,
9.3+alpha, 195cc6ea85). `ISSUE.md` is the draft report.

## Process

- Did not shrink the repo file by file. Instead, `Set Debug "tactic-unification"`
  on the original `apply fmap_presupposition_family` showed the problem
  directly: `Family.fmap (Judgement.fmap ?M) ~= Judgement.boundary_slot`
  (FO heads), delta + eta gives the ill-typed `family_index jf` with
  `jf : form`, and `form@{u}` has 1 universe level against `family_index@{u u0}`'s 2.
  The MWE was rebuilt from scratch on that pattern.
- Essential ingredients (each checked by a variant):
  - primitive projections on the record (`family`): without them, ordinary error;
  - universe polymorphism of the record: monomorphic `family` gives ordinary
    error (`Unable to find an instance for n`; `eapply` succeeds);
  - the variable's inductive (`form`) polymorphic with FEWER universe levels
    than the record (1 vs 2): 0 levels (Set) or 2 levels give no anomaly;
  - a meta inside the head (`fmap ?n`), otherwise closed-term conversion solves it;
  - `apply`/`eapply` (legacy unifier); `refine` works.
- The wrapping record `T` of earlier attempts and non-primitive vs primitive
  projections for it turned out irrelevant; `T` is an axiom now.
- Neither `-noinit` nor `-indices-matter` matters.
- Note: `Inductive form := fo | fe.` is lowered to Set (no anomaly), but the
  original `Inductive form : Type := ...` with constructors taking
  `syntactic_class` stays `form@{u}`; hence the explicit `form@{u} : Type@{u}`.

## Remaining questions

- The analysis of the cause is from reading the source + debug traces; not
  confirmed by patching Rocq.
- The same-length-instance case (2 levels) silently builds an
  ill-instantiated constant; whether that can cause other wrong behaviour is
  not explored.
- Versions other than 9.1.1 and master not tested.
