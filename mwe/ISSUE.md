# Anomaly "index out of bounds" in `apply`: projection expanded with the universe instance of an unrelated inductive

## Description of the problem

With universe polymorphism and primitive projections, `apply` / `eapply` can raise

```
Error: Anomaly "Uncaught exception Invalid_argument("index out of bounds")."
Please report at http://rocq-prover.org/bugs/.
```

The anomaly arises in the legacy unifier (`Unification`), when first-order
unification plus delta/eta produces an ill-typed projection `index jf` (with
`jf` not of the record type), and that projection is then expanded to its
compatibility constant.

Originally found in a real development (a formalisation of type theories over
the HoTT library); the file below is a library-free reduction.

## Small Rocq file to reproduce the bug

```coq
Set Universe Polymorphism.
Set Primitive Projections.

(* A polymorphic primitive record with 2 universe levels: index@{u u0}. *)
Record family (X : Type) := { index : Type }.

Definition fmap (n : nat) (K : family nat) : family nat
  := {| index := index _ K |}.

(* A polymorphic inductive with only 1 universe level (fewer than [family]). *)
Inductive form@{u} : Type@{u} := fo.

Axiom K : family nat.
Definition slot (jf : form) : family nat := K.

Axiom T : family nat -> Type.
Axiom lemma : forall n P, T (fmap n P).

Goal forall x, T (slot x).
Proof.
  intros.
  apply lemma. (* Anomaly; [eapply lemma] too. *)
Abort.
```

Compiled with plain `rocq compile anomaly_mwe.v` (no extra flags).

## Version of Rocq where this bug occurs

- 9.1.1 (OCaml 5.3.0): anomaly.
- master, 9.3+alpha (commit 195cc6ea851650bfe63a667865bb4cc1a6424887, 2026-06-10): anomaly, same backtrace.

Other versions not tested.

## Expected behaviour

No anomaly. Without universe polymorphism on `family`/`fmap` (only `form`
kept polymorphic), the same `apply lemma` gives the ordinary error
`Unable to find an instance for the variable n.` (unification succeeds with
`P := K`, since `fmap n K` is convertible to `K` by eta), and `eapply lemma`
would leave `n` as an existential. Something similar (success, or an ordinary
unification error) is expected here.

## Variations

- `eapply lemma`: same anomaly.
- `refine (lemma _ _)`: works. `exact (lemma _ _)`: ordinary error (cannot infer `n`).
- `simple apply lemma`: ordinary unification error.
- `family` non-primitive (`Unset Primitive Projections`): ordinary unification error.
- `family`/`fmap` monomorphic: ordinary error `Unable to find an instance for the variable n` (see above).
- `form` with 0 universe levels (e.g. lowered to `Set`, as happens for `Inductive form := fo | fe.`): no anomaly.
- `form` with 2 universe levels (`form@{u v} : Type@{max(u,v)}`): no anomaly (the instance is still the wrong one, but has the same length as `index`'s).
- `fmap` without the extra argument `n`: no anomaly (the unification problem is meta-free and is solved by conversion).

## Backtrace (9.1.1, `Set Debug "backtrace"`)

```
Raised by primitive operation at UVars.subst_instance_level in file "kernel/uVars.ml", line 221, characters 14-45
Called from UVars.subst_instance_universe.f in file "kernel/uVars.ml", line 245, characters 13-37
Called from CList.Smart.map in file "clib/cList.ml", line 971, characters 13-16
Called from UVars.subst_instance_universe in file "kernel/uVars.ml", line 250, characters 11-29
Called from Sorts.subst_fn in file "kernel/sorts.ml", line 410, characters 13-17
Called from Vars.subst_instance_constr.aux in file "kernel/vars.ml", line 448, characters 17-50
Called from Constr.map in file "kernel/constr.ml", line 655, characters 15-18
Called from Constr.map in file "kernel/constr.ml", line 655, characters 15-18
Called from Retyping.type_of_constant in file "pretyping/retyping.ml", line 139, characters 11-83
Called from Unification.unify_0_with_initial_metas.expand in file "pretyping/unification.ml", line 1453, characters 25-62
Called from Unification.unify_0_with_initial_metas.unify_app in file "pretyping/unification.ml", line 1370, characters 12-81
Called from CArray.fold_left2.fold in file "clib/cArray.ml", line 185, characters 33-62
Called from Unification.unify_0_with_initial_metas.unirec_rec in file "pretyping/unification.ml", line 1220, characters 13-85
Called from Unification.unify_0_with_initial_metas.unify_app in file "pretyping/unification.ml", line 1370, characters 12-81
Called from CArray.fold_left2.fold in file "clib/cArray.ml", line 185, characters 33-62
Called from Unification.unify_0_with_initial_metas.unify_app in file "pretyping/unification.ml", lines 1369-1370, characters 10-87
Called from Unification.unify_0_with_initial_metas in file "pretyping/unification.ml", line 1608, characters 14-64
Called from Unification.w_unify_core_0 in file "pretyping/unification.ml", lines 1989-1990, characters 5-33
Called from Clenv.clenv_unify in file "proofs/clenv.ml", line 414, characters 21-74
Called from Clenv.res_pf.(fun) in file "proofs/clenv.ml", line 888, characters 16-56
...
```

On master the backtrace is the same (`Retyping.type_of_constant` <-
`Unification.unify_0_with_initial_metas.expand` at unification.ml:1475 <-
`unify_app` ...).

## Unification trace (`Set Debug "tactic-unification"`, master)

```
T (fmap ?M176 ?M177) ~= T (slot x)
fmap ?M176 ?M177 ~= slot x
fmap ?M176 ~= slot                      (first-order: heads)
fmap ?M176 ~= fun _ : form => K         (delta on slot)
fmap ?M176 jf ~= K                      (eta; jf : form, so the lhs is ill-typed)
{| index := index _ jf |} ~= K          (delta on fmap)
index _ jf ~= index nat K               (record eta)
index ~= index nat                      (projections expanded; lhs gets form's instance)
-> anomaly
```

## Analysis (reporter's hypothesis, not verified by instrumenting Rocq)

1. First-order unification of `fmap ?n ?P ~= slot x` splits it into
   `fmap ?n ~= slot` and `?P ~= x`. Unfolding `slot` and eta-expanding gives
   `fmap ?n jf ~= K` with `jf : form`, which is ill-typed (`fmap ?n` expects a
   `family nat`). Unfolding `fmap` and record eta gives the ill-typed
   primitive projection `index jf`.

2. In `unify_app`, `expand_proj` calls `expand_projection_with_metas`
   (pretyping/unification.ml, 9.1.1 line 1055; unchanged on master, line 1077):

   ```ocaml
   let expand_projection_with_metas ~metas env sigma pr c args =
     let ty = get_type_of_with_metas ~metas ~lax:true env sigma c in
     let (i,u), ind_args =
       try Inductiveops.find_mrectype env sigma ty
       with Not_found -> error_disallowed_sprop env sigma (* dummy, caught immediately *)
     in
       mkApp (mkConstU (Projection.constant pr,u),
              Array.of_list (ind_args @ (c :: args)))
   ```

   It takes the universe instance `u` (and parameters) from whatever inductive
   `find_mrectype` finds in the (lax) type of `c`, without checking that this
   inductive `i` is the record of the projection `pr`. Here `c = jf : form`, so
   it builds `index@{u_form}` with the 1-element instance of `form`, while
   `index` expects a 2-element instance.

3. The resulting head problem `index@{u_form} ~= index@{u u0} nat` fails
   structurally and falls through to `expand`, which (with `with_types`) calls
   `Retyping.get_type_of` on it; `Retyping.type_of_constant` does
   `subst_instance_constr` with the too-short instance, and
   `UVars.subst_instance_level` raises `Invalid_argument "index out of bounds"`.

   The comment at the call site of `expand_proj` already says "Unification can
   be called on ill-typed terms, due to FO and eta in particular, fail
   gracefully in that case", but only `RetypeError` is caught there; the
   "wrong inductive" case is not detected. A possible fix: in
   `expand_projection_with_metas`, check that `i` is `Projection.inductive pr`
   and otherwise raise (e.g. a `RetypeError`) so `expand_proj` falls back to
   the unexpanded projection. (If the instance has the same length, the
   current code silently builds an ill-instantiated term instead of
   crashing.)

## Workaround

Use `refine`-based tactics (`refine (lemma _ _)`, HoTT's `rapply`), or
`exact` with explicit arguments, instead of `apply`/`eapply`.

## Possibly related issues

None found that is clearly the same bug. Searched for `subst_instance_level`,
`expand_projection`, `unify_same_proj`, `"index out of bounds"` (with
apply / universe / anomaly). Closest:

- #19325 (closed): "index out of bounds" anomaly from a double universe-instance substitution (sort polymorphism, `Arguments`); different mechanism.
- #21689, #21970 (closed): "index out of bounds" from double universe substitution in let-ins; different mechanism.
- #21890 (closed): anomaly (`Not_found`) in the legacy unifier with primitive projections and polymorphism; different exception.
- #5720 (closed): universe polymorphism + primitive projections causing "unable to unify" in older versions.
