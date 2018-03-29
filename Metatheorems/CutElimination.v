
(* TODO: theorem stating cut-elimination.  Probably should hold over any flat type theoy. *)

(* Sketch proof: roughly paralleling our definition of substitution.

  First show: given a cut-free derivation of a judgement J and a renaming of variables of the context of J, can rename throughout derivation to get a cut-free derivartion of the renamed judgement.

  Then show: given a cut-free derivation of a judgement J, and a context map into the context of J with cut-free typing derivations of the terms in the context map, can substitute throughout derivation to get a cut-free derivartion of the substituted judgement.

  Then do the main induction to cut-eliminate in all proofs. *)
