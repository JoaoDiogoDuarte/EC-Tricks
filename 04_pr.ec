(* Pr[...] rewriting, and moving between Pr, hoare and phoare.
 * Run: easycrypt compile 04_pr.ec *)
require import AllCore Distr DBool.

module T = {
  var x : int
  proc flip() : bool = { var b; b <$ {0,1}; return b; }
  proc keep() : unit = { }
}.

(* ------------------------------------------------------------------------ *)
(* 1. The rewrite rules: Pr[lemma] applies a distribution lemma to a Pr term. *)
lemma le1 &m : Pr[T.flip() @ &m : res] <= 1%r.
proof. by rewrite Pr[mu_le1]. qed.

lemma sub &m : Pr[T.flip() @ &m : res /\ T.x = 0] <= Pr[T.flip() @ &m : res].
proof. by rewrite Pr[mu_sub]. qed.            (* event inclusion *)

lemma not &m :
  Pr[T.flip() @ &m : !res] = Pr[T.flip() @ &m : true] - Pr[T.flip() @ &m : res].
proof. by rewrite Pr[mu_not]. qed.

lemma or &m :
  Pr[T.flip() @ &m : res \/ T.x = 0] =
  Pr[T.flip() @ &m : res] + Pr[T.flip() @ &m : T.x = 0]
  - Pr[T.flip() @ &m : res /\ T.x = 0].
proof. by rewrite Pr[mu_or]. qed.

lemma split_ex &m :
  Pr[T.flip() @ &m : res] =
  Pr[T.flip() @ &m : res /\ T.x = 0] + Pr[T.flip() @ &m : res /\ !(T.x = 0)].
proof. by rewrite Pr[mu_split (T.x = 0)]. qed.

(* NOTE: `split` is a keyword: `lemma split` and `have split : ...` are both
 * parse errors.  Same for other tactic names.  Use hsplit, split_ex, ... *)

(* ------------------------------------------------------------------------ *)
(* 2. Pr[E] = 0 from a hoare triple on "not E". *)
lemma never &m : Pr[T.keep() @ &m : T.x <> T.x{m}] = 0%r.
proof. byphoare (_: T.x = T.x{m} ==> _) => //; hoare; proc; auto. qed.

(* ------------------------------------------------------------------------ *)
(* 3. phoare = 1 from a Pr = 1 fact that holds at every memory: bypr. *)
lemma keep_pr &m : Pr[T.keep() @ &m : T.x = T.x{m}] = 1%r.
proof. byphoare (_: T.x = T.x{m} ==> T.x = T.x{m}) => //; proc; auto. qed.

lemma keep_ph (n : int) : phoare [T.keep : T.x = n ==> T.x = n] = 1%r.
proof. by bypr => &m <-; exact (keep_pr &m). qed.

(* ------------------------------------------------------------------------ *)
(* 4. hoare from a Pr = 1 fact: bypr turns the goal into Pr[not Q] = 0.
 *    Pr[not Q] = Pr[true] - Pr[Q] = Pr[true] - 1, and 1 = Pr[Q] <= Pr[true] <= 1.
 *    No losslessness needed.
 *
 *    PITFALL: inside a Pr[...] event written in a proof, T.x{m} for the
 *    memory bound by bypr is read as the CURRENT value (the event becomes
 *    T.x = T.x).  Don't write the event by hand; get it from the hypothesis,
 *    as in  rewrite -h1 Pr[mu_sub]. *)
lemma keep_h (n : int) : hoare [T.keep : T.x = n ==> T.x = n].
proof.
  bypr => &m <-.
  have h1 := keep_pr &m.
  have h2 : Pr[T.keep() @ &m : true] <= 1%r by rewrite Pr[mu_le1].
  have h3 : 1%r <= Pr[T.keep() @ &m : true] by rewrite -h1 Pr[mu_sub].
  by rewrite Pr[mu_not] h1; smt().
qed.

(* ------------------------------------------------------------------------ *)
(* 5. byequiv: a lemma must match the goal's pre/post EXACTLY.  State the
 *    spec you want in byequiv, then conseq the lemma into it.  If the games
 *    are on the other sides, symmetry flips the goal ({1} and {2} swap). *)
module U = {
  proc f() : bool = { var b; b <$ {0,1}; return b; }
  proc g() : bool = { var b; b <$ {0,1}; return !b; }
}.

equiv fg : U.f ~ U.g : true ==> res{1} = !res{2}.
proof. by proc; auto. qed.                      (* couples b{1} = b{2} *)

lemma fg_pr &m : Pr[U.f() @ &m : res] <= Pr[U.g() @ &m : !res].
proof.
  byequiv (: true ==> res{1} = !res{2}) => //.   (* => // closed pre/post *)
  by conseq fg.
qed.

lemma gf_pr &m : Pr[U.g() @ &m : !res] <= Pr[U.f() @ &m : res].
proof.
  byequiv (: true ==> res{2} = !res{1}) => //.
  by symmetry; conseq fg => /#.
qed.

(* ------------------------------------------------------------------------ *)
(* 6. Pr arithmetic with smt: hypotheses about Pr terms are fine, smt treats
 *    the Pr terms as opaque reals.  Keep the terms syntactically identical. *)
lemma eq_from_two &m : Pr[U.f() @ &m : res] = Pr[U.g() @ &m : !res].
proof. by have := fg_pr &m; have := gf_pr &m; smt(). qed.
