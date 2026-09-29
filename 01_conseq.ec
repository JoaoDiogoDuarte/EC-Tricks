(* conseq: the shapes worth knowing.
 * Run: easycrypt compile 01_conseq.ec *)
require import AllCore.

module M = {
  var x, y : int

  proc incr() : unit = { x <- x + 1; }
  proc both() : unit = { x <- x + 1; y <- y + 1; }
  proc f(a : int) : int = { x <- x + 1; return a; }
}.

(* ------------------------------------------------------------------------ *)
(* 1. Apply a spec lemma, weakening its post / strengthening its pre.
 *    The side goals are  pre => pre'  and  post' => post. *)
lemma incr_spec (n : int) : hoare [M.incr : M.x = n ==> M.x = n + 1].
proof. by proc; auto. qed.

lemma use_spec : hoare [M.incr : 0 <= M.x ==> 0 < M.x].
proof.
  exists* M.x; elim* => n.        (* name the initial value; see 03_exlim_seq *)
  by conseq (incr_spec n) => /#.
qed.

(* ------------------------------------------------------------------------ *)
(* 2. Change the post to what the next tactic proves, keep the pre ( _ ).
 *    Typical before sim, which wants equalities. *)
lemma to_sim : equiv [M.both ~ M.both : ={M.x, M.y} ==> M.x{1} = M.x{2}].
proof.
  conseq (: _ ==> ={M.x, M.y}) => //.
  by sim.
qed.

(* Same, with the implication proved by hand instead of => // . *)
lemma to_sim' : equiv [M.both ~ M.both : ={M.x, M.y} ==> M.x{1} + M.y{1} = M.x{2} + M.y{2}].
proof.
  conseq (: _ ==> ={M.x, M.y}).
  + by move=> &1 &2 /> /#.        (* post implication, if not automatic *)
  by sim.
qed.

(* ------------------------------------------------------------------------ *)
(* 3. conseq E H1 H2 : glue one-sided hoare facts onto a two-sided equiv.
 *    An equiv relates {1} to {2}; it cannot say how a side's state relates to
 *    its OWN initial value.  Fix the initial values, then add a hoare triple
 *    per side.  Side goals: pre => P /\ P1{1} /\ P2{2}, and
 *    Q /\ Q1{1} /\ Q2{2} => post. *)
equiv f_eq : M.f ~ M.f : ={arg} ==> ={res}.
proof. by proc; auto. qed.

lemma f_x (n : int) : hoare [M.f : M.x = n ==> M.x = n + 1].
proof. by proc; auto. qed.

lemma glue (n1 n2 : int) :
  equiv [M.f ~ M.f : ={arg} /\ M.x{1} = n1 /\ M.x{2} = n2
                 ==> ={res} /\ M.x{1} = n1 + 1 /\ M.x{2} = n2 + 1].
proof. by conseq f_eq (f_x n1) (f_x n2). qed.

(* (_: true ==> true) = "nothing extra on this side"; it becomes a trivial goal. *)
lemma glue_right (n2 : int) :
  equiv [M.f ~ M.f : ={arg} /\ M.x{2} = n2 ==> ={res} /\ M.x{2} = n2 + 1].
proof. by conseq f_eq (_: true ==> true) (f_x n2). qed.
(* Here => // closed the trivial hoare goal; otherwise: + by proc; auto. *)

(* Inside a proof, when the initial value is not a lemma argument yet:
 *   exists* M.x{2}; elim* => n2.
 *   conseq f_eq (_: true ==> true) (f_x n2).                              *)

(* ------------------------------------------------------------------------ *)
(* 4. phoare = 1 from losslessness + a hoare triple (what call{i} wants). *)
lemma f_ll : islossless M.f.
proof. by proc; auto. qed.

lemma f_ph (n : int) : phoare [M.f : M.x = n ==> M.x = n + 1] = 1%r.
proof. by conseq f_ll (f_x n). qed.

(* ------------------------------------------------------------------------ *)
(* 5. Combine two hoare triples (conjoin their posts). *)
lemma f_arg (a0 : int) : hoare [M.f : arg = a0 ==> res = a0].
proof. by proc; auto. qed.

lemma f_both (n a0 : int) :
  hoare [M.f : M.x = n /\ arg = a0 ==> M.x = n + 1 /\ res = a0].
proof. by conseq (f_x n) (f_arg a0) => /#. qed.
