(* Up-to-bad: two games that agree until a flag is raised.
 * Run: easycrypt compile 05_upto_bad.ec
 *
 * The call rule has three parts:
 *
 *   call (: B, I, J).
 *     B : the bad event, read on the RIGHT memory (written without {2})
 *     I : relational invariant while not B
 *     J : what still holds once B happened (relational; optional)
 *
 * It generates, for the adversary and then for EACH oracle procedure o:
 *   - the adversary terminates when its oracles do
 *   - equiv [o ~ o : !B{2} /\ ={arg} /\ I ==> if B{2} then J else ={res} /\ I]
 *   - forall &2, B{2} => phoare [o{1} : J ==> J] = 1      (left, after bad)
 *   - forall &1,         phoare [o{2} : B /\ J ==> B /\ J] = 1  (right keeps bad)
 * and leaves the code before the call with post
 *   if B{2} then J else (={res, glob A} /\ I).
 *
 * Choosing I: include ={flag} itself, or nothing says the LEFT flag is
 * still down while the right one is (you then can't conclude ={Flag.bad}).
 *
 * Choosing J: it must be preserved by each side ALONE, and it must imply
 * that B stays set.  If an oracle could un-set B (e.g. overwrite the record
 * B is computed from) put in J whatever switches that oracle off.
 *)
require import AllCore Distr.

module type Orc = {
  proc f(x : int) : int
}.

module type Adv (O : Orc) = {
  proc run() : bool
}.

module Flag = {
  var bad : bool
  var s   : int
}.

(* Two oracles that differ only on the point s; both raise the flag there.
 * Nonnegative queries only, so with s < 0 the flag can never be raised. *)
module OL : Orc = {
  proc f(x : int) : int = {
    if (0 <= x /\ x = Flag.s) { Flag.bad <- true; }
    return x;
  }
}.

module OR : Orc = {
  proc f(x : int) : int = {
    var r;
    r <- x;
    if (0 <= x /\ x = Flag.s) { Flag.bad <- true; r <- 0; }
    return r;
  }
}.

module Game (O : Orc) (A : Adv) = {
  proc main(s0 : int) : bool = {
    var b;
    Flag.bad <- false;
    Flag.s <- s0;
    b <@ A(O).run();
    return b;
  }
}.

section.

declare module A <: Adv {-Flag}.

declare axiom A_ll (O <: Orc {-A}) : islossless O.f => islossless A(O).run.

(* ------------------------------------------------------------------------ *)
(* 1. The up-to-bad equivalence. *)
equiv upto : Game(OL, A).main ~ Game(OR, A).main :
  ={glob A, arg} ==> ={Flag.bad} /\ (!Flag.bad{2} => ={res}).
proof.
  proc.
  call (: Flag.bad, ={Flag.s, Flag.bad}, Flag.bad{1}).
  + exact A_ll.                              (* adversary terminates *)
  + by proc; auto => /#.                     (* oracle, before bad *)
  + by move=> &2 _; proc; auto.              (* left oracle, after bad *)
  + by move=> &1; proc; auto.                (* right oracle keeps bad *)
  by auto => /#.
qed.

(* If you only need !bad{2} => ={res} (not ={Flag.bad}), drop J:
 *   call (: Flag.bad, ={Flag.s, Flag.bad}).
 * and the "after bad" goals only ask for termination. *)

(* ------------------------------------------------------------------------ *)
(* 2. The usual bound: Pr1[E] <= Pr2[E] + Pr2[bad]. *)
lemma upto_bound &m (s0 : int) :
  Pr[Game(OL, A).main(s0) @ &m : res] <=
  Pr[Game(OR, A).main(s0) @ &m : res] + Pr[Game(OR, A).main(s0) @ &m : Flag.bad].
proof.
  have le : Pr[Game(OL, A).main(s0) @ &m : res] <=
            Pr[Game(OR, A).main(s0) @ &m : res \/ Flag.bad].
  + byequiv (: ={glob A, arg} ==> ={Flag.bad} /\ (!Flag.bad{2} => ={res})) => //.
    + by conseq upto.
    by move=> &1 &2 /#.
  have hor : Pr[Game(OR, A).main(s0) @ &m : res \/ Flag.bad] <=
             Pr[Game(OR, A).main(s0) @ &m : res] +
             Pr[Game(OR, A).main(s0) @ &m : Flag.bad].
  + by rewrite Pr[mu_or]; smt(mu_bounded).      (* drop the - Pr[res /\ bad] *)
  smt().
qed.

(* ------------------------------------------------------------------------ *)
(* 3. When bad provably never happens: Pr[bad] = 0 from a hoare triple on the
 *    right game, then equality from two one-directional byequivs. *)
lemma no_bad &m (s0 : int) :
  s0 < 0 => Pr[Game(OR, A).main(s0) @ &m : Flag.bad] = 0%r.
proof.
  move=> hs; byphoare (_: arg = s0 ==> _) => //; hoare.
  proc.
  call (: !Flag.bad /\ Flag.s < 0); first by proc; auto => /#.
  by auto => /#.
qed.

lemma upto_eq &m (s0 : int) :
  s0 < 0 =>
  Pr[Game(OL, A).main(s0) @ &m : res] = Pr[Game(OR, A).main(s0) @ &m : res].
proof.
  move=> hs; have nb := no_bad &m s0 hs.
  (* Pr1[res] <= Pr2[res \/ bad] *)
  have le1 : Pr[Game(OL, A).main(s0) @ &m : res] <=
             Pr[Game(OR, A).main(s0) @ &m : res \/ Flag.bad].
  + byequiv (: ={glob A, arg} ==> ={Flag.bad} /\ (!Flag.bad{2} => ={res})) => //.
    + by conseq upto.
    by move=> &1 &2 /#.
  (* Pr2[res /\ !bad] <= Pr1[res]: the games are now on the other sides *)
  have le2 : Pr[Game(OR, A).main(s0) @ &m : res /\ !Flag.bad] <=
             Pr[Game(OL, A).main(s0) @ &m : res].
  + byequiv (: ={glob A, arg} ==> ={Flag.bad} /\ (!Flag.bad{1} => ={res})) => //.
    + by symmetry; conseq upto => /#.
    by move=> &1 &2 /#.
  (* arithmetic *)
  have hor : Pr[Game(OR, A).main(s0) @ &m : res \/ Flag.bad] <=
             Pr[Game(OR, A).main(s0) @ &m : res] +
             Pr[Game(OR, A).main(s0) @ &m : Flag.bad].
  + by rewrite Pr[mu_or]; smt(mu_bounded).
  have hsplit : Pr[Game(OR, A).main(s0) @ &m : res] =
                Pr[Game(OR, A).main(s0) @ &m : res /\ Flag.bad] +
                Pr[Game(OR, A).main(s0) @ &m : res /\ !Flag.bad].
  + by rewrite Pr[mu_split Flag.bad].
  have hsub : Pr[Game(OR, A).main(s0) @ &m : res /\ Flag.bad] <=
              Pr[Game(OR, A).main(s0) @ &m : Flag.bad].
  + by rewrite Pr[mu_sub].
  smt(mu_bounded).
qed.

end section.
