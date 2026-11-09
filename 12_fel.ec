(* fel: a bad event charged per oracle call, with a counter.
 * Run: easycrypt compile 12_fel.ec
 *
 * An oracle that, at each of at most q calls, raises bad with probability
 * at most 1/n gives Pr[bad] <= q/n, whatever the adversary does between the
 * calls.  fel is that union bound over the calls.  It needs
 * require import FelTactic.
 *
 *   fel k cnt delta q bad [o1 : (guard1); o2 : (guard2); ...] inv
 *
 *   k       the number of statements of the game BEFORE the adversary runs
 *           (they must set cnt to 0 and bad to false, and establish inv)
 *   cnt     the counter, delta its charge: the call made when cnt = c may
 *           raise bad with probability at most delta c
 *   q       the bound on the counter in the event
 *   bad     the failure event
 *   [o : guard]  when an oracle is charged.  Name the oracle as the
 *           adversary calls it (O.f, not the procedure O.f is an alias of):
 *           an entry that names no oracle is silently ignored, and that
 *           oracle gets the guard true.
 *   inv     an invariant of every oracle call (optional; true if absent)
 *
 * The goal must be Pr[G : E] <= bound.  The goals fel leaves, in order
 * (some are closed by => //):
 *   1. bigi predT delta 0 q <= bound                 the sum of the charges
 *   2. forall &hr, E => inv => bad /\ cnt <= q       the event
 *   3. the first k statements end in !bad /\ cnt = 0 /\ inv
 *   and, for each oracle, in the alphabetical order of the module names
 *   (not the order of the list):
 *   4. phoare[o : 0 <= cnt < q /\ !bad /\ inv /\ guard ==> bad] <= delta cnt
 *   5. forall c, hoare[o : guard /\ c = cnt /\ inv ==> c < cnt /\ inv]
 *   6. forall b c, hoare[o : !guard /\ bad = b /\ cnt = c /\ inv
 *                            ==> bad = b /\ c <= cnt /\ inv]
 * Goal 4 is the charge, goal 5 says a charged call pays one step of the
 * counter, goal 6 that an uncharged call raises nothing.
 *)
require import AllCore List Distr DInterval StdBigop FelTactic.
(*---*) import StdOrder.RealOrder.

op n : { int | 0 < n } as gt0_n.
op q : { int | 0 <= q } as ge0_q.

module type Orc = { proc f() : int }.
module type Adv (O : Orc) = { proc run() : bool }.

module O : Orc = {
  var cnt : int
  var bad : bool

  proc f() : int = {
    var x;
    x <- 0;
    if (cnt < q) {
      cnt <- cnt + 1;
      x <$ [0..n-1];
      bad <- bad \/ x = 0;
    }
    return x;
  }
}.

module G (A : Adv) = {
  proc main() : bool = {
    var b;
    O.cnt <- 0;
    O.bad <- false;
    b <@ A(O).run();
    return b;
  }
}.

lemma mu_hit : mu [0..n-1] (pred1 0) = inv n%r.
proof. by rewrite dinter1E; smt(gt0_n). qed.

section.

declare module A <: Adv {-O}.

lemma pr_bad &m : Pr[G(A).main() @ &m : O.bad] <= q%r / n%r.
proof.
  (* the event must say that the counter stays within q: carry it in inv *)
  fel 2 O.cnt (fun _ => inv n%r) q O.bad [O.f : (O.cnt < q)] (O.cnt <= q) => //.
  + (* 1. q charges of 1/n *)
    by rewrite (Bigreal.BRA.sumri_const (inv n%r) 0 q ge0_q) /= RField.intmulr.
  + (* 3. the first two statements *)
    by auto => />; exact ge0_q.
  + (* 4. one served call raises bad with probability at most 1/n *)
    proc; rcondt 2; first by auto.
    (* newer EasyCrypt also asks 0 <= 1/n here: ?mu_hit skips that goal *)
    wp; rnd (pred1 0); auto => />; rewrite ?mu_hit /= => *; smt(gt0_n invr_ge0).
  + (* 5. a served call increments the counter *)
    by move=> c; proc; rcondt 2; [auto | auto => /#].
  (* 6. a refused call changes nothing *)
  by move=> b c; proc; rcondf 2; auto.
qed.

end section.
