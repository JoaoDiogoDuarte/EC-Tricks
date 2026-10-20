(* A sample the run does not use: draw it after the run, then bound the
 * chance that the run's output guesses it or hits it.
 * Run: easycrypt compile 08_late_sample.ec
 *
 * A game draws x and then runs an adversary that never sees x.  Inside the
 * run nothing can say "x is independent of what the adversary does": x is
 * already in memory at every call.  Move the sampling AFTER the call
 * (swap, then rnd and call (: true)); then x is drawn when the run's output
 * is fixed, and any event "x lies in a set the output determines" has
 * probability at most the mass of that set.
 *
 *   x <$ d; v <@ A.run();    ~    v <@ A.run(); x <$ d;
 *
 * The phoare seq after the swap.  seq n : R p1 p2 p3 p4 cuts after n
 * statements and bounds the probability by p1 * p2 + p3 * p4, where
 *   p1 bounds  Pr[first part ends in R]       p2 bounds  Pr[rest hits | R]
 *   p3 bounds  Pr[first part ends in !R]      p4 bounds  Pr[rest hits | !R]
 * Here: seq 1 : (I v) 1%r p 0%r 1%r.  After the call I v holds (p3 = 0 is a
 * hoare triple on the call), and given I v the last sampling hits with
 * probability at most p.  No termination is needed: these are upper bounds.
 *)
require import AllCore List Distr DInterval.
(*---*) import StdOrder.RealOrder.

op n : { int | 0 < n } as gt0_n.

lemma mu1_d (x : int) : mu1 [0..n-1] x <= inv n%r.
proof. by rewrite dinter1E; smt(gt0_n invr_ge0). qed.

(* The adversary returns a list of at most k guesses. *)
op k : { int | 0 <= k } as ge0_k.

module type Adv = { proc run() : int list }.

(* The hidden point is a global of the game, so the event can mention it,
 * and A, declared {-Early}, cannot read it. *)
module Early (A : Adv) = {
  var x : int
  proc main() : int list = {
    var l;
    x <$ [0..n-1];
    l <@ A.run();
    return l;
  }
}.

module Late (A : Adv) = {
  var x : int
  proc main() : int list = {
    var l;
    l <@ A.run();
    x <$ [0..n-1];
    return l;
  }
}.

section.

declare module A <: Adv {-Early, -Late}.

declare axiom A_size : hoare[A.run : true ==> size res <= k].

(* ------------------------------------------------------------------------ *)
(* 1. The two games are one experiment: swap the sampling behind the call. *)
equiv early_late : Early(A).main ~ Late(A).main :
  ={glob A} ==> ={res, glob A} /\ Early.x{1} = Late.x{2}.
proof. by proc; swap{1} 1 1; rnd; call (: true); auto. qed.

(* ------------------------------------------------------------------------ *)
(* 2. The bound, sample last.  After the call the list has at most k
 *    elements (A_size); then x falls in it with probability at most
 *    size l * (1/n) (mu_mem_le_mu1). *)
lemma late_hit &m : Pr[Late(A).main() @ &m : Late.x \in res] <= k%r / n%r.
proof.
  (* newer EasyCrypt makes rnd ask 0 <= bound: have it, => // uses it *)
  have hb : 0%r <= k%r / n%r by smt(ge0_k gt0_n divr_ge0).
  byphoare => //; proc.
  seq 1 : (size l <= k) 1%r (k%r / n%r) 0%r 1%r => //.
  + rnd (mem l) => //; skip => /> &hr hl.
    apply (ler_trans ((size l{hr})%r * inv n%r)); first exact (mu_mem_le_mu1 _ _ _ mu1_d).
    by apply ler_wpmul2r; [smt(invr_ge0 gt0_n) | rewrite le_fromint].
  by hoare; call A_size.
qed.

(* 3. ...hence with the sample first: rewrite with the equivalence. *)
lemma early_hit &m : Pr[Early(A).main() @ &m : Early.x \in res] <= k%r / n%r.
proof.
  have -> : Pr[Early(A).main() @ &m : Early.x \in res] = Pr[Late(A).main() @ &m : Late.x \in res].
  + by byequiv early_late => // /#.
  exact (late_hit &m).
qed.

(* ------------------------------------------------------------------------ *)
(* 4. A guess: the first element of the list equals x.  No hypothesis on the
 *    adversary at all, so the seq invariant is just true. *)
lemma early_guess &m : Pr[Early(A).main() @ &m : Early.x = head 0 res] <= inv n%r.
proof.
  have -> : Pr[Early(A).main() @ &m : Early.x = head 0 res]
          = Pr[Late(A).main() @ &m : Late.x = head 0 res].
  + by byequiv early_late => // /#.
  have hb : 0%r <= inv n%r by smt(gt0_n invr_ge0).
  byphoare => //; proc.
  (* with the invariant true, => // also closes the branch where it fails *)
  seq 1 : true 1%r (inv n%r) 0%r 1%r => //.
  by rnd (pred1 (head 0 l)) => //; skip => /> &hr; exact (mu1_d (head 0 l{hr})).
qed.

end section.

(* What this cannot do: bound an event that the run itself makes depend on
 * x (e.g. an oracle that answers differently at x).  First show the game
 * equivalent to one where the run does not read x at all (an equiv whose
 * oracles ignore x), then move the sample. *)
