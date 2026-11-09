(* Exact laws, and equivalences that rnd cannot prove.
 * Run: easycrypt compile 10_laws.ec
 *
 * - The law of "draw coins, then run a deterministic procedure" is an exact
 *   phoare, from a hoare spec of the procedure and its losslessness.
 * - Two programs whose results have the same law are equivalent, even when
 *   no bijection relates their samplings: bypr (res{1}) (res{2}), then one
 *   Pr per side.
 * - transitivity chains equivalences, and transitivity{1} { s } replaces a
 *   statement by another one (e.g. a sampling by a procedure call) so that a
 *   lemma about procedures can be used with call.
 *)
require import AllCore List Distr DInterval.

op n : { int | 0 < n } as gt0_n.

lemma dn_ll : is_lossless [0..n-1].
proof. by apply dinter_ll; smt(gt0_n). qed.

(* ------------------------------------------------------------------------ *)
(* 1. The law of a program that draws coins and runs a procedure.  All that
 *    is known of D is that it terminates and computes F, leaving its state
 *    as it was. *)
op F : int -> int.

module type Det = { proc run(r : int) : int }.

module S (D : Det) = {
  proc f() : int = {
    var r, y;
    r <$ [0..n-1];
    y <@ D.run(r);
    return y;
  }
}.

section.

declare module D <: Det.

declare axiom D_ll : islossless D.run.

declare axiom D_spec (r0 : int) (g0 : glob D) :
  hoare[D.run : r = r0 /\ (glob D) = g0 ==> res = F r0 /\ (glob D) = g0].

(* the spec with termination: the form a call in a phoare takes *)
lemma D_pr (r0 : int) (g0 : glob D) :
  phoare[D.run : r = r0 /\ (glob D) = g0 ==> res = F r0 /\ (glob D) = g0] = 1%r.
proof. by conseq D_ll (D_spec r0 g0). qed.

(* phoare seq with five numbers, for an EXACT bound:
 *   seq 1 : R p1 p2 p3 p4      Pr = p1 * p2 + p3 * p4
 * R is "the coins already decide the event"; p2 = 1 and p4 = 0 because
 * the procedure computes F (the p4 branch is a hoare triple).  The _ for p3
 * is filled in from p1. *)
lemma S_law (P : int -> bool) :
  phoare[S(D).f : true ==> P res] = (mu [0..n-1] (fun r => P (F r))).
proof.
  proc.
  seq 1 : (P (F r)) (mu [0..n-1] (fun r => P (F r))) 1%r _ 0%r => //.
  + by rnd; skip.
  + by exists* r, (glob D); elim* => r0 g0; call (D_pr r0 g0); skip => />.
  by hoare; exists* r, (glob D); elim* => r0 g0; call (D_spec r0 g0); skip => />.
qed.

(* The probability of an event of the program is then a probability over
 * the coins, which is a fact about distributions. *)
lemma S_pr &m : Pr[S(D).f() @ &m : res = 0] = mu [0..n-1] (fun r => F r = 0).
proof. by byphoare (S_law (pred1 0)). qed.

end section.

(* ------------------------------------------------------------------------ *)
(* 2. Same law, no bijection.  The left side draws a PAIR and keeps its first
 *    component; the right side draws one value.  rnd would need a bijection
 *    between pairs and values.  bypr reduces the equivalence to the equality
 *    of the two laws, value by value. *)
module Coins = {
  proc pair() : int = { var p; p <$ [0..n-1] `*` [0..n-1]; return p.`1; }
  proc one() : int = { var x; x <$ [0..n-1]; return x; }
}.

equiv pair_one : Coins.pair ~ Coins.one : true ==> ={res}.
proof.
  (* the goal: forall &1 &2 v, pre => Pr[left : res = v] = Pr[right : res = v];
   * here the pre is true and => // removes it *)
  bypr (res{1}) (res{2}) => // &1 &2 v.
  have -> : Pr[Coins.pair() @ &1 : res = v]
          = mu ([0..n-1] `*` [0..n-1]) (fun (p : int * int) => p.`1 = v).
  + by byphoare => //; proc; rnd; skip.
  have -> : Pr[Coins.one() @ &2 : res = v] = mu [0..n-1] (pred1 v).
  + by byphoare => //; proc; rnd; skip.
  by rewrite (dprodEl _ _ (pred1 v)) dn_ll.
qed.

(* ------------------------------------------------------------------------ *)
(* 3. transitivity{1}: a sampling statement where a lemma about a procedure
 *    is wanted.  Replace the left statement by a call of Coins.pair (first
 *    premise: inline), then call pair_one (second premise).  The two
 *    relations are the pre/post of the two halves; the side goals say they
 *    compose. *)
module G1 = {
  proc main() : int = {
    var p, x;
    p <$ [0..n-1] `*` [0..n-1];
    x <- p.`1;
    return x + 1;
  }
}.

module G2 = {
  proc main() : int = {
    var x;
    x <@ Coins.one();
    return x + 1;
  }
}.

equiv g1_g2 : G1.main ~ G2.main : true ==> ={res}.
proof.
  proc.
  (* cut first: the statements to replace must be ALL of the left program *)
  seq 2 1 : (={x}); last by auto.
  transitivity{1} { x <@ Coins.pair(); } (true ==> ={x}) (true ==> ={x}) => //.
  + by inline *; auto.
  by call pair_one.
qed.

(* transitivity at the level of procedures, through a third program.  Its
 * side goals ask for a middle argument for every related pair, and that the
 * two posts compose; => // closes both here. *)
module Gp = {
  proc main() : int = {
    var x;
    x <@ Coins.pair();
    return x + 1;
  }
}.

equiv g1_g2' : G1.main ~ G2.main : true ==> ={res}.
proof.
  transitivity Gp.main (true ==> ={res}) (true ==> ={res}) => //.
  + by proc; inline *; auto.
  by proc; call pair_one.
qed.
