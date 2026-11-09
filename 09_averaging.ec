(* A probability as a phoare spec, and a random parameter as an average.
 * Run: easycrypt compile 09_averaging.ec
 *
 * Pr[G.main(x0) @ &m : res] depends on &m only through glob G.  Stated as
 *   phoare[G.main : arg = x0 /\ (glob G) = (glob G){m} ==> res]
 *     = (Pr[G.main(x0) @ &m : res])
 * it can be CALLED inside a bigger program: this is how a bound proved for
 * every fixed value becomes a bound for a value drawn at random, and how
 * "on average" becomes "there is a value".
 *
 * proc true proves G ~ G for an abstract G: equal state, equal arguments,
 * equal results.
 *)
require import AllCore List Distr DInterval.
(*---*) import StdOrder.RealOrder.

op n : { int | 0 < n } as gt0_n.

module type Game = { proc main(x : int) : bool }.

(* draw the parameter, then play *)
module Avg (G : Game) = {
  proc main() : bool = {
    var x, b;
    x <$ [0..n-1];
    b <@ G.main(x);
    return b;
  }
}.

(* ------------------------------------------------------------------------ *)
(* 1. A Pr term as a phoare spec: bypr, then byequiv with G ~ G. *)
lemma game_ph (G <: Game) (x0 : int) &m :
  phoare[G.main : arg = x0 /\ (glob G) = (glob G){m} ==> res]
    = (Pr[G.main(x0) @ &m : res]).
proof.
  bypr => &m0.
  (* newer EasyCrypt adds 0 <= Pr[...] /\ in front of the goal *)
  try (split; first by rewrite Pr[mu_ge0]).
  move=> -[-> hG].
  by byequiv (: ={arg, glob G} ==> ={res}) => //; proc true.
qed.

(* ------------------------------------------------------------------------ *)
(* 2. A bound for every value is a bound for a random one.  After the draw
 *    x is in the support; exlim names it, and the call uses game_ph at that
 *    value.  case @[ambient] splits on a formula that mentions no program
 *    variable (here xx \in [0..n-1]). *)
lemma avg_le (G <: Game) (eps : real) &m :
  (forall x, x \in [0..n-1] => Pr[G.main(x) @ &m : res] <= eps) =>
  Pr[Avg(G).main() @ &m : res] <= eps.
proof.
  move=> h.
  (* newer EasyCrypt asks 0 <= eps of phoare bounds: a probability is below it *)
  have heps : 0%r <= eps.
  + have h0 := h 0 _; first by rewrite supp_dinter; smt(gt0_n).
    have h1 : 0%r <= Pr[G.main(0) @ &m : res] by rewrite Pr[mu_ge0].
    smt().
  byphoare (: (glob G) = (glob G){m} ==> res) => //; proc.
  seq 1 : (x \in [0..n-1] /\ (glob G) = (glob G){m}) 1%r eps 0%r 1%r => //.
  + exlim x => xx; case @[ambient]: (xx \in [0..n-1]) => hxx; last by exfalso => /#.
    call (: arg = xx /\ (glob G) = (glob G){m} ==> res); last by skip => />.
    by conseq (: _ ==> _ : = (Pr[G.main(xx) @ &m : res])); [smt() | exact (game_ph G xx &m)].
  by hoare; auto => />; smt(supp_dinter).
qed.

(* The lower bound, the same way.  The draw now has to be lossless.  (A
 * negative eps is trivial; newer EasyCrypt wants 0 <= eps of the bound.) *)
lemma avg_ge (G <: Game) (eps : real) &m :
  0%r <= eps =>
  (forall x, x \in [0..n-1] => eps <= Pr[G.main(x) @ &m : res]) =>
  eps <= Pr[Avg(G).main() @ &m : res].
proof.
  move=> heps h; byphoare (: (glob G) = (glob G){m} ==> res) => //; proc.
  seq 1 : (x \in [0..n-1] /\ (glob G) = (glob G){m}) 1%r eps 0%r 0%r => //.
  + rnd; skip => />; rewrite -(mu_eq_support _ predT) ?weight_dinter //; smt(gt0_n).
  exlim x => xx; case @[ambient]: (xx \in [0..n-1]) => hxx; last by exfalso => /#.
  call (: arg = xx /\ (glob G) = (glob G){m} ==> res); last by skip => />.
  by conseq (: _ ==> _ : = (Pr[G.main(xx) @ &m : res])); [smt() | exact (game_ph G xx &m)].
qed.

(* ------------------------------------------------------------------------ *)
(* 3. From random to fixed: a value no better than the average.  Take the
 *    value that minimises the probability over the (finite) support; every
 *    value is at least as good, so avg_ge gives the average. *)
lemma argmin_list ['a] (f : 'a -> real) (s : 'a list) :
  s <> [] => exists x, x \in s /\ forall y, y \in s => f x <= f y.
proof.
  elim: s => // x s ih _; case: (s = []) => [->|hs]; first by exists x.
  by have [x0 [h0 hmin]] := ih hs; case: (f x <= f x0) => hx; [exists x | exists x0]; smt().
qed.

lemma exists_le_avg (G <: Game) &m :
  exists x, x \in [0..n-1] /\ Pr[G.main(x) @ &m : res] <= Pr[Avg(G).main() @ &m : res].
proof.
  have hs : range 0 n <> [] by rewrite -size_eq0 size_range; smt(gt0_n).
  have /= [x0 [hin hmin]] := argmin_list (fun x => Pr[G.main(x) @ &m : res]) _ hs.
  exists x0; split; first by move: hin; rewrite supp_dinter mem_range /#.
  apply (avg_ge G (Pr[G.main(x0) @ &m : res]) &m); first by rewrite Pr[mu_ge0].
  by move=> x; rewrite supp_dinter => hx; apply hmin; rewrite mem_range /#.
qed.

(* Typical use: a theorem about a game on a random key, world or oracle
 *   Pr[Avg(G).main() @ &m : res] <= eps
 * gives one fixed value that the bound holds for:
 *   exists x, x \in [0..n-1] /\ Pr[G.main(x) @ &m : res] <= eps
 * The value may depend on G and &m: it is chosen after them. *)
lemma fixed_value (G <: Game) (eps : real) &m :
  Pr[Avg(G).main() @ &m : res] <= eps =>
  exists x, x \in [0..n-1] /\ Pr[G.main(x) @ &m : res] <= eps.
proof.
  move=> h; have [x [hx hle]] := exists_le_avg G &m.
  by exists x; split => //; apply (ler_trans _ _ _ hle h).
qed.
