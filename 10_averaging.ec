(* From a random parameter to a fixed one: a game's probability as a phoare,
 * averaging, and "some value is no worse than the average".
 * Run: easycrypt compile 10_averaging.ec
 * (Condensed from simon/src/util/Averaging.ec.) *)
require import AllCore Distr List StdOrder.
import RealOrder.

type input.
op d : input distr.

module type Game = { proc main(x : input) : bool }.

module Avg (G : Game) = {
  proc main() : bool = {
    var x, b;
    x <$ d;
    b <@ G.main(x);
    return b;
  }
}.

(* ------------------------------------------------------------------------ *)
(* 1. A Pr[...] as a phoare bound, to be used as a step of a larger program.
 *    Fix the module's state to the one of &m:  (glob G) = (glob G){m}.
 *    bypr turns the phoare into a statement about Pr from every memory &m0
 *    satisfying the pre; byequiv + proc true (= call with the trivial
 *    invariant for an abstract procedure) relates it to &m. *)
lemma game_ph (G <: Game) (x0 : input) &m :
  phoare [G.main : arg = x0 /\ (glob G) = (glob G){m} ==> res]
    = (Pr[G.main(x0) @ &m : res]).
proof.
  (* bypr on a phoare "= p" also asks for 0 <= p *)
  bypr => &m0; split => [|[-> hG]]; first smt(mu_bounded).
  by byequiv (: ={arg, glob G} ==> ={res}) => //; proc true; auto.
qed.

(* ------------------------------------------------------------------------ *)
(* 2. Averaging from below.
 *    - byphoare (: (glob G) = (glob G){m} ==> res)  keeps the link to &m.
 *    - seq 1 with the 5-argument form (08_sampling.ec, 4.).
 *    - exlim x => xx  then  case @[ambient]: (xx \in d)  : the case
 *      analysis is done in the AMBIENT logic (not on the program state),
 *      so each branch has the plain fact  xx \in d  as a hypothesis.
 *    - conseq (: _ ==> _ : = p) : change the bound of a phoare goal to
 *      the one of the lemma; the side goal compares the two bounds. *)
lemma avg_ge (G <: Game) (eps : real) &m :
  is_lossless d =>
  (forall x, x \in d => eps <= Pr[G.main(x) @ &m : res]) =>
  eps <= Pr[Avg(G).main() @ &m : res].
proof.
  move=> hll h; case: (eps <= 0%r) => heps; first smt(mu_bounded).
  byphoare (: (glob G) = (glob G){m} ==> res) => //; proc.
  seq 1 : (x \in d /\ (glob G) = (glob G){m}) 1%r eps 0%r 0%r => //.
  + by rnd; skip => />; rewrite -weightE_support hll.
  exlim x => xx; case @[ambient]: (xx \in d) => hxx; last by exfalso; smt().
  call (: arg = xx /\ (glob G) = (glob G){m} ==> res); last by skip => />.
  conseq (: _ ==> _ : = (Pr[G.main(xx) @ &m : res])).
  + by smt().
  exact (game_ph G xx &m).
qed.

(* ------------------------------------------------------------------------ *)
(* 3. A value no better than the average, on a finite support s.
 *    The minimiser over a list (argmin_list) plus averaging from below. *)
lemma argmin_list ['a] (f : 'a -> real) (s : 'a list) :
  s <> [] => exists x, x \in s /\ forall y, y \in s => f x <= f y.
proof.
  elim: s => // x s ih _; case: (s = []) => [->|hs]; first by exists x.
  smt().
qed.

lemma exists_le_avg (G <: Game) (s : input list) &m :
  is_lossless d => s <> [] => (forall x, x \in d <=> x \in s) =>
  exists x, x \in d /\ Pr[G.main(x) @ &m : res] <= Pr[Avg(G).main() @ &m : res].
proof.
  move=> hll hs hd.
  have /= [x0 [hin hmin]] := argmin_list (fun x => Pr[G.main(x) @ &m : res]) s hs.
  exists x0; split; first by rewrite hd.
  by apply (avg_ge G (Pr[G.main(x0) @ &m : res]) &m hll) => x hx; apply hmin; rewrite -hd.
qed.
