(* Samplings: rnd with a bijection, one-sided rnd, moving a draw, product
 * samplings, and the five-argument phoare seq.
 * Run: easycrypt compile 08_sampling.ec *)
require import AllCore Distr DBool DInterval.
require DProd.

(* ------------------------------------------------------------------------ *)
(* 1. rnd f g : couple two draws through a bijection.
 *    rnd f g  relates  x{1} <$ d1  with  x{2} <$ d2  by  x{2} = f x{1},
 *    with g the inverse.  Side goals (all in the skip goal):
 *      forall x2 \in d2, f (g x2) = x2
 *      forall x2 \in d2, mu1 d2 x2 = mu1 d1 (g x2)
 *      forall x1 \in d1, f x1 \in d2 /\ g (f x1) = x1
 *    rnd f alone when f is an involution (f = g).
 *    (SwapGames.ec: rnd (fun y => minv m y) (fun xs => oget m.[xs]);
 *     HRBirthday.ec: rnd (exchange_row a) (exchange_row a).) *)
module Flip = {
  proc pos() : bool = { var b; b <$ {0,1}; return b; }
  proc neg() : bool = { var b; b <$ {0,1}; return !b; }
}.

lemma pos_neg : equiv [Flip.pos ~ Flip.neg : true ==> ={res}].
proof.
  proc; rnd (fun b => !b).
  by skip => />; smt(dbool1E).
qed.

(* An offset on an interval: x{2} = n - 1 - x{1}, an involution of [0..n-1]. *)
module Iv = {
  proc up(n : int) : int = { var x; x <$ [0 .. n - 1]; return x; }
  proc down(n : int) : int = { var x; x <$ [0 .. n - 1]; return n - 1 - x; }
}.

lemma up_down : equiv [Iv.up ~ Iv.down : ={n} ==> ={res}].
proof.
  proc; rnd (fun x => n{1} - 1 - x).
  (* the three side goals, in order: f (g x) = x, equal masses, and
   * f x in the support with g (f x) = x *)
  skip => /> &2; split => [x _ | _]; first by ring.
  split => [x hx | _ x hx]; first by rewrite !dinter1E; smt(supp_dinter).
  smt(supp_dinter).
qed.

(* ------------------------------------------------------------------------ *)
(* 2. rnd{2} : a draw on one side only, never used.  Needs the distribution
 *    to be lossless (side goal  weight d = 1  or  is_lossless d).
 *    Typical for a lazy cache: a repeated query reads the cache on one side
 *    and draws a fresh, discarded sample on the other (SimonFixed.ec). *)
module Waste = {
  proc a() : int = { return 0; }
  proc b() : int = { var x; x <$ {0,1}; return 0; }
}.

lemma waste : equiv [Waste.a ~ Waste.b : true ==> ={res}].
proof. by proc; rnd{2}; skip => />; exact dbool_ll. qed.

(* ------------------------------------------------------------------------ *)
(* 3. Move a draw past a call that does not read it: swap, then the call
 *    with (: true) for an abstract module.  This is how "x is independent of
 *    the adversary's view" becomes provable: draw x AFTER the run, then any
 *    event "x in S(view)" has probability <= mu d (S view)  (LateSample.ec). *)
module type Run = { proc run() : int }.

module Early (R : Run) = {
  proc main() : bool * int = {
    var x, v;
    x <$ {0,1};
    v <@ R.run();
    return (x, v);
  }
}.

module Late (R : Run) = {
  proc main() : bool * int = {
    var x, v;
    v <@ R.run();
    x <$ {0,1};
    return (x, v);
  }
}.

lemma early_late (R <: Run) :
  equiv [Early(R).main ~ Late(R).main : ={glob R} ==> ={res, glob R}].
proof. by proc; swap{1} 1 1; rnd; call (: true); auto. qed.

(* ------------------------------------------------------------------------ *)
(* 4. The five-argument seq for phoare: split a probability as a product.
 *
 *      seq n : (R) p1 p2 p3 p4 (I).
 *
 *    For pre ==> post with bound b, cutting after n instructions:
 *      goal 1:  hoare  [first n : pre ==> I]      (I = true when omitted)
 *      goal 2:  phoare [first n : pre ==> R]      = p1   (or <= / >=)
 *      goal 3:  phoare [rest : R /\ I ==> post]   = p2
 *      goal 4:  phoare [first n : pre ==> !R]     = p3   (dropped if p4 = 0)
 *      goal 5:  phoare [rest : !R /\ I ==> post]  = p4
 *      goal 6:  p1 * p2 + p3 * p4  vs  b
 *    Use 1%r / 0%r for the parts you don't care about; the goals with a
 *    0%r probability are hoare goals in disguise (close with  hoare; ...).
 *    `_` for a probability leaves it as a metavariable (HRRefusal.ec). *)
module Two = {
  proc main() : bool = {
    var b1, b2;
    b1 <$ {0,1};
    b2 <$ {0,1};
    return b1 /\ b2;
  }
}.

lemma two_quarter : phoare [Two.main : true ==> res] = (1%r / 4%r).
proof.
  proc.
  seq 1 : b1 (1%r / 2%r) (1%r / 2%r) (1%r / 2%r) 0%r.
  (* p4 = 0 : EasyCrypt drops the goal for p3 (it is multiplied by 0) *)
  + by auto.                                         (* hoare: to I = true *)
  + by rnd; skip => />; rewrite dboolE.             (* Pr[b1] = 1/2 *)
  + by rnd; skip => />; rewrite dboolE.             (* b1 ==> Pr[b1 /\ b2] = 1/2 *)
  + by hoare; rnd; skip => /> &hr ->.                (* !b1 ==> Pr = 0 *)
  by move=> _ _; field.                              (* 1/2 * 1/2 + ... *)
qed.

(* ------------------------------------------------------------------------ *)
(* 5. rnd P in a phoare: the probability of the predicate P on the drawn
 *    value.  The skip goal is  mu d P  (relation to the bound)  plus
 *    forall x, (x \in d) => P x <=> post[x].  Writing P explicitly helps
 *    when the post mentions other variables. *)
lemma coin_true : phoare [Flip.pos : true ==> res] = (1%r / 2%r).
proof. by proc; rnd (fun b => b); skip => />; rewrite dboolE. qed.

(* ------------------------------------------------------------------------ *)
(* 6. DProd.ProdSampling: one draw from a product  =  two draws.
 *    The library equiv  S.sample ~ S.sample2 ; with  symmetry  for the other
 *    direction, and  conseq  to adapt the pre.  (HRBirthday.ec)
 *    The equiv itself is proved with   rnd : 0 0   (see TACTICS.md). *)
clone DProd.ProdSampling as PS with
  type t1 <- bool,
  type t2 <- bool.

module Pair = {
  proc one() : bool * bool = {
    var p;
    p <@ PS.S.sample({0,1}, {0,1});
    return p;
  }
  proc two() : bool * bool = {
    var p;
    p <@ PS.S.sample2({0,1}, {0,1});
    return p;
  }
}.

lemma one_two : equiv [Pair.one ~ Pair.two : true ==> ={res}].
proof. by proc; call PS.sample_sample2; auto. qed.

lemma two_one : equiv [Pair.two ~ Pair.one : true ==> ={res}].
proof.
  proc; call (: ={d1, d2} ==> ={res}).
  + by symmetry; conseq PS.sample_sample2 => /#.
  by auto.
qed.

(* ------------------------------------------------------------------------ *)
(* 7. rndsem{i} n : merge the block of draws (and assignments) that starts
 *    after position n into ONE draw from the composed law (dlet / dmap).
 *      rndsem{1} 0   a <$ d1; b <$ d2; c <- (a, b)
 *                    becomes  (a, b, c) <$ dlet d1 (fun a => dmap d2 ...)
 *      rndsem*{1} 0  the same, keeping only what is used later:
 *                    c <$ dlet d1 (fun a => dmap d2 (fun b => (a, b)))
 *    Then one rnd relates it to a single draw on the other side; when the
 *    two laws are equal but not syntactically, give the identity
 *    bijection and prove the masses equal (here with dprod_dlet).
 *    (HRPublic.ec, HRFixed.ec, SimonFixed.ec: rndsem*{1} 0; rnd.) *)
module Sq = {
  proc seq2() : bool * bool = {
    var a, b, c;
    a <$ {0,1};
    b <$ {0,1};
    c <- (a, b);
    return c;
  }
  proc joint() : bool * bool = {
    var p;
    p <$ {0,1} `*` {0,1};
    return p;
  }
}.

lemma seq2_joint : equiv [Sq.seq2 ~ Sq.joint : true ==> ={res}].
proof.
  proc; rndsem*{1} 0.
  rnd (fun p => p) (fun p => p); skip => />.
  by move=> p _; rewrite dprod_dlet.
qed.
