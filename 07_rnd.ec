(* rnd: coupling the samplings of the two sides.
 * Run: easycrypt compile 07_rnd.ec
 *
 * rnd works on the LAST statement of each side, so it is used after wp and
 * before the samplings that come earlier, from the end of the program.
 *
 *   rnd            the two samples are equal (same distribution on both sides)
 *   rnd f g        the right sample is f of the left one; g is the inverse of f
 *   rnd{1}, rnd{2} a sampling on one side only (its distribution must be
 *                  lossless: nothing on the other side pays for its mass)
 *
 * The side goals of rnd f g, for left x <$ dL and right y <$ dR:
 *   forall yR, yR \in dR => yR = f (g yR)             f undoes g
 *   forall yR, yR \in dR => mu1 dR yR = mu1 dL (g yR) masses agree
 *   forall xL, xL \in dL => f xL \in dR /\ xL = g (f xL) /\ (post at xL, f xL)
 * For two uniform distributions on sets of the same size the mass goal is
 * the equality of the two constants.
 *)
require import AllCore Bool Distr DBool DInterval IntDiv.

(* ------------------------------------------------------------------------ *)
(* 1. A bijection: the one-time pad.  The key is uniform, so the ciphertext
 *    is uniform whatever the message.  f k = k ^^ m{1} sends the key to the
 *    ciphertext and is its own inverse. *)
module OTP = {
  proc enc(m : bool) : bool = { var k; k <$ {0,1}; return k ^^ m; }
  proc rand(m : bool) : bool = { var c; c <$ {0,1}; return c; }
}.

equiv otp : OTP.enc ~ OTP.rand : true ==> ={res}.
proof.
  proc; rnd (fun k => k ^^ m{1}) (fun c => c ^^ m{1}).
  by skip => /> &1; smt(xorA xorK xor_false dbool1E supp_dbool).
qed.

(* The same with a shift modulo n: f x = (x + k) %% n, g y = (y - k) %% n. *)
op n : { int | 0 < n } as gt0_n.

module Shift = {
  proc f(k : int) : int = { var x; x <$ [0..n-1]; return (x + k) %% n; }
  proc g(k : int) : int = { var y; y <$ [0..n-1]; return y; }
}.

equiv shift : Shift.f ~ Shift.g : true ==> ={res}.
proof.
  proc; rnd (fun x => (x + k{1}) %% n) (fun y => (y - k{1}) %% n).
  skip => /> &1; split => [y /supp_dinter hy | _].
  + by rewrite modzDml /= modz_small /#.
  split => [y /supp_dinter hy | _ x /supp_dinter hx].
  + by rewrite !dinter1E; smt(modz_ge0 ltz_pmod gt0_n).
  rewrite supp_dinter; split; first smt(modz_ge0 ltz_pmod gt0_n).
  by move=> _; rewrite modzDml addrK modz_small /#.
qed.

(* ------------------------------------------------------------------------ *)
(* 2. A sampling on one side only.  The right side draws a value it never
 *    uses; rnd{2} consumes it (it comes last) and asks for its losslessness. *)
module Extra = {
  proc one() : bool = { var b; b <$ {0,1}; return b; }
  proc two() : bool = { var b, u; b <$ {0,1}; u <$ [0..n-1]; return b; }
}.

equiv extra : Extra.one ~ Extra.two : true ==> ={res}.
proof.
  proc; rnd{2}; rnd; skip => /> _ _.
  by apply dinter_ll; smt(gt0_n).            (* is_lossless [0..n-1] *)
qed.

(* ------------------------------------------------------------------------ *)
(* 3. Coupling a game with ITSELF, crosswise: swap the samplings on one side
 *    so that the left x meets the right y.  rnd pairs the last samplings, so
 *    after swap{2} 1 1 it couples y{1} with x{2}, then x{1} with y{2}. *)
module Two = {
  proc pair() : int * int = {
    var x, y;
    x <$ [0..n-1];
    y <$ [0..n-1];
    return (x, y);
  }
}.

equiv mirror : Two.pair ~ Two.pair : true ==> res{1}.`1 = res{2}.`2 /\ res{1}.`2 = res{2}.`1.
proof. by proc; swap{2} 1 1; rnd; rnd; skip. qed.

(* A symmetry argument is then one byequiv: the events are exchanged. *)
lemma lt_sym &m :
  Pr[Two.pair() @ &m : res.`1 < res.`2] = Pr[Two.pair() @ &m : res.`2 < res.`1].
proof. by byequiv mirror => // /#. qed.

(* The same with an adversary in between.  Two hidden points, neither given
 * to it: its guess hits the one as often as the other.  call (: true) gives
 * ={res, glob A} because A cannot read Hidden. *)
module type Guesser = { proc guess() : int }.

module Hidden (A : Guesser) = {
  var a, b : int
  proc main() : int = {
    var g;
    a <$ [0..n-1];
    b <$ [0..n-1];
    g <@ A.guess();
    return g;
  }
}.

lemma guess_sym (A <: Guesser {-Hidden}) &m :
  Pr[Hidden(A).main() @ &m : res = Hidden.a] = Pr[Hidden(A).main() @ &m : res = Hidden.b].
proof.
  byequiv (: ={glob A} ==> ={res} /\ Hidden.a{1} = Hidden.b{2} /\ Hidden.b{1} = Hidden.a{2}) => //.
  by proc; call (: true); swap{2} 1 1; rnd; rnd; skip.
qed.
