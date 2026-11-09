(* ehoare: bounding EXPECTED values (expectation Hoare logic).
 * Run: easycrypt compile 14_ehoare_patterns.ec
 *
 *   ehoare [ M.f : pre ==> post ]
 *
 * pre and post are xreal-valued (xreal = non-negative reals + oo).  The
 * judgment says: for every initial memory, the expected value of post over
 * the final memories is at most pre (evaluated in the initial memory).
 * Read it as "post is a potential; pre pays for it".
 *
 * Vocabulary (theory Xreal):
 *   x%xr          real / int / bool into xreal (negative reals become 0,
 *                 bools become 0 or 1)
 *   b `|` x       "x if b, oo otherwise": puts a boolean fact in a pre.
 *                 An oo pre is trivially true, so b is an assumption.
 *   Ep d f        expectation of f : 'a -> xreal under d
 *   xle_cxr_r     (b => x <= y) => x <= (b `|` y)      (use the fact b)
 *   xle_cxr_l     b => x <= y  => (b `|` x) <= y       (discharge b)
 *   xle_cxr       both at once
 *   xle_rle       0 <= x <= y => x%xr <= y%xr          (back to reals)
 *   xlexx         x <= x
 *   Ep_mu         Ep d (fun x => (p x)%xr) = (mu d p)%xr
 *   EpC           Ep d (fun _ => c) = (weight d) ** c
 *   Ep_dbool      Ep {0,1} f = 0.5 ** f true + 0.5 ** f false
 *
 * After proc; wp; skip (or auto) the goal is   forall &hr, post' <= pre
 * (an xreal inequality), which smt / the lemmas above close. *)
require import AllCore Distr DBool Xreal.
require import StdOrder.
import RealOrder.

module M = {
  var hits : int

  proc coin() : bool = {
    var b;
    b <$ {0,1};
    return b;
  }

  proc incr(x : int) : int = { return x + 1; }

  proc flip() : unit = {
    var b;
    b <$ {0,1};
    if (b) hits <- hits + 1;
  }

  proc run(n : int) : unit = {
    var i;
    i <- 0;
    while (i < n) {
      flip();
      i <- i + 1;
    }
  }
}.

(* ------------------------------------------------------------------------ *)
(* 1. rnd turns the post into an expectation over the distribution.
 *    Close with a law-specific lemma (Ep_dbool: the two-point average) or
 *    with Ep_mu for an indicator.  Note: rewrite Ep_mu did not match
 *    fun b => b%xr here (higher-order pattern); Ep_dbool does. *)
lemma coin_e : ehoare [M.coin : (1%r / 2%r)%xr ==> res%xr].
proof.
  proc; rnd; skip => &hr /=.
  (* goal:  Ep {0,1} (fun b => b%xr) <= (1/2)%xr *)
  by rewrite Ep_dbool.
qed.

(* ------------------------------------------------------------------------ *)
(* 2. ehoare -> Pr bound: byehoare (: pre ==> post).
 *    The event is res; the post must be >= the indicator (res%xr here). *)
module G = {
  proc main() : bool = { var b; b <@ M.coin(); return b; }
}.

lemma pr_coin &m : Pr[G.main() @ &m : res] <= 1%r / 2%r.
proof.
  (* side goal: the pre is a non-negative real (0 <= 1/2) *)
  byehoare (: (1%r / 2%r)%xr ==> res%xr) => //; last by smt().
  by proc; call coin_e; skip => &hr; exact xlexx.
qed.

(* ------------------------------------------------------------------------ *)
(* 3. "Exact" specs for any potential K.  For a deterministic procedure,
 *    ehoare [f : K (spec arg) ==> K res]  for every K  is as strong as the
 *    functional spec; it is the form that composes in ehoare proofs.
 *    (Simon.ec: evaluate_expectation, find_partner_expectation, ...) *)
lemma incr_K (K : int -> xreal) : ehoare [M.incr : K (x + 1) ==> K res].
proof. by proc; skip => &hr; apply xlexx. qed.

(* ------------------------------------------------------------------------ *)
(* 4. call with a TRANSFORMER:  call /(fun v => F v) lemma.
 *    From  ehoare [f : P ==> Q]  it uses  ehoare [f : F P ==> F Q]  when F
 *    is concave and increasing (EasyCrypt asks for that as a side goal,
 *    usually closed automatically).  Two transformers do most of the work:
 *
 *      (fun v => p%xr * v)      scale a bound by p       (LateSample.ec)
 *      (fun v => (A) `|` v)     carry a boolean fact A across the call:
 *                               A must only mention variables the call
 *                               does not modify (a frame).          *)
module N = {
  proc twice() : bool = {
    var b;
    b <@ M.coin();
    return b;
  }
}.

(* Scaling: from the 1/2 of coin_e get 1/4 for "res, times 1/2".
 * Write the scaling as  c%xr * v  (an xreal product).  With  c ** v  the
 * concavity side condition sent EasyCrypt r2026.10 into a loop. *)
lemma coin_scaled :
  ehoare [N.twice : (1%r / 4%r)%xr ==> (1%r / 2%r)%xr * res%xr].
proof.
  proc; call /(fun v => (1%r / 2%r)%xr * v) coin_e.
  (* remaining: (1/2) * (1/2) <= 1/4 in xreal; /= computes it *)
  by skip => &hr /=.
qed.

(* Framing: x0 is not modified by the call, so x = x0 can be carried. *)
module P = {
  proc f(x : int) : int = {
    var y;
    y <@ M.incr(x);
    return y + x;
  }
}.

lemma f_K (K : int -> xreal) : ehoare [P.f : K (2 * x + 1) ==> K res].
proof.
  proc.
  exlim x => x0.                                      (* name x *)
  call /(fun v => (x = x0) `|` v) (incr_K (fun r => K (r + x0))).
  (* goal 1: the post of the call (framed) pays for the outer post *)
  + by move=> &hr; apply xle_cxr_r => ->; exact xlexx.
  (* goal 2: the outer pre pays for the pre of the call (framed) *)
  skip => &hr; apply xle_cxr => <- /=.
  by rewrite (_ : x0 + 1 + x0 = 2 * x0 + 1) 1:/# xlexx.
qed.

(* ------------------------------------------------------------------------ *)
(* 5. while: the invariant is an xreal potential.  Pattern:
 *
 *      while ((side facts) `|` potential).
 *      + exit:  !cond /\ I  pays for the post          (move=> &hr; xle_cxr_r)
 *      + body:  ehoare [body : I ==> I]   (with cond in the pre)
 *      the code before the loop must pay for I.
 *
 *    Here: n coins; the expected number of heads is hits + (n - i) / 2. *)
lemma flip_e :
  ehoare [M.flip : (0 <= M.hits) `|` (M.hits%r + 1%r / 2%r)%xr
               ==> (0 <= M.hits) `|` M.hits%xr].
proof.
  proc; seq 1 : ((0 <= M.hits) `|` (M.hits%r + b2r b)%xr).
  + rnd; skip => &hr /=.
    (* First take the side condition out (xle_cxr_r), and only then
     * simplify the expectation: in the other order the goal blows up. *)
    apply xle_cxr_r => h; rewrite h /=.
    (* Ep_dbool: 1/2 f true + 1/2 f false; %pos is max(., 0) on reals *)
    by rewrite Ep_dbool /= !to_pos_pos; smt().
  by if; auto => &hr /=; apply xle_cxr => -[hb h]; rewrite hb /=; smt().
qed.

lemma run_e :
  ehoare [M.run : (0 <= M.hits /\ 0 <= n) `|` (M.hits%r + n%r / 2%r)%xr
              ==> M.hits%xr].
proof.
  proc.
  while ((0 <= M.hits /\ 0 <= i <= n) `|` (M.hits%r + (n - i)%r / 2%r)%xr).
  + (* exit: the potential pays for the post.  /= first merges the nested
     * `|` (cxrA), then xle_cxr_r assumes the facts. *)
    by move=> &hr /=; apply xle_cxr_r => /> *; smt().
  + (* body: fix i and n, frame them across the call of flip, and add the
     * part of the budget the remaining iterations will spend. *)
    wp; exlim i, n => i0 n0.
    call /(fun v => (i = i0 /\ n = n0 /\ 0 <= i0 < n0)
                    `|` (v + ((n0 - (i0 + 1))%r / 2%r)%xr)) flip_e.
    + (* the framed post of flip pays for the invariant after i <- i + 1 *)
      move=> &hr /=; apply xle_cxr_r => /> *.
      apply xle_cxr_l; first smt().
      by rewrite of_realD; smt().
    (* the invariant, with i < n, pays for the framed pre of flip *)
    skip => &hr /=; apply xle_cxr_r => /> *.
    smt(to_pos_pos).
  (* before the loop *)
  by auto => &hr /=; apply xle_cxr => /> *; smt().
qed.

(* ------------------------------------------------------------------------ *)
(* 6. Expected count -> probability: "at least one head" is at most n/2
 *    (Markov-style: the indicator of hits >= 1 is below hits%xr). *)
module R = {
  proc main(n : int) : bool = {
    M.hits <- 0;
    M.run(n);
    return 1 <= M.hits;
  }
}.

lemma pr_some_head &m (n0 : int) : 0 <= n0 =>
  Pr[R.main(n0) @ &m : res] <= n0%r / 2%r.
proof.
  move=> hn.
  byehoare (: (n = n0) `|` (n0%r / 2%r)%xr ==> res%xr) => //; last by smt().
  proc; wp.
  (* conseq in ehoare: the side goals quantify over what the program
   * modifies, so a fact like "the indicator is below hits" shows up as
   * a forall in a `|` condition. *)
  conseq (: _ ==> M.hits%xr).
  + move=> &hr; apply xle_cxr_l; last exact xlexx.
    by move=> h; case: (1 <= h) => /= ?; smt().
  + by move=> &hr; apply xle_cxr_r => h; exact (h M.hits{hr}).
  call run_e; wp; skip => &hr /=.
  by apply xle_cxr => ->.
qed.

(* ------------------------------------------------------------------------ *)
(* 7. An abstract adversary: call (: potential).
 *    The adversary makes any number of oracle calls; the oracle answers
 *    at most q of them, and each answered call flips a coin.  Expected
 *    heads <= q/2.  Budget the unanswered calls in the potential:
 *        (facts) `|` (hits + (q - n) / 2)
 *    Each answered call spends 1/2 of the budget and pays for the
 *    expected new head; the oracle goal is ehoare [query : I ==> I].
 *    (SwapCore.ec: recording_potential, finder_query_preserves_potential.) *)
op q : { int | 0 <= q } as ge0_q.

module type Oracle = { proc query() : unit }.

module Ob : Oracle = {
  var n : int
  proc query() : unit = {
    if (n < q) {
      n <- n + 1;
      M.flip();
    }
  }
}.

module type AdvT (O : Oracle) = { proc run() : unit }.

module H (A : AdvT) = {
  proc main() : unit = {
    M.hits <- 0;
    Ob.n <- 0;
    A(Ob).run();
  }
}.

op pot (hits n : int) : xreal =
  (0 <= hits /\ 0 <= n <= q) `|` (hits%r + (q - n)%r / 2%r)%xr.

lemma query_pot : ehoare [Ob.query : pot M.hits Ob.n ==> pot M.hits Ob.n].
proof.
  proc; if; last first.
  + by skip => &hr; apply xle_cxr_r => _; exact xlexx.
  call /(fun v => (0 <= Ob.n <= q) `|` (v + ((q - Ob.n)%r / 2%r)%xr)) flip_e.
  + by move=> &hr /=; rewrite /pot; apply xle_cxr_r => /> *; smt(to_pos_pos).
  (* the pre is  (n < q) `|` (pot facts `|` ...) : peel the outer
   * condition first, then relate the two inner ones *)
  wp; skip => &hr /=; rewrite /pot; apply xle_cxr_r => /> *.
  by apply xle_cxr => /> *; smt(to_pos_pos).
qed.

section.

declare module A <: AdvT {-M, -Ob}.

lemma adv_heads : ehoare [H(A).main : (q%r / 2%r)%xr ==> M.hits%xr].
proof.
  proc.
  (* weaken the post to the potential; "hits <= pot hits n" is the
   * universally quantified side condition *)
  conseq (: _ ==> pot M.hits Ob.n).
  + move=> _; apply xle_cxr_l; last exact xlexx.
    by move=> h n; rewrite /pot; apply xle_cxr_r => /> *; smt().
  + by move=> &hr; apply xle_cxr_r => h; exact (h M.hits{hr} Ob.n{hr}).
  call (: pot M.hits Ob.n).
  + exact query_pot.
  by auto => &hr /=; rewrite /pot /=; smt(ge0_q).
qed.

end section.
