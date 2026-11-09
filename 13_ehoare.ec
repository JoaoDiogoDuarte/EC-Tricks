(* ehoare: expectations instead of events.
 * Run: easycrypt compile 13_ehoare.ec
 *
 *   ehoare[c : f ==> g]     the expected value of g after c is at most f
 *                           before it; f, g : xreal (nonnegative, maybe oo)
 *
 * The bridge to probabilities is the indicator: Pr[c : E] is the
 * expectation of E%xr.  So
 *   byehoare (: f ==> E%xr)     proves  Pr[c @ &m : E] <= f{m}
 * (an upper bound only).
 *
 * Coercions: x%xr for a real, i%xr for an int, b%xr for a bool (1 or 0).
 * (b `|` f) is f when b holds and oo otherwise: a precondition guarded by b.
 *
 * What makes ehoare worth it: call (: inv) through an abstract adversary,
 * with an invariant inv that is an expectation.  Each oracle call must not
 * increase inv on average, whatever state it starts from; then the whole
 * run does not either, whatever the adversary does between calls.  The
 * same union bound as 12_fel.ec, as one invariant.
 *)
require import AllCore List Distr DInterval Xreal.
(*---*) import StdOrder.RealOrder.

op n : { int | 0 < n } as gt0_n.
op q : { int | 0 <= q } as ge0_q.

lemma mu_hit : mu [0..n-1] (pred1 0) = inv n%r.
proof. by rewrite dinter1E; smt(gt0_n). qed.

(* ------------------------------------------------------------------------ *)
(* 1. One sampling. *)
module F = {
  proc hit() : bool = { var x; x <$ [0..n-1]; return x = 0; }
}.

ehoare hit_e : F.hit : (inv n%r)%xr ==> res%xr.
proof.
  proc; rnd; skip => &hr /=.
  by rewrite Ep_mu -/(pred1 0) mu_hit.
qed.

lemma hit_pr &m : Pr[F.hit() @ &m : res] <= inv n%r.
proof.
  have hb : 0%r <= inv n%r by smt(gt0_n invr_ge0).
  by byehoare hit_e.
qed.

(* ------------------------------------------------------------------------ *)
(* 2. The union bound of 12_fel.ec as an expectation invariant.  The
 *    potential is bad plus what the remaining calls may still add:
 *      pot = bad + (q - cnt) / n.
 *    A served call turns (bad, cnt) into (bad \/ x = 0, cnt + 1); on
 *    average it adds at most 1/n to bad and removes exactly 1/n from the
 *    second term. *)
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

op pot (bad : bool) (cnt : int) : xreal = bad%xr + ((q - cnt)%r / n%r)%xr.

(* One served call does not increase pot on average.  The xreal goal turns
 * into real arithmetic over %pos once the expectations are computed: EpD
 * splits a sum, EpC a constant (times the weight), Ep_mu an indicator. *)
lemma pot_step (b : bool) (c : int) : c < q =>
  Ep [0..n-1] (fun x => pot (b \/ x = 0) (c + 1)) <= pot b c.
proof.
  move=> hc; have hn : 0 <= n - 1 by smt(gt0_n).
  rewrite /pot; apply (xle_trans (Ep [0..n-1] (fun x => b%xr + ((x = 0)%xr + ((q - (c + 1))%r / n%r)%xr)))).
  + by apply le_Ep => x _ /=; rewrite /(%pos); smt().
  rewrite EpD EpC EpD EpC Ep_mu weight_dinter hn /= -/(pred1 0) mu_hit /(%pos).
  have -> : (q - c)%r / n%r = inv n%r + (q - (c + 1))%r / n%r by field; smt(gt0_n).
  smt(gt0_n invr_ge0 divr_ge0).
qed.

(* The oracle keeps the invariant.  Take x <- 0 off with seq 1: sp does not
 * apply to ehoare goals.  In ehoare an if puts its condition in front of
 * each branch's pre, as (cond) `|` pot: open it with xle_cxr_r. *)
ehoare O_pot : O.f : pot O.bad O.cnt ==> pot O.bad O.cnt.
proof.
  proc; seq 1 : (pot O.bad O.cnt); first by auto.
  if; last by skip => &hr; apply xle_cxr_r => _; apply xlexx.
  (* in ehoare, wp also goes through the sampling: it becomes an Ep *)
  wp; skip => &hr /=; apply xle_cxr_r => hlt.
  exact (pot_step O.bad{hr} O.cnt{hr} hlt).
qed.

(* The whole run: call (: inv) through the adversary.  The event is below
 * the potential (conseq), and the potential starts at q/n. *)
lemma pr_bad (A <: Adv {-O}) &m : Pr[G(A).main() @ &m : O.bad] <= q%r / n%r.
proof.
  (* newer EasyCrypt also asks for 0 <= bound: have it, => // uses it *)
  have hb : 0%r <= q%r / n%r by smt(ge0_q gt0_n divr_ge0).
  byehoare (: (q%r / n%r)%xr ==> O.bad%xr) => //.
  (* conseq in ehoare: the post implication comes back as a guard
   * (forall modified variables, new post <= old post) `|` ... on both sides *)
  proc; conseq (: _ ==> pot O.bad O.cnt).
  + move=> &hr; apply xle_cxr_l; last by apply xlexx.
    by move=> b c; rewrite /pot; apply xle_add_r.
  + by move=> &hr; apply xle_cxr_r => h; apply h.
  call (: pot O.bad O.cnt); first by conseq O_pot.
  by wp; skip => &hr; rewrite /pot /=; smt(ge0_q gt0_n divr_ge0).
qed.

(* ------------------------------------------------------------------------ *)
(* 3. An ehoare judgment carried across an equiv.  There is no conseq that
 *    combines an ehoare with a hoare spec, so a program that calls a
 *    procedure known only by its hoare spec is handled through a reference
 *    program that computes the function directly:
 *      ehoare for the reference (no call in it),
 *      equiv program ~ reference (where the spec is usable, one-sided),
 *      conseq E H on the program.
 *    The side goals of conseq E H: for every left memory there are values
 *    of what the right pre mentions with E's pre and H's pre <= ours (or
 *    ours infinite); and E's post makes our post <= H's post. *)
op P : int -> bool.

module type Det = { proc run(x : int) : bool }.

module Prog (D : Det) = {
  proc hit() : bool = { var x, b; x <$ [0..n-1]; b <@ D.run(x); return b; }
}.

module Ref = {
  proc hit() : bool = { var x; x <$ [0..n-1]; return P x; }
}.

ehoare ref_e : Ref.hit : (mu [0..n-1] P)%xr ==> res%xr.
proof. by proc; wp; skip => &hr /=; rewrite Ep_mu. qed.

section.

declare module D <: Det.

declare axiom D_ll : islossless D.run.

declare axiom D_spec (x0 : int) : hoare[D.run : x = x0 ==> res = P x0].

equiv prog_ref : Prog(D).hit ~ Ref.hit : true ==> ={res}.
proof.
  proc; seq 1 1 : (={x}); first by auto.
  exists* x{1}; elim* => x0.
  call{1} (: x = x0 ==> res = P x0); first by conseq D_ll (D_spec x0).
  by auto.
qed.

ehoare prog_e : Prog(D).hit : (mu [0..n-1] P)%xr ==> res%xr.
proof. by conseq prog_ref ref_e => // &1 &2 ->. qed.

end section.
