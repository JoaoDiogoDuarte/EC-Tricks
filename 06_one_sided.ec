(* Dropping one-sided calls to an abstract adversary (e.g. a discarded run in
 * a rewinding reduction).
 * Run: easycrypt compile 06_one_sided.ec
 *
 * Recipe:
 *   1. for every call you drop, a phoare [...] = 1%r spec saying what it does
 *      to the state you still care about;
 *   2. exlim the values those specs need, at a point where they are right
 *      (see 03_exlim_seq.ec);
 *   3. call{1} each spec, from the LAST dropped call backwards;
 *   4. close with auto / smt.
 *
 * Where the phoare specs come from:
 *   - losslessness + a hoare fact:  conseq ll H          (01_conseq.ec, 4.)
 *   - an axiom stated with Pr[...] = 1%r:  bypr => &m ...; exact ...
 *)
require import AllCore.

module type Orc = {
  proc get(x : int) : int
}.

(* save and load may not call the oracle ({}): they are the reduction's
 * snapshot of the adversary, not adversary actions. *)
module type Adv (O : Orc) = {
  proc save() : int {}
  proc load(s : int) : unit {}
  proc run() : bool
}.

(* An oracle that only reads its state, so a run leaves it unchanged. *)
module Cnt : Orc = {
  var k : int
  proc get(x : int) : int = { return x + k; }
}.

module G1 (A : Adv) = {
  var st : int
  proc main() : bool = {
    var b1, b2;
    st <@ A(Cnt).save();
    b1 <@ A(Cnt).run();           (* discarded run *)
    A(Cnt).load(st);
    b2 <@ A(Cnt).run();
    return b2;
  }
}.

module G2 (A : Adv) = {
  proc main() : bool = {
    var b;
    b <@ A(Cnt).run();
    return b;
  }
}.

section.

declare module A <: Adv {-Cnt, -G1}.

declare axiom A_ll (O <: Orc {-A}) : islossless O.get => islossless A(O).run.

(* Rewindability, stated with probabilities. *)
declare axiom A_rew :
  exists (f : glob A -> int),
    (forall (O <: Orc) &m,
       Pr[A(O).save() @ &m : (glob A) = (glob A){m} /\ res = f (glob A){m}] = 1%r) /\
    (forall (O <: Orc) &m (x : glob A) (s : int),
       s = f x => Pr[A(O).load(s) @ &m : (glob A) = x] = 1%r).

lemma drop_run : equiv [G1(A).main ~ G2(A).main : ={glob A, Cnt.k} ==> ={res}].
proof.
  (* 1. the specs.  f only exists after elim, so these are haves. *)
  elim A_rew => f [hs hl].
  have phs : forall g, phoare [A(Cnt).save : (glob A) = g ==> (glob A) = g /\ res = f g] = 1%r.
  + by move=> g; bypr => &m <-; exact (hs Cnt &m).
  have phl : forall g, phoare [A(Cnt).load : arg = f g ==> (glob A) = g] = 1%r.
  + by move=> g; bypr => &m hs'; exact (hl Cnt &m g arg{m} hs').
  have phr : forall k0, phoare [A(Cnt).run : Cnt.k = k0 ==> Cnt.k = k0] = 1%r.
  + move=> k0; conseq (A_ll Cnt _) (_: Cnt.k = k0 ==> Cnt.k = k0) => //.
    (* goals come out in this order: the hoare fact, then the side condition
     * of A_ll.  When unsure, look: easycrypt llm, then GOALS ALL. *)
    + by proc (Cnt.k = k0) => //; proc; auto.      (* run leaves Cnt.k *)
    by proc; auto.                                 (* Cnt.get is lossless *)
  proc.
  (* the kept run, two-sided *)
  call (: ={Cnt.k}); first by proc; auto.
  (* 2. nothing before the dropped calls changes glob A or Cnt.k, so exlim
   *    at the top gives the right values *)
  exlim (glob A){1}, Cnt.k{1} => g k0.
  (* 3. backwards: load, then the run, then save *)
  call{1} (phl g).
  call{1} (phr k0).
  call{1} (phs g).
  (* 4. *)
  by auto => /#.
qed.

end section.
