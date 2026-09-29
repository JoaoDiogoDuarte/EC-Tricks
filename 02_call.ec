(* call: the shapes worth knowing.
 * Run: easycrypt compile 02_call.ec *)
require import AllCore.

module type Orc = {
  proc get(x : int) : int
}.

(* An adversary with one state-reading procedure that may NOT call the oracle
 * ({} = empty list of allowed oracle procedures) and one that may. *)
module type Adv (O : Orc) = {
  proc save() : int {}
  proc run() : bool
}.

module O1 : Orc = {
  var n : int
  proc get(x : int) : int = { n <- n + 1; return x; }
}.

module O2 : Orc = {
  var m : int
  proc get(x : int) : int = { m <- m + 1; return x; }
}.

(* An oracle that is a mere alias of another. *)
module W (O : Orc) : Orc = {
  proc get = O.get
}.

module G (O : Orc) (A : Adv) = {
  var s : int
  proc main() : bool = {
    var b;
    s <@ A(O).save();
    b <@ A(O).run();
    return b;
  }
}.

section.

declare module A <: Adv {-O1, -O2, -G}.
declare module O <: Orc {-A}.

(* ------------------------------------------------------------------------ *)
(* 1. Abstract adversary, different oracles: call with an invariant I.
 *    One goal per oracle procedure: ={arg} /\ I ==> ={res} /\ I.
 *    The call itself gives ={res, glob A} /\ I from ={arg, glob A} /\ I. *)
lemma run_rel :
  equiv [G(O1, A).main ~ G(O2, A).main :
         ={glob A} /\ O1.n{1} = O2.m{2} ==> ={res} /\ O1.n{1} = O2.m{2}].
proof.
  proc.
  call (: O1.n{1} = O2.m{2}).
  + by proc; auto.                  (* the oracle goal *)
  (* save has {} : it touches nothing but glob A, so (: true) is enough and
   * every other fact in the precondition is carried over unchanged. *)
  call (: true).
  by auto.
qed.

(* The same statement proved directly on the procedure: proc I. *)
lemma run_rel' :
  equiv [A(O1).run ~ A(O2).run :
         ={glob A} /\ O1.n{1} = O2.m{2} ==> ={res, glob A} /\ O1.n{1} = O2.m{2}].
proof.
  proc (O1.n{1} = O2.m{2}) => //.
  by proc; auto.
qed.

(* ------------------------------------------------------------------------ *)
(* 2. An abstract oracle procedure, or an alias of one: proc* then call (: true).
 *    For an abstract procedure call (: true) gives ={res, glob O} from
 *    ={arg, glob O}. *)
equiv w_get : W(O).get ~ W(O).get : ={arg, glob O} ==> ={res, glob O}.
proof. by proc*; call (: true); auto. qed.

(* ------------------------------------------------------------------------ *)
(* 3. One-sided call: call{1} / call{2} with a phoare = 1 spec.
 *    The other side does nothing; the spec's post is all you learn. *)
module K = {
  var c : int
  proc tick() : unit = { c <- c + 1; }
  proc two() : unit = { tick(); tick(); }
  proc one() : unit = { tick(); }
}.

lemma tick_ph (n : int) : phoare [K.tick : K.c = n ==> K.c = n + 1] = 1%r.
proof. by proc; auto. qed.

lemma drop_one :
  equiv [K.two ~ K.one : ={K.c} ==> K.c{1} = K.c{2} + 1].
proof.
  proc.
  (* last calls, two-sided.  For a concrete procedure give a full spec
   * (: P ==> Q); the invariant form (: I) is for abstract procedures. *)
  call (: K.c{1} = K.c{2} + 1 ==> K.c{1} = K.c{2} + 1).
  + by proc; auto.
  (* the remaining left-only call: fix K.c{1}, then call{1} *)
  exlim K.c{1} => n.
  call{1} (tick_ph n).
  by auto => /#.
qed.

(* A lossless spec drops a call whose effect you don't care about:
 *   call{1} some_ll.      where some_ll : islossless P.f
 * You lose every fact about what P.f writes. *)

(* ------------------------------------------------------------------------ *)
(* 4. call with a spec lemma instead of an invariant (hoare or equiv). *)
lemma tick_h (n : int) : hoare [K.tick : K.c = n ==> K.c = n + 1].
proof. by proc; auto. qed.

lemma two_h (n : int) : hoare [K.two : K.c = n ==> K.c = n + 2].
proof.
  proc.
  call (tick_h (n + 1)).
  call (tick_h n).
  by auto => /#.
qed.

end section.
