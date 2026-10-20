(* Loops: invariants, variants, and replacing a loop by the function it
 * computes.
 * Run: easycrypt compile 11_while.ec
 *
 *   while (I)          hoare: I holds before, and the body keeps I while the
 *                      guard holds; after the loop: I /\ !guard
 *   while (I) (v)      losslessness (phoare = 1): for every z, the body run
 *                      from guard /\ I /\ v = z terminates with I /\ v < z;
 *                      and before the loop, v <= 0 must imply !guard
 *   rcondt n / rcondf n   the if (or while) at statement n is taken / not
 *                      taken: prove its condition after the first n-1
 *                      statements
 *
 * A procedure that loops is best given a functional spec, a hoare triple
 * "res = the function of the arguments", plus termination.  The spec is
 * then used on each side of an equiv separately (call{1}, call{2}), which
 * works even when the two loops do not run in step.
 *)
require import AllCore List.

op f : int -> int.

module M = {
  var tmp : int                      (* a global the procedures borrow *)

  (* map f, left to right *)
  proc fwd(l : int list) : int list = {
    var i, r, s;
    s <- tmp;
    i <- 0; r <- [];
    while (i < size l) {
      tmp <- f (nth 0 l i);
      r <- rcons r tmp;
      i <- i + 1;
    }
    tmp <- s;
    return r;
  }

  (* map f, right to left *)
  proc bwd(l : int list) : int list = {
    var i, r;
    i <- size l; r <- [];
    while (0 < i) {
      i <- i - 1;
      r <- f (nth 0 l i) :: r;
    }
    return r;
  }
}.

(* ------------------------------------------------------------------------ *)
(* 1. A hoare invariant.  r = map f (take i l), and take (i+1) l is
 *    rcons (take i l) (nth 0 l i) (take_nth).  The global the loop borrows
 *    is put back: the spec says so, with an initial value t0. *)
lemma fwd_spec (l0 : int list) (t0 : int) :
  hoare[M.fwd : l = l0 /\ M.tmp = t0 ==> res = map f l0 /\ M.tmp = t0].
proof.
  proc; wp.
  while (0 <= i <= size l /\ r = map f (take i l) /\ s = t0).
  + by auto => /> &hr h0 _ hlt; rewrite (take_nth 0) // map_rcons /#.
  by auto => />; smt(take0 take_size size_ge0).
qed.

(* 2. The variant: size l - i.  The goal has a fresh z for its value. *)
lemma fwd_ll : islossless M.fwd.
proof.
  proc; wp; while (true) (size l - i).
  + by move=> z; auto => /#.
  by auto => /#.
qed.

lemma bwd_spec (l0 : int list) :
  hoare[M.bwd : l = l0 ==> res = map f l0].
proof.
  proc.
  while (0 <= i <= size l /\ r = map f (drop i l) /\ l = l0).
  + auto => /> &hr h0 hle hlt; rewrite (drop_nth 0 (i{hr} - 1) l0) 1:/# /= /#.
  by auto => />; smt(drop0 drop_size size_ge0).
qed.

lemma bwd_ll : islossless M.bwd.
proof.
  by proc; while (true) (i); auto => /#.
qed.

(* ------------------------------------------------------------------------ *)
(* 3. Two loops that do not run in step are equivalent because they compute
 *    the same function.  Name the arguments and the borrowed global with
 *    exists* and elim*, then run each side alone with its spec made a
 *    phoare = 1 (conseq ll spec). *)
equiv fwd_bwd : M.fwd ~ M.bwd : ={l} ==> ={res}.
proof.
  proc*.                           (* the calls become statements: r <@ M.fwd(l) *)
  exists* l{1}, M.tmp{1}; elim* => l0 t0.
  call{1} (: l = l0 /\ M.tmp = t0 ==> res = map f l0 /\ M.tmp = t0).
  + by conseq fwd_ll (fwd_spec l0 t0).
  call{2} (: l = l0 ==> res = map f l0).
  + by conseq bwd_ll (bwd_spec l0).
  by skip => />.
qed.

(* ------------------------------------------------------------------------ *)
(* 4. A loop that calls an oracle with a spec: ecall (lemma args) applies the
 *    spec at the current values of program variables, which a plain call
 *    cannot do from inside the loop body. *)
op g : int -> int.

module type Orc = { proc get(x : int) : int }.

module Loop (O : Orc) = {
  proc run(l : int list) : int list = {
    var i, r, y;
    i <- 0; r <- [];
    while (i < size l) {
      y <@ O.get(nth 0 l i);
      r <- rcons r y;
      i <- i + 1;
    }
    return r;
  }
}.

section.

declare module O <: Orc.

declare axiom O_spec (x0 : int) : hoare[O.get : x = x0 ==> res = g x0].

lemma run_spec (l0 : int list) : hoare[Loop(O).run : l = l0 ==> res = map g l0].
proof.
  proc.
  while (0 <= i <= size l /\ r = map g (take i l) /\ l = l0).
  + wp; ecall (O_spec (nth 0 l i)); auto => /> &hr h0 _ hlt.
    by rewrite (take_nth 0) // map_rcons /#.
  by auto => />; smt(take0 take_size size_ge0).
qed.

end section.

(* ------------------------------------------------------------------------ *)
(* 5. A branch whose condition is known.  rcondt 2 says the if at statement 2
 *    is taken (after statement 1, c < 1), and leaves its body inline. *)
module Once = {
  var c : int
  proc f() : int = {
    var r;
    r <- 0;
    c <- 0;
    if (c < 1) { c <- c + 1; r <- 5; }
    return r;
  }
}.

lemma once : hoare[Once.f : true ==> res = 5].
proof. by proc; rcondt 3; [auto | auto]. qed.
