(* Program-level tactics: ecall, rcondt / rcondf, termination variants,
 * rewrite equiv[...], proc*, sp with two counts.
 * Run: easycrypt compile 09_program.ec *)
require import AllCore Distr DBool.

module M = {
  var c : int

  proc double(x : int) : int = { return 2 * x; }

  proc twice(x : int) : int = {
    var y, z;
    y <@ double(x);
    z <@ double(y);
    return z;
  }

  proc count(n : int) : int = {
    var i;
    i <- 0;
    while (i < n) { i <- i + 1; }
    return i;
  }

  proc guarded(x : int) : int = {
    var r;
    r <- 0;
    if (0 <= x) { r <- x; } else { r <- -x; }
    return r;
  }
}.

(* ------------------------------------------------------------------------ *)
(* 1. ecall (lemma args): call with a spec whose pre fixes the arguments.
 *    call needs the pre to match; ecall takes the lemma instance and
 *    substitutes the actual arguments (program expressions are allowed as
 *    lemma arguments).  Works in hoare, phoare, and with {1}/{2} in equiv.
 *    (Simon.ec: ecall{1} (evaluate_exact q{1} m{1} w{1}).)              *)
lemma double_spec (x0 : int) : hoare [M.double : x = x0 ==> res = 2 * x0].
proof. by proc; auto. qed.

lemma twice_spec (x0 : int) : hoare [M.twice : x = x0 ==> res = 4 * x0].
proof.
  proc.
  ecall (double_spec y).          (* y : the program variable *)
  ecall (double_spec x).
  by auto => /#.
qed.

lemma double_ll : islossless M.double by proc; auto.

lemma double_exact (x0 : int) :
  phoare [M.double : x = x0 ==> res = 2 * x0] = 1%r.
proof. by conseq double_ll (double_spec x0). qed.

(* One-sided ecall in an equiv: a different, exact fact per side. *)
lemma twice_rel : equiv [M.twice ~ M.twice : x{1} = - x{2} ==> res{1} = - res{2}].
proof.
  proc.
  ecall{1} (double_exact y{1}); ecall{2} (double_exact y{2}).
  ecall{1} (double_exact x{1}); ecall{2} (double_exact x{2}).
  by auto => /#.
qed.

(* ------------------------------------------------------------------------ *)
(* 2. Termination: while (I) (variant).
 *    For islossless / phoare = 1: the variant is an int that decreases at
 *    each iteration and is <= 0 when the loop must stop.  Goals: the body
 *    (for every value z of the variant, it decreases) and the code before
 *    the loop, which must establish I and the exit implication.
 *    (MultiSimon.ec: while (true) (q_eval - i); while (true) (size rest).) *)
lemma count_ll : islossless M.count.
proof.
  proc; while (true) (n - i).
  + by move=> z; auto => /#.
  by auto => /#.
qed.

(* ------------------------------------------------------------------------ *)
(* 3. rcondt / rcondf : decide an if (or the first iteration of a while)
 *    at position n.  Side goal: a hoare triple saying the condition is
 *    true (resp. false) at that point.  rcondt{1} n / rcondf{2} n in an
 *    equiv.  (HRFixed.ec / SimonFixed.ec: rcondf{2} 2; first by auto.) *)
lemma guarded_pos (x0 : int) : hoare [M.guarded : x = x0 /\ 0 <= x0 ==> res = x0].
proof.
  proc.
  rcondt 2; first by auto.
  by auto.
qed.

lemma guarded_neg : equiv [M.guarded ~ M.guarded :
                           x{1} = - x{2} /\ 0 < x{1} ==> ={res}].
proof.
  proc.
  (* side goal: forall &m, hoare [prefix : pre, other side read in &m ==> cond] *)
  rcondt{1} 2; first by auto => /#.
  rcondf{2} 2; first by auto => /#.
  by auto.
qed.

(* A while whose condition is known: rcondt unrolls one iteration. *)
lemma count_one : hoare [M.count : n = 1 ==> res = 1].
proof.
  proc.
  rcondt 2; first by auto.
  rcondf 3; first by auto.
  by auto.
qed.

(* ------------------------------------------------------------------------ *)
(* 4. sp n m : symbolic execution of the first n (left) and m (right)
 *    assignments.  sp alone eats as many as possible on both sides; the
 *    counts let you stop before an instruction you want to keep (e.g. one
 *    that writes a variable your invariant reads).  if{1} : case only on
 *    the left if (when the sides branch differently). *)
lemma guarded_left : equiv [M.guarded ~ M.double : x{1} = x{2} /\ 0 <= x{1}
                                                ==> 2 * res{1} = res{2}].
proof.
  proc; sp 1 0.
  if{1}.
  + by auto.
  by exfalso; auto => /#.
qed.

(* ------------------------------------------------------------------------ *)
(* 5. rewrite equiv[{1} n lemma] : replace the call at line n of the left
 *    program by the right program of an equiv lemma (program rewriting).
 *    The lemma must be stated with plain variables (e.g. ={x} ==> ={res}).
 *    Use proc* first, so the goal is about "r <@ M.f(args)" itself.
 *    (HRSwap.ec: rewrite equiv[{1} 1 fresh_procedure_exact].)          *)
module Alt = {
  proc twice(x : int) : int = { return 4 * x; }
}.

lemma twice_alt : equiv [M.twice ~ Alt.twice : ={x} ==> ={res}].
proof.
  proc; inline *; auto => /#.
qed.

lemma twice_sym : equiv [M.twice ~ M.twice : ={x} ==> ={res}].
proof.
  proc*.
  rewrite equiv[{1} 1 twice_alt].
  rewrite equiv[{2} 1 twice_alt].
  by inline *; auto.
qed.
