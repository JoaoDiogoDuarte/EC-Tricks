(* exlim / exists* and seq.
 * Run: easycrypt compile 03_exlim_seq.ec
 *
 * THE RULE: exlim e => v  binds v to the value of e in the PRECONDITION of
 * the current goal, i.e. at the START of the program that is left.  If the
 * program changes e before the point where you need v, first cut the program
 * so that point becomes the start (seq, sp), then exlim.
 *
 *   exlim e1, e2 => a b.          same as   exists* e1, e2; elim* => a b.
 *   exlim x{1}, M.y{2} => a b.    relational goals: say which side.
 *)
require import AllCore.

module P = {
  var x : int
  proc inc() : unit = { x <- x + 1; }
  proc main() : unit = { x <- 5; inc(); }
  proc main2() : unit = { inc(); }
}.

lemma inc_h (n : int) : hoare [P.inc : P.x = n ==> P.x = n + 1].
proof. by proc; auto. qed.

lemma inc_ph (n : int) : phoare [P.inc : P.x = n ==> P.x = n + 1] = 1%r.
proof. by proc; auto. qed.

(* ------------------------------------------------------------------------ *)
(* WRONG: exlim at the top binds the value BEFORE x <- 5, so the call's
 * precondition P.x = n cannot be met:
 *
 *   proc. exlim P.x => n. call (inc_h n).   (* stuck: need 5 = n *)
 *
 * RIGHT: cut first, so the call is at the start of what is left.          *)
lemma main_h : hoare [P.main : true ==> P.x = 6].
proof.
  proc.
  seq 1 : (P.x = 5); first by auto.   (* hoare seq: seq <#stmts> : (P) *)
  exlim P.x => n.                     (* now n is the value at the call *)
  call (inc_h n).
  by auto => /#.
qed.

(* For straight-line assignments at the start, sp does the cut for you. *)
lemma main_h' : hoare [P.main : true ==> P.x = 6].
proof.
  proc; sp.                           (* pre is now P.x = 5 *)
  exlim P.x => n.
  call (inc_h n).
  by auto => /#.
qed.

(* ------------------------------------------------------------------------ *)
(* Relational version: a one-sided call needs the ghost at the call point.
 * equiv seq: seq <#left> <#right> : (P).  #pre = the current precondition. *)
lemma main_eq : equiv [P.main ~ P.main2 : true ==> P.x{1} = 6].
proof.
  proc.
  seq 1 0 : (P.x{1} = 5); first by auto.
  exlim P.x{1} => n.
  call{1} (inc_ph n).
  (* right side still has its call; drop it one-sided too (no ghost needed) *)
  call{2} (: true ==> true); first by proc; auto.
  by auto => /#.
qed.

(* ------------------------------------------------------------------------ *)
(* Calls are processed from the END of the program.  exlim at the top is fine
 * when nothing before the call changes the value: then "value at the start"
 * and "value at the call" coincide. *)
lemma twice (n : int) :
  equiv [P.main2 ~ P.main2 : P.x{1} = n /\ P.x{2} = n ==> ={P.x}].
proof.
  proc.
  exlim P.x{1} => v.                   (* fine: inc is the first statement *)
  call{1} (inc_ph v).
  exlim P.x{2} => w.
  call{2} (inc_ph w).
  by auto => /#.
qed.

(* ------------------------------------------------------------------------ *)
(* Other cutting tools
 *   seq 3 3 : (#pre /\ ={x}).        keep the old facts and add one
 *   seq 1 1 : (Q); first by ... .    discharge the prefix inline
 *   sp / sp 1 1                      consume leading assignments into the pre
 *   wp                               consume trailing assignments into the post
 *   swap{1} 3 -2                     move left statement 3 up by 2 (needs
 *                                    syntactic independence)                  *)
