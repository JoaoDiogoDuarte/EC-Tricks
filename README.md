# EasyCrypt tricks

Small, self-contained examples; each file compiles on its own against the
standard library (checked with EasyCrypt release `r2026.10`).

`TACTICS.md` is a reference for the less common tactics and syntax (ehoare,
`rndsem`, `rnd f g`, the five-argument `seq`, `rcondt`, `rewrite equiv[...]`,
`case @[ambient]`, clone forms, ...): what each does, its syntax, and where
an example is.  Files 07-16 and most of `TACTICS.md` are drawn from the
Simon / Hsiao-Reyzin separation development (`simon/src`).

The same material with explanations is in `easycrypt-tricks.pdf`
(`latexmk -pdf easycrypt-tricks.tex` rebuilds it; the listings are read from
the `.ec` files).

```sh
for f in *.ec; do easycrypt compile "$f" || echo "FAILED: $f"; done
```

Every file was checked with EasyCrypt r2026.07-78 and with the main branch
of October 2026 (r2026.10-1), each time with all provers and with Z3 alone
(`easycrypt compile -p Z3 file.ec`).  The pitfalls below were observed with
r2026.07-78.

| File | What it shows |
|---|---|
| `01_conseq.ec` | applying a spec with weakening; `conseq (: _ ==> Q)` before `sim`; `conseq E H1 H2` (one-sided facts on an equiv); `(_: true ==> true)`; phoare = 1 from `conseq ll H`; conjoining hoare triples |
| `02_call.ec` | `call (: I)` for abstract adversaries; `proc I`; `call (: true)` for `{}` procedures and for oracle aliases (`proc*`); concrete calls need `(: P ==> Q)`; `call{1}` with a phoare spec; `call` with a hoare lemma |
| `03_exlim_seq.ec` | **when exlim binds what**, and how to cut with `seq` / `sp` first; relational exlim; `#pre`; `swap` |
| `04_pr.ec` | `Pr[mu_le1]`, `Pr[mu_sub]`, `Pr[mu_not]`, `Pr[mu_or]`, `Pr[mu_split E]`; Pr = 0 from hoare; phoare / hoare from Pr = 1 via `bypr`; `byequiv` with a lemma and `symmetry`; Pr arithmetic with `smt`; `Pr[E1] <= Pr[E2]` from a hoare fact `E1 => E2`; `Pr[!E] = 1 - Pr[E]` needs termination |
| `05_upto_bad.ec` | `call (: B, I, J)`; every generated goal; `Pr1 <= Pr2 + Pr2[bad]`; equality from `Pr[bad] = 0` |
| `06_one_sided.ec` | dropping a discarded adversary run: phoare specs from `bypr` and `conseq ll H`, then `exlim` and `call{1}` backwards |
| `07_rnd.ec` | `rnd f g` with a bijection (one-time pad, shift mod n) and its side goals; `rnd{2}` for a sample one side never uses; a game coupled with itself crosswise (`swap{2}`, then `rnd; rnd`) for symmetry arguments, also around an adversary |
| `08_late_sample.ec` | a sample the adversary never sees, moved after its run (`swap; rnd; call (: true)`); then `Pr[x in its list] <= k/n` and `Pr[x = its guess] <= 1/n`; the four bounds of a phoare `seq` |
| `09_averaging.ec` | `Pr[G.main(x0) @ &m : res]` as a phoare spec (`bypr`, `byequiv`, `proc true`); a bound for every value of a parameter is a bound for a random one (`exlim`, `case @[ambient]`, a `call` of that spec); from random to fixed: some value is no worse than the average |
| `10_laws.ec` | the exact law of "draw coins, run a procedure known by its spec" (phoare `seq` with five numbers); `byphoare` with it; equivalence from equal laws when no bijection exists (`bypr (res{1}) (res{2})`); `transitivity{1} { s }` and `transitivity` between procedures |
| `11_while.ec` | `while (I)`, `while (I) (v)`; a functional spec that puts back a borrowed global; two loops that do not run in step, equivalent by their specs one-sided (`proc*`, `call{1}`, `call{2}`); `ecall` in a loop body; `rcondt` |
| `12_fel.ec` | `fel`: every argument, every goal it leaves and in which order |
| `13_ehoare.ec` | `ehoare` and `byehoare`; the bound of `12_fel.ec` as an expectation invariant through an adversary (`call (: inv)`, `Ep` / `xreal` arithmetic); an ehoare carried across an equiv (`conseq E H`) |
| `14_ehoare_patterns.ec` | more ehoare: `%xr`, `` `\|` ``, `rnd` + `Ep_dbool`; "exact" specs for every potential `K`; `call /(fun v => ...)` to frame facts and scale bounds; a `while` with a potential; `conseq` side goals; an abstract adversary charged through a budget potential |
| `15_sampling.ec` | `rnd f g` / `rnd f` on intervals; `rnd{2}`; the five-argument phoare `seq` (which goals it leaves); `rnd P`; `DProd.ProdSampling` with `symmetry`; `rndsem*` (merge draws into one) |
| `16_program.ec` | `ecall` (also one-sided with phoare = 1); `while (true) (variant)`; `rcondt` / `rcondf` (also on a `while`); `sp n m` and `if{1}`; `proc*` + `rewrite equiv[{1} 1 E]` |

## Rules of thumb

- **exlim binds the value at the start of the remaining program** (the
  current precondition).  If the program changes the value before you need
  it, `seq` / `sp` to that point first.  `exlim e => v` = `exists* e; elim* => v`.
- **Calls are processed from the end.**  One-sided drops: last dropped call first.
- **An equiv can't relate a side to its own past.**  Fix the old value with
  exlim and add a hoare triple for that side with `conseq E H1 H2`.
- **`byequiv lemma` needs an exact match.**  Write the spec in `byequiv (: P ==> Q)`,
  then `conseq lemma`.  Games on the other sides: `symmetry` first.
- **Up-to-bad invariant must include the flag's equality** while not bad.
- **Pr = 1 facts become specs with `bypr`**: `bypr => &m <-; exact (h &m)`
  for phoare; for hoare go through `Pr[mu_not]` (see `04_pr.ec`, 4.).
- **A probability is a spec.**  `bypr; byequiv; proc true` turns
  `Pr[G.main(x0) @ &m : res]` into a phoare that a `call` can use: that is how
  a bound for every value becomes a bound for a random one, and a theorem
  about a random key, world or oracle gives one fixed value (`09_averaging.ec`).
- **A sample the run never reads: draw it after the run.**  `swap` it behind
  the call; then the chance that it lands in what the run outputs is the mass
  of that set (`08_late_sample.ec`).  Show first that the run really does not
  read it.
- **Symmetry is a coupling of the game with itself**: swap the samplings on
  one side so that the two hidden values cross (`07_rnd.ec`, 3.).
- **Same law, no bijection: `bypr (res{1}) (res{2})`**, then one `byphoare`
  per side (`10_laws.ec`, 2.).
- **Reason about a loop once.**  Prove its functional spec (hoare + lossless)
  and use it on each side of an equiv alone; the two programs need not run in
  step (`11_while.ec`, 3.).
- **A constant charge per call: `fel`.  A charge that depends on the state:
  an ehoare potential**, an invariant of every oracle call
  (`12_fel.ec`, `13_ehoare.ec`).
- **ehoare cannot use a hoare spec.**  Prove the ehoare for a reference
  program that computes the function, the equiv to it, and `conseq E H`
  (`13_ehoare.ec`, 3.).
- **Expected counts: ehoare + a budget.**  Keep the cost of the remaining
  oracle calls in the potential; each call spends its share
  (`14_ehoare_patterns.ec`, 7.).

## Pitfalls

- `forall` extends as far right as possible.  In an invariant write
  `/\ (forall y, P y) /\ Q`, with the parentheses, or `Q` ends up under the binder.
- `split` (and other tactic names) can't be lemma or hypothesis names.
- Inside a `Pr[...]` event written in a proof, `X{m}` for the memory bound by
  `bypr` is read as the current `X`.  Don't retype the event; rewrite with the
  hypothesis that already has it (`rewrite -h1 Pr[mu_sub]`).
- Program expressions can't mention `glob M`
  ("expressions cannot contain a glob statement").
- In a section, a `declare axiom` can't use a `local` predicate, and a
  non-local operator can't mention a declared module's `glob`.  Spell the
  predicate out in the axiom.
- `call (: I)` is for abstract procedures.  For a concrete one give
  `(: P ==> Q)`.
- `=> //` may close more goals than you expect; the next bullet then fails
  with "all goals are closed".  It also removes a `true` precondition: after
  `bypr (res{1}) (res{2}) => //` there is no hypothesis left to introduce.
- `ecall{1} (lemma (glob A){1})` crashes (`InvalidGoalShape`).  With
  ordinary program variables `ecall{1}` works (`ecall{1} (inc_ph P.x{1})`
  needs no `seq` / `exlim`), and so does naming the glob first:
  `exlim (glob A){1} => g; ecall{1} (lemma g)`.  Otherwise `seq` + `exlim` +
  `call{1}` does the same job.
- `*)` ends a comment wherever it is: `(* ... (exists* ... elim*) ... *)`
  closes at `elim*)`.
- `^^` on `bool` needs `require import Bool` (`AllCore` does not export it).
  `fel` needs `require import FelTactic`.
- A lemma parameter named like a program variable shadows it:
  `lemma l (x : int) : hoare[M.f : x = 3 ==> ...]` constrains the parameter,
  not the argument `x` of `M.f`.  Name parameters `x0`, `xx`.
- Once the section is closed, every lemma of it takes the declared modules and
  EVERY `declare axiom` declared before it, in order, used or not (`print` it).
  Declare an axiom after the lemmas that do not need it, or in its own section.
- `sp` runs through an `if` whose branches only assign, and the `if` that
  follows fails ("invalid first instruction").  Give it a count (`sp 1; if`).
  `sp` does not apply to ehoare goals at all: cut with `seq 1 : (inv)`.
- In ehoare, `wp` also goes through a sampling (it becomes an `Ep`).
- `fel` takes its oracles as the adversary calls them (`O.f`, not the
  procedure that `O.f` is an alias of).  An entry that names no oracle is
  silently ignored and that oracle gets the guard `true`.  Its goals come in
  the alphabetical order of the oracles' module names, not in the order of the
  list.
- In a rewrite chain `1:/#` is fine but `1:smt(lemma)` is a parse error.
  Prove the side fact first with `have`.
- `clone ... proof *` followed by `realize` lines: a missing `realize` is
  reported only by the next command, and at the very end of a file not at all
  (the file compiles).  End such a file with a lemma.
- `rename [module] "Atk" as "Coll"` renames every module whose name CONTAINS
  `Atk` (`AtkJ` becomes `CollJ`).
- EasyCrypt does not re-check a required file that has a fresh `.eco`.  Delete
  the `.eco` files, or check a clean copy, before trusting a build.
- Newer EasyCrypt (after r2026.07) wants the bound of a phoare or ehoare to be
  nonnegative, as extra goals of `rnd`, `bypr` (`0 <= Pr[...] /\ ...`),
  `byehoare` and `exfalso`.  Keep `have hb : 0%r <= bound` in the context so
  that `=> //` closes them; `08`, `09`, `12` and `13` work on both versions
  that way.
- ehoare: scale with `call /(fun v => p%xr * v)`.  `p ** v` with an `inv`
  in `p` (e.g. `(1%r/2%r) ** v`) never returns: `Xreal`'s simplification hints
  `of_realI` and `to_realK_simpl` undo the definition of `Rp.inv`, so any
  delta-reduction of `(inv x)%rp` loops (`simplify delta` there gives
  "Stack overflow").  Take `` `|` `` conditions out (`xle_cxr_r`) before
  simplifying an expectation, or the goal blows up.
- In a post, a procedure's arguments are out of scope: fix them with a
  lemma parameter (`x = x0` in the pre, `x0` in the post).

## Seeing the goals from the command line

`easycrypt llm` loads a file up to a line and prints the goals there.  In
release `r2026.10` the options are `-upto` and `-lastgoals`:

```sh
easycrypt llm -I <dirs> -upto 42 file.ec     # goals before line 42 (LINE:COL works)
easycrypt llm -I <dirs> -lastgoals file.ec   # goals at the first failure
```

Other builds also accept an interactive script with `-eval`:

```sh
easycrypt llm -I <dirs> -eval 'LOAD "file.ec" 42
QUIET ON
proc.
GOALS ALL'
```

- `LOAD` checks everything up to and including line 42, then waits for more
  input.  If the line is `proof. admit. qed.`, split it first, or you load
  past the proof.
- Each further line is one tactic (one sentence per line; two sentences on
  one line are rejected).  A statement spanning several lines cannot be
  sent: put it in the file and `LOAD` up to its `proof.` line.
- `GOALS` shows the focused goal, `GOALS ALL` all of them, `TREE ALL` the
  goal tree.  Errors print `ERROR` plus the offending `source:` line.
