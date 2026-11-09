# Less common EasyCrypt tactics and syntax

A reference for tactics and forms that the usual tutorials skip, with what
they do, their syntax, and a pointer to a runnable example in this
directory.  Most of them come from the Simon / Hsiao-Reyzin separation
development (`simon/src`), where they carry real proofs; file names given
in parentheses (`Simon.ec`, `SwapCore.ec`, ...) are from there.  Everything
below was checked against EasyCrypt **r2026.10**; the behaviours marked
*observed* were found by running the examples, not taken from the manual.

Conventions: `{i}` is a side (`{1}` or `{2}`) in a relational goal; `n`, `m`
are instruction positions (1-based; `0` means "before the first").

---

## Expectation Hoare logic (`ehoare`)

The logic for **expected values**, from `theories/datatypes/Xreal.ec`.
Example: `07_ehoare.ec`.

### The judgment

```
ehoare [ M.f : pre ==> post ]
```

`pre` and `post` are of type `xreal` (non-negative reals extended with
`oo`).  Meaning: from every initial memory, the expectation of `post` over
the final memories is at most `pre`.  Think of `post` as a *potential* that
`pre` pays for.  A non-terminating run contributes nothing to the
expectation, so only upper bounds make sense.

| Notation | Meaning |
|---|---|
| `x%xr` | an `int`, `real` or `bool` as an `xreal` (bools: 0 / 1; negative reals: 0) |
| `b `\|` x` | `x` if `b`, otherwise `oo`.  In a **pre**, a boolean assumption (an `oo` pre is trivially satisfied) |
| `Ep d f` | expectation of `f : 'a -> xreal` under `d` |
| `c ** x` | scalar multiple (`c : real`) |
| `oo` | infinity |

### Useful lemmas

| Lemma | Statement |
|---|---|
| `xle_cxr_r` | `(b => x <= y) => x <= (b `\|` y)` — assume the fact in the pre |
| `xle_cxr_l` | `b => x <= y => (b `\|` x) <= y` — discharge it in a post |
| `xle_cxr` | both sides carry a condition |
| `xle_rle` | `0%r <= x <= y => x%xr <= y%xr` — back to real arithmetic |
| `xlexx`, `xle_trans` | reflexivity, transitivity |
| `Ep_mu` | `Ep d (fun x => (p x)%xr) = (mu d p)%xr` — expectation of an indicator |
| `EpC` | `Ep d (fun _ => c) = weight d ** c` |
| `EpD`, `EpZ` | linearity |
| `Ep_dbool`, `Ep_duniform`, `Ep_dinterval`, `Ep_dmap`, `Ep_dlet` | for specific laws |
| `of_realD`, `of_realM` | `(x + y)%xr = x%xr + y%xr` etc., under non-negativity |
| `to_pos_pos` | `0%r <= x => x%pos = x` (shows up after `rnd`) |

### Tactics in ehoare

* **`proc; wp; skip => &hr /=`** — the goal becomes the xreal inequality
  `post' <= pre`.  Typical closing: `apply xle_cxr_r => /> ...; smt(xlexx)`.
* **`rnd`** — turns `post` into `Ep d (fun x => post[x])`.  Follow with
  `Ep_mu` or a law-specific `Ep_*` lemma.
* **`call H`** — as in hoare, with `H : ehoare [...]`.
* **`call /(fun v => F v) H`** — *call with a transformer*: from
  `ehoare [f : P ==> Q]` use `ehoare [f : F P ==> F Q]`.  `F` must be
  concave and increasing (side goal, often automatic).  The two transformers
  that matter:
  * `(fun v => (A) `|` v)` — **frame** a boolean fact `A` about variables
    the call does not write (Simon.ec: `call /(fun v => (c=c0 /\ m=m0) `|` v) (evaluate_expectation ...)`);
  * `(fun v => p%xr * v)` — **scale** the bound (LateSample.ec:
    `call /(fun x => p1%xr * x) hS`).  *Observed:* write the scaling as an
    xreal product `p%xr * v`; with `p ** v` the concavity check made
    EasyCrypt loop.
* **`while (I)`** — `I` is an xreal potential, usually
  `(side facts) `|` potential`.  Goals: exit
  (`forall &hr, post <= (!cond) `|` I`), body
  (`ehoare [body : cond `|` I ==> I]`), then the code before the loop pays
  for `I`.  To call a procedure inside the body, `exlim` the loop
  variables and frame them with the transformer, adding the budget of the
  remaining iterations: `call /(fun v => (i = i0 /\ ...) `|` (v + rest%xr)) H`
  (`07_ehoare.ec`, `run_e`).
* **`call (: I)`** on an **abstract adversary** — `I` is a potential that
  every oracle procedure preserves in expectation.  The standard trick
  (SwapCore.ec: `recording_potential`): budget the remaining queries in the
  potential, e.g. `(0 <= n <= q) `|` (hits + (q - n) * p)%xr`, so that each
  query spends `p` of the budget and pays for the expected new hits.
* **`seq n : (Q)`** — `Q` is an xreal intermediate potential.
* **`exlim x => x0`** — as usual; combine with the framing transformer to
  remember the value across a call.
* **`conseq (: _ ==> Q)`** — weakening.  *Observed:* the side goals
  quantify over the variables the program writes, inside a `|`, e.g.
  `(forall hits, (1 <= hits)%xr <= hits%xr) `|` pre <= pre`; close the first
  with `apply xle_cxr_l` and the second with `apply xle_cxr_r => h; exact (h M.hits{hr})`.
* **`conseq E H`** with an equiv `E` and `H : ehoare` transports an ehoare
  across an equivalence (HRSwap.ec: `conseq fresh_procedure_exact freshSpec_charge`).

### Working with the xreal goals (observed)

* **Take conditions out before simplifying.**  On
  `Ep d (fun x => (b) `|` f x) <= (b) `|` g`, do `apply xle_cxr_r => h; rewrite h /=`
  first, *then* `rewrite Ep_dbool /=`; in the other order the goal grew
  until `apply` hung.
* `/=` merges nested conditions (`cxrA` is a `hint simplify`) but not
  always: after `wp; skip` the pre can stay `(c) `|` ((I) `|` f)`.  Peel the
  outer condition with `apply xle_cxr_r => /> *`, then relate the inner ones
  with `apply xle_cxr => /> *`.
* After the conditions are gone, `/=` usually turns `x%xr <= y%xr` into
  `x%pos <= y%pos` on reals: `smt(to_pos_pos)` or `rewrite !to_pos_pos`.
* A sum of `%xr` terms against a `%xr` of a sum: `rewrite of_realD; smt()`.

### From ehoare to probabilities

```
byehoare (: pre ==> post) => //; last by smt().
```

proves `Pr[M.f(args) @ &m : E] <= p` when `pre` evaluates to `p%xr` in `&m`
and `post` dominates the indicator `E%xr`.  *Observed:* one side goal,
`0%r <= p`, is not closed by `=> //`.  Typical uses: a union bound over
a list whose *expected* length is bounded (LateSample.ec: `early_mem`), and
Markov-style bounds.

### Pattern: "exact" specs for every potential

For a deterministic procedure, prove

```
lemma f_K (K : out -> xreal) : ehoare [M.f : K (spec args) ==> K res].
```

once; it says as much as a functional hoare spec and plugs into any later
ehoare proof by instantiating `K` (Simon.ec: `evaluate_expectation`,
`find_partner_expectation`, `collect_bad_points_expectation`).

---

## Sampling

Examples: `08_sampling.ec`.

| Tactic | What it does |
|---|---|
| `rnd f g` | couple `x{1} <$ d1` and `x{2} <$ d2` through the bijection `x{2} = f x{1}`, inverse `g`.  Side goals: `f (g y) = y`, `mu1 d2 y = mu1 d1 (g y)`, and `f x \in d2 /\ g (f x) = x` on supports |
| `rnd f` | same, `f` an involution |
| `rnd{i}` | a draw on one side only; needs the law lossless |
| `rnd P` (phoare) | the probability of the drawn value satisfying `P` |
| `rnd : 0 0` | rnd by semantics (the form the standard library uses to prove `DProd.sample_sample2`) |
| `rndsem{i} n` | **merge** the block of draws and assignments after position `n` into one draw from the composed law.  *Observed:* `a <$ d1; b <$ d2; c <- (a, b)` becomes `(a, b, c) <$ dlet d1 (fun a => dmap d2 (fun b => (a, b, (a, b))))` |
| `rndsem*{i} n` | the same, keeping only the variables used later: `c <$ dlet d1 (fun a => dmap d2 (fun b => (a, b)))`.  Follow with `rnd`, or `rnd (fun p => p) (fun p => p)` when the laws are equal but not syntactically (side goal: equal `mu1`, e.g. by `dprod_dlet`) |
| `swap{i} n k` | move instruction `n` by `k` positions (negative: up).  `swap{i} [n..m] k` moves a block |

* **Moving a draw past a call** (`swap{1} 1 1; rnd; call (: true)`): the
  key step of "the sample is independent of the view".  Draw it *after*
  the run; then any event "x in S(view)" has probability `<= mu d S(view)`
  (LateSample.ec).
* **`DProd.ProdSampling`**: `S.sample` (one draw from `d1 `*` d2`) ~
  `S.sample2` (two draws).  For the reverse direction:
  `symmetry; conseq PS.sample_sample2 => /#`.
* **`DProd.DLetSampling`**: dependent draws `t <$ dt; u <$ du t` vs.
  `dlet`.

### Five-argument `seq` for phoare

```
seq n : (R) p1 p2 p3 p4 (I).
```

Splits `phoare [c1; c2 : pre ==> post] ~ b` at `n`:

1. `hoare [c1 : pre ==> I]` (`I = true` when omitted; the goal is still there);
2. `phoare [c1 : pre ==> R] = p1`;
3. `phoare [c2 : R /\ I ==> post] = p2`;
4. `phoare [c1 : pre ==> !R] = p3` — *observed:* omitted when `p4` is `0%r`;
5. `phoare [c2 : !R /\ I ==> post] = p4`;
6. `p1 * p2 + p3 * p4` compared to `b` (as `forall _, pre => ...`).

Give `1%r` / `0%r` for parts you don't need; a `0%r` goal is a hoare goal
in disguise (`hoare; ...`).  A `_` leaves the probability to be inferred.
`=> //` after the `seq` closes the trivial ones.  (LateSample.ec:
`seq 1 : (I v) 1%r p 0%r 1%r`, Averaging.ec, HRRefusal.ec.)

---

## Program transformations

Examples: `09_program.ec`.

| Tactic | What it does |
|---|---|
| `ecall (H args)` | `call` with a spec whose pre fixes arguments: `args` may be program expressions (`ecall (double_spec y)`); the pre is discharged by substitution.  `ecall{i}` in equivs, with a phoare `= 1%r` spec |
| `rcondt{i} n` / `rcondf{i} n` | the `if`/`while` at line `n` takes the true/false branch; side goal: a hoare triple on the prefix proving the condition.  In an equiv it reads `forall &m, hoare [prefix : pre (other side read in &m) ==> cond]`, so `first by auto => /#`.  On a `while`, `rcondt` unrolls one iteration |
| `while (I) (v)` | termination: `v : int` decreases each iteration; with `I = true` the standard islossless proof (`while (true) (n - i)`, `while (true) (size rest)`) |
| `sp n m` | symbolic execution of `n` / `m` leading assignments (left / right) |
| `if{i}` | case only on one side's `if` |
| `proc*` | open a procedure as a single call statement `r <@ M.f(args)`, so that call-level rewriting applies |
| `rewrite equiv[{i} n E]` | replace the call at line `n` of side `i` by the other program of the equiv `E` (program rewriting) |
| `proc true` | `proc I` for abstract procedures with the trivial invariant |
| `inline {i} M.f` / `inline *` | inline specific procedures / everything |
| `seq n m : (R)` | relational cut after `n` left / `m` right instructions |

---

## Probabilities and the ambient logic

Examples: `04_pr.ec`, `10_averaging.ec`.

| Form | What it does |
|---|---|
| `bypr => &m0 h` | phoare / equality of `Pr`: reason about `Pr[... @ &m0 : ...]` for every memory satisfying the pre.  On `phoare [...] = p` it also asks `0%r <= p` (`split => [\|[-> h]]; first smt(mu_bounded)`) |
| `byphoare (: P ==> Q) => //` | `Pr[...]` from a phoare; with `(glob G) = (glob G){m}` in `P` to remember the starting memory |
| `byphoare ... ; hoare` | `Pr[...] = 0` from a hoare triple |
| `conseq (: _ ==> _ : = p)` | change the bound of a phoare goal; side goal compares bounds |
| `case @[ambient]: (e)` | case on `e` **in the ambient logic** inside a program goal: each branch gets `e` / `!e` as a hypothesis (instead of as a pre conjunct).  Typical after `exlim x => xx` |
| `Pr[mu_split E]`, `Pr[mu_eq]`, `Pr[mu_sub]`, `Pr[mu_false]` | rewriting `Pr` terms (`rewrite Pr[mu_split (x \in s)]`) |
| `game_ph` pattern | `phoare [G.main : arg = x0 /\ (glob G) = (glob G){m} ==> res] = Pr[G.main(x0) @ &m : res]` — reuse a `Pr` as a step of a bigger program (Averaging.ec) |

### Lazy vs eager random oracles (`PROM`)

`clone PROM.FullRO as RO with type in_t <- ..., type out_t <- ..., op dout <- ...`
gives the lazy `RO` and `FullRO`; `clone RO.FinEager as E with op FinFrom.enum <- ...`
(finite domain) gives `E.FinRO` and `E.FunRO` (one function drawn up front)
and the probability equalities `E.pr_RO_FinRO_D` and `E.pr_FinRO_FunRO_D`
for a distinguisher.  SimonFixed.ec turns the finder's lazily drawn coins
into a function this way, then draws (table, function) as one parameter and
averages over it (`10_averaging.ec`).

---

## Theories and declarations

| Form | What it does |
|---|---|
| `op q : { int \| 0 <= q } as ge0_q.` | an abstract constant with an axiom `ge0_q : 0 <= q`, in one line |
| `clone T as U with type t <- int, op d <- ... proof *.` | instantiate; `proof *` turns all of `T`'s axioms into obligations, discharged afterwards with `realize ax. proof. ... qed.` |
| `clone include T with ...` | copy `T` into the current theory (inheritance between abstract theories; the Simon development chains them) |
| `clone ... with theory FinT <- PtFin` | instantiate a whole sub-theory |
| `realize ax by ...` / `... proof ax by tac` (in the clone) | discharge a cloned axiom |
| `declare module A <: T {-M1, -M2}` | an adversary that may not touch `M1`, `M2` |
| `declare axiom H : equiv[...]` | a section hypothesis on a declared module's code (used to state the code of machines as hypotheses) |
| `local module`, `local lemma` | internal games and steps, invisible after the section |
| `hint simplify L` | add `L` to `/=` (Xreal: `cxr_true`, `cxrA`) |

---

## Rewriting and intro-pattern odds and ends

| Form | What it does |
|---|---|
| `rewrite L 1:/#` | rewrite, and close the 1st side condition with `smt()` |
| `rewrite (_ : a = b) 1:/#` | rewrite with an on-the-spot equation |
| `rewrite -{1}(head_behead s witness hne)` | rewrite only the first occurrence |
| `rewrite !L` | rewrite as long as possible |
| `have /= [x [h1 h2]] := L args` | apply, simplify, destruct |
| `move=> /witness_support [x [hx hnB]]` | view: apply a lemma to the top hypothesis |
| `=> -[h1 h2]` | destruct a conjunction during intro |
| `first 2 by smt()` / `last first` | apply to the first two goals / move the last goal first |
| `[tac1 \| tac2]` | one tactic per generated goal |
| `exfalso` | goal becomes `false` |
| `pose x := e` | name an expression (also in program goals) |
| `exlim e1, e2 => v1 v2` | several exlims at once |
