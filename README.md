# EasyCrypt tricks

Small, self-contained examples; each file compiles on its own against the
standard library (checked with EasyCrypt release `r2026.10`).

`TACTICS.md` is a reference for the less common tactics and syntax (ehoare,
`rndsem`, `rnd f g`, the five-argument `seq`, `rcondt`, `rewrite equiv[...]`,
`case @[ambient]`, clone forms, ...): what each does, its syntax, and where
an example is.  Files 07-10 and most of `TACTICS.md` are drawn from the
Simon / Hsiao-Reyzin separation development (`simon/src`).

The same material with explanations is in `easycrypt-tricks.pdf`
(`latexmk -pdf easycrypt-tricks.tex` rebuilds it; the listings are read from
the `.ec` files).

```sh
for f in *.ec; do easycrypt compile "$f" || echo "FAILED: $f"; done
```

| File | What it shows |
|---|---|
| `01_conseq.ec` | applying a spec with weakening; `conseq (: _ ==> Q)` before `sim`; `conseq E H1 H2` (one-sided facts on an equiv); `(_: true ==> true)`; phoare = 1 from `conseq ll H`; conjoining hoare triples |
| `02_call.ec` | `call (: I)` for abstract adversaries; `proc I`; `call (: true)` for `{}` procedures and for oracle aliases (`proc*`); concrete calls need `(: P ==> Q)`; `call{1}` with a phoare spec; `call` with a hoare lemma |
| `03_exlim_seq.ec` | **when exlim binds what**, and how to cut with `seq` / `sp` first; relational exlim; `#pre`; `swap` |
| `04_pr.ec` | `Pr[mu_le1]`, `Pr[mu_sub]`, `Pr[mu_not]`, `Pr[mu_or]`, `Pr[mu_split E]`; Pr = 0 from hoare; phoare / hoare from Pr = 1 via `bypr`; `byequiv` with a lemma and `symmetry`; Pr arithmetic with `smt` |
| `05_upto_bad.ec` | `call (: B, I, J)`; every generated goal; `Pr1 <= Pr2 + Pr2[bad]`; equality from `Pr[bad] = 0` |
| `06_one_sided.ec` | dropping a discarded adversary run: phoare specs from `bypr` and `conseq ll H`, then `exlim` and `call{1}` backwards |
| `07_ehoare.ec` | **expectation Hoare logic**: `%xr`, `` `\|` ``, `rnd` + `Ep_dbool`, `byehoare`; "exact" specs for every potential `K`; `call /(fun v => ...)` to frame facts and scale bounds; a `while` with a potential; `conseq` side goals; an abstract adversary charged through a potential (`call (: pot)`) |
| `08_sampling.ec` | `rnd f g` / `rnd f` bijections; `rnd{2}` discarded draws; moving a draw past a call (late sampling); the five-argument phoare `seq`; `rnd P`; `DProd.ProdSampling` with `symmetry`; `rndsem*` |
| `09_program.ec` | `ecall` (also one-sided with phoare = 1); `while (true) (variant)` for losslessness; `rcondt` / `rcondf` (also on a `while`); `sp n m` and `if{1}`; `proc*` + `rewrite equiv[{1} 1 E]` |
| `10_averaging.ec` | a `Pr[...]` as a phoare step (`(glob G) = (glob G){m}`); averaging over a random parameter; `case @[ambient]`; `conseq (: _ ==> _ : = p)`; "some fixed value is no worse than the average" |

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
- **Expected counts: ehoare + a potential.**  Bound E[count] with an
  ehoare judgment, budget the remaining oracle calls in the potential, and
  read off `Pr[...]` with `byehoare` (`07_ehoare.ec`).
- **Independence = draw it later.**  Move a sample the run never reads
  behind the run (`swap`), then bound the event by the sample's mass
  (`08_sampling.ec`, 3.).

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
  with "all goals are closed".
- `ecall{1} (lemma e{1} ...)` crashed (`InvalidGoalShape`) in an earlier
  version; in `r2026.10` it works with a phoare = 1 spec (`09_program.ec`).
  `seq` + `exlim` + `call{1}` does the same job.
- ehoare: scale with `call /(fun v => p%xr * v)`; with `p ** v` the
  concavity check looped.  Take `` `|` `` conditions out (`xle_cxr_r`)
  before simplifying an expectation, or the goal blows up.
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
- Each further line is one tactic (one sentence per line).
- `GOALS` shows the focused goal, `GOALS ALL` all of them, `TREE ALL` the
  goal tree.  Errors print `ERROR` plus the offending `source:` line.
