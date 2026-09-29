# EasyCrypt tricks

Small, self-contained examples; each file compiles on its own against the
standard library.

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
- `ecall{1} (lemma e{1} ...)` crashed (`InvalidGoalShape`) in the version
  used here; `seq` + `exlim` + `call{1}` does the same job.

## Seeing the goals from the command line

`easycrypt llm` loads a file up to a line and prints the goals there:

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
