# eink0rn

A Lean 4 proof checker in Haskell, written clean-room.

It reads a [`lean4export`](https://github.com/leanprover/lean4export) NDJSON file
and prints `ACCEPT` or `REJECT`. It does not run Lean, elaborate anything, or
produce a `.olean`; it reads an exported environment and says whether it holds
together.

```
$ eink0rn refs/tests/good/proof-irrel.ndjson
ACCEPT
$ eink0rn refs/tests/bad/extra-rec.ndjson
REJECT
False: the block's recursors are ["False.rec","rogue"], expected ["False.rec"]
```

The verdict goes to stdout and the reason, if there is one, to stderr. Exit
status is 0 for `ACCEPT` and 1 for `REJECT`; 2 says no verdict was reached
because a limit given on the command line was hit (`+RTS -M`, `+RTS -K`), and 3
that the checker faulted or could not read its arguments. Nothing else exits 1,
in particular: a crash is never reported as a rejection.

## What is different about it

**It normalises the surface language away before checking anything.** The export
format offers rather more than a type theory needs: binder annotations, metadata,
theorems, opaque definitions, nested inductive types, exported recursors with
their reduction rules. `Front.Export` and `Front.Lower` reduce all of that to a
core of five kinds of constant and eleven expression formers, and only then does
the kernel run. Nested inductives are compiled into flat mutual blocks, and every
mutual block is then flattened into a single indexed family (SPEC §9), so the
core sees neither a nested occurrence nor a mutual one — it is a theory of one
inductive type, and one recursor. Both compilations invent constants, and they
invent them in a namespace the export format has no syntax for (SPEC §9.4), so
"nothing the front end invented survives into the environment" is a test the
kernel can actually run rather than a naming convention. Recursors are not
believed — they are re-derived from the inductive specification and the exported
ones are required to match (SPEC §1, §8.7), so an export cannot smuggle in an
unwarranted large elimination or an extra iota rule. Nor are they believed once
derived: every reduction rule the kernel ends up with is typechecked against the
type its own left-hand side has (SPEC §8.9), which is what stands behind a rule
that both this kernel and the exporter might have got wrong the same way.

**It takes a mutual block whose types span universes.** Every other Lean kernel
requires them to end in the same sort. That rule is a commitment the elaborator
makes, not a theorem: a `Prop` member cuts the chain of inequalities that would
otherwise force a cycle of data members to share a level, and the `Prop` that
cuts it is the same one whose proof irrelevance collapses the injection a paradox
would need. So the block is accepted — but derived, not believed (SPEC §9.6): an
all-`Prop` shadow of the whole block, the data members declared separately in
topological order, and the block's recursors rebuilt over the two, with every
constructor type and every iota rule the file declares checked definitionally
against the derivation. `--enforce-mutual-univ` turns it off.

**It was written without looking at a Lean kernel.** The only references used
were Carneiro's *The Type Theory of Lean*, the NDJSON format specification, and
the accept/reject verdicts of the Lean Kernel Arena test corpus. Nothing was read
from `lean4`, `lean4lean`, `trepplein`, or any other implementation. Where
eink0rn diverges from official Lean, SPEC §12 says so and says why.

**Its type theory is written down.** [`SPEC.md`](SPEC.md) is the normative
description: every rule the kernel implements should be there, and nothing that
is not there should be implemented. It is meant to be read against the source.

## Building

Needs GHC 9.6 and cabal. No dependencies outside the GHC boot libraries (`base`,
`bytestring`, `containers`, `array`, `mtl`).

```
cabal build
cabal list-bin eink0rn
```

## Options

Everything defaults to the strictest setting that does not reject a faithful
export.

| flag | default | effect |
| --- | --- | --- |
| `--nat-accel=off\|canonical\|verified\|always` | `canonical` | how much evidence the arithmetic shortcuts of SPEC §6.5 demand before a `Nat` operation is computed on a bignum instead of unfolded. `always` trusts the *name* and is unsound; it exists to reproduce the behaviour of kernels that do that. |
| `--pin-std=off\|warn\|error` | `off` | audit `False`, `Eq`, `Iff`, `Nonempty`, the quotient package and the three standard axioms against their standard forms (SPEC §12.5). |
| `--keep-proofs` | off | retain every proof term instead of sealing it (SPEC §12.10). By default a checked `theorem` becomes an axiom of its own statement, which is where two thirds of `mathlib`'s peak went; the one case in any corpus that needs the proof back is named there. |
| `--enforce-mutual-univ` | off | reject a mutual inductive block whose types do not all end in the same sort, as every other Lean kernel does. By default such a block is derived from simpler declarations and accepted if the derivation checks out (SPEC §9.6, §12.14). |
| `--progress[=SECS]` | off | report on stderr as the file is checked, naming each declaration that took at least `SECS` seconds. |
| `-jN` | off | check in two passes, the second on `N` threads (bare `-j`: one per core). Pass one only reads each declaration into the environment, taking its statement on trust; pass two makes both judgements about it, which is where all but a few per cent of the time goes and which nothing else depends on. Each obligation is started as pass one files it, and the file is read on a thread of its own alongside. Same verdict either way — SPEC §11.6 says why. On the three smaller corpora pass one costs no more than reading the file: `std` in 9.5s rather than 133s. |

## Tests

The arena corpus lives in `refs/tests/` (extracted from `refs/tests.tar.gz`),
laid out as `good/*.ndjson`, `bad/*.ndjson` and `either/*.ndjson` — the last for
the cases the arena itself scores `outcome: either`, where a verdict is demanded
but not a particular one:

```
bash tools/run-tests.sh                 # 193/193
bash tools/run-tests.sh tests           # 16/16, hand-written
bash tools/run-tests.sh validation      # the validation corpus below
```

`tests/` is the hand-written corpus: cases for shapes `lean4export` cannot
produce, so no exporter will ever hand one over. Most of it is the
heterogeneous-universe blocks of SPEC §9.6, written by `tools/mkhetero.py`.

`validation/` is a separate corpus of pathological cases built by a subagent that
*was* allowed to read Lean's source and issue tracker, as an adversarial check on
a kernel that was not. 827 of its 846 labelled cases get the label's verdict; the
other 19 are divergences SPEC §12 records and defends — eight on the arithmetic
licence (§12.6), five mutual blocks whose types span universes (§12.14), three
universe-polymorphic inductives whose fields satisfy the universe condition under
every assignment (§12.2), two nested occurrences at a fixed index (§12.12), and
one quotient package spelled under other names (§12.3, which `--pin-std`
catches). With `--enforce-mutual-univ` the count is 832, as it was before §9.6.

`validation/disputed/` holds 35 further cases where eink0rn and official Lean are
expected to disagree and eink0rn is not obviously wrong. It accepts 22 and
rejects 13, and every one falls into a family SPEC §12 already argues: level
identities the complete `≤` decides (§12.2), files that redefine `Nat.add` and
then assert the standard fact about it (§12.6, in both directions), the line
schema (§12.8), and `Acc.rec` on a proof variable (§12.13).

### The Lean Kernel Arena exports

All four, through the resource half of the run line the arena entry uses —
`--mem=4000 -j8 +RTS -A32m -M13g`; the entry also passes
`--enforce-mutual-univ`, which no export gives anything to do — on a GCP `n2`
instance with 64 cores and other work on it. The memory column is the largest of
three or four runs and does not care what else the box is doing; the `-j8` clock
is the *best* of the same runs, because the box was carrying load averages
between 20 and 110 throughout and a loaded run only ever reads slow.

| corpus | declarations | verdict | `-j8` | anonymous | mapped file | `-j1` |
| --- | --- | --- | --- | --- | --- | --- |
| `init.ndjson` (325 MB) | 53,093 | ACCEPT | 19s | 0.76 GB | 0.33 GB | 1m 12s |
| `std.ndjson` (552 MB) | 90,778 | ACCEPT | 35s | 1.83 GB | 0.56 GB | 2m 15s |
| `cslib.ndjson` (2.1 GB) | 370,939 | ACCEPT | 2m 25s | 3.80 GB | 2.15 GB | 16m 03s |
| `mathlib.ndjson` (5.6 GB) | 654,504 | ACCEPT | 8m 07s | 8.61 GB | 5.64 GB | 55m 22s |

Two memory columns because only one of them is a requirement. The export is
mapped rather than read, so its pages are clean and file-backed: resident on a
machine with room, and handed straight back on one without. What has to fit is
the anonymous column. The last column is the same check on one thread with the
compiled-in defaults instead of the flags above, for scale — and only for scale:
it is one run each, taken while the box was busiest, and with no ceiling on it
the same `mathlib` run wants 7.01 GB.

Three of those four are read-bound at `-j8` and their clocks have not moved in a
long time. `mathlib` is the one that is not, and it is where sealing proof bodies
(SPEC §12.10) landed: that row read 11m 37s and 12.87 GB before it, and 19.0 GB
in the `-j1` column.

Nothing is near the ceiling any more, but the run line still names one rather
than a collection ratio, and that is deliberate. An earlier
version of this run line added `-F1.3`, which holds the heap to 1.3 times the
live set everywhere; repeated interleaved runs put that at 26% of `mathlib`'s
wall clock for a peak indistinguishable from the default's, because near `-M`
the collector reins the ratio in by itself and below `-M` there was never
anything to rein in. The three smaller exports pay for the ceiling in memory
they have to spare rather than in time.

That memory came at a price in time, and the price is worth stating. Measured
alternately against the commit before it, arms interleaved so that whatever the
box was doing it did to both, one thread went 72.8s to 85.6s on `init`, 143.6s
to 162.4s on `std` and 524.3s to 656.8s on `cslib` — 18%, 13%, 25%. Three
quarters of that is mapping the file rather than reading it, which the same
comparison isolates: with the eviction machinery disabled and only the mapping
left, `init` is already at 83.0s. Reading a mapped file costs a page fault per
page and the parser touches every one of them. The other quarter is
`Front.Scan`'s extra pass and the per-line bookkeeping `Front.Pool` does to know
when an index is finished with.

What it buys is the last row of the table: `mathlib` used to want 25 GB and now
wants 8.6, which on a 16 GB runner is the difference between a verdict and
none. Two later passes did the rest — the checker's own representations (SPEC
§11.8) took 17.6% off the live set, and sealing proof bodies (§12.10) took
two thirds of what was left — and both show in the `-j1` column more plainly
than in the `-j8` one, since under `-M13g` the anonymous column is partly the
ceiling talking rather than the heap.

One mathlib theorem —
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_isAffine`
— used to account for 4m 27s of the single-threaded figure on its own, against
1m 01s for the next slowest and 20 seconds for all but five declarations in the
export. It was also the memory spike described below, which lasted four minutes
and came at the very end, exactly where a declaration that much slower than the
rest would still be running once everything else was done. Both were the same
thing: what it spent that time on was unfolding the proofs its statement
mentions. Since §12.10 sealed those, a `--progress=20` run over the whole export
on one thread names **no declaration at all**.

### Submitting to the arena

`tools/arena-checker.yaml` is the entry for
[`leanprover/lean-kernel-arena`](https://github.com/leanprover/lean-kernel-arena),
kept here so the recipe travels with the thing it builds; submitting is copying
it to that repository's `checkers/eink0rn.yaml` and bumping `rev`. The two
commands in it are:

```
bash tools/arena-build.sh                                          # build:
./arena/eink0rn --enforce-mutual-univ --mem=4000 -j8 "$IN" \       # run:
  +RTS -A32m -M13g -RTS
```

`tools/arena-build.sh` is one `ghc --make` — there is no package index to fetch
and nothing to resolve, because the checker depends on the GHC boot libraries
and nothing else. It tries every GHC it can find in turn and installs 9.6.6 with
ghcup if none of them can build it, which is the case that matters: the arena
builds each checker on an 8-vCPU, 16 GB `nscloud-ubuntu-22.04` runner inside a
nix shell that provides elan, cargo, node, ocaml and zig, but no Haskell. Cold
— clone, ghcup, the compiler, and the sixteen modules — that path takes 2m 55s
and 2.6 GB of disk; against a GHC already on the machine, 43s.

`--enforce-mutual-univ` is the one flag in the line that is not about resources.
It turns off the only place where this kernel accepts a file official Lean
refuses — a mutual inductive block whose types do not all end in the same sort,
§9.6 — so that what the arena scores is the language every other checker is
being scored on. It is a setting rather than a repair: with it off the block is
derived from admissible declarations and checked definitionally, not waved
through. `lean4export` emits no such block, so it changes no verdict on any of
the four exports. The other divergences of §12 get no such switch here:
`--nat-accel=always` would match official Lean's name-keyed arithmetic but is
unsound on purpose and exists for differential testing, `--pin-std` is an extra
audit that can only reject more than official Lean rather than less, and
`--keep-proofs` would close one false-reject — `subject-reduction-redex`, which
the arena scores `either` anyway — at the cost of keeping every `mathlib` proof
body, which is most of what this run line exists to fit.

The rest of the run line is all about that 16 GB, and all about `mathlib`. `-M`
is a limit rather than a wish: over it the checker prints `DECLINE` and exits 2
instead of taking the runner down with it, which is a resource limit reported as
one rather than as a wrong verdict or a crash. But it is also the flag that
keeps the run under the limit in the first place, and that is why the run line
names a ceiling and not a ratio. Above 30% of `-M` the RTS collects the oldest
generation in place instead of copying it, and as the heap approaches `-M` it
reins in how far ahead of the live set the heap is allowed to run before that
generation is collected. So the squeeze applies itself where it is needed and
nowhere else. It used to be worth eight gigabytes on `mathlib` — 12.8 GB under
`-M13g` against 21.1 with the limit raised out of reach — and since SPEC §11.8 it
was worth the spread instead: three runs with the limit out of reach peaked at
12.5, 13.0 and 15.1 GB against 12.9 or below under `-M13g`, in the same time to
within a per cent. Since §12.10 it is worth nothing at all: interleaved,
`-M13g` peaks at 8.53 and 8.06 GB and `-M30g` at 8.44 and 8.61, in the same time
again. It stays because what it bounds is the run that goes wrong — over the
limit the checker says `DECLINE` and exits, which is a resource limit reported as
one. `init`, `std` and `cslib` never came near it and are collected at the fast
default throughout, and `mathlib` no longer does either. `--mem=4000` is the checker's
own budget, below. `-Mgrace=256m` is built into the binary, so it applies
whenever `-M` does: it is the room the overflow handler needs in order to speak,
the default 1M being gone before the exception is even delivered when eight
threads are allocating.

Its own two limits are the reason the entry rewrites two exit statuses to 2.
One is the `timeout`. The other is 251, which is the RTS exiting on the heap
limit by itself, and it happens when the live set grows past `-M` by more than
the grace in the gap between two collections — a heap that outgrows the limit
between one collection and the next can commit to an allocation it has no room
to finish. Both are `-M` and the clock doing their job, and neither is a
judgement about the file.

Nothing is declined, and the table above is that run line.

`mathlib` is the whole reason the flags are the flags, and its difficulty is one
declaration. A heap census (SPEC §11.8) showed the live set flat under 3 GB for
three quarters of an hour and then more than tripling to 9.6 GB in the last few
minutes before collapsing back — and doing exactly the same thing, to within six
per cent of the same height, on one thread. So it was not eight obligations
landing at once and no amount of throttling was going to get under it; it was
one theorem's memo tables, and those tables were full of the reduced forms of
proofs. Sealing them (§12.10) takes that peak to 3.1–3.4 GB. `--mem` is a budget
on the live set that halves how many threads may work when a major collection
finds more than that alive and gives a thread back when one finds comfortably
less, which is what kept the other seven from piling on top of that declaration.
It is now barely reached on `mathlib` either.

## Layout

```
SPEC.md              the type theory, normatively
src/Kernel/Name      names, and the hash they are looked up by
src/Kernel/Level     universe levels, and the decision procedure for <=
src/Kernel/Expr      terms: de Bruijn bound variables, named free variables
src/Kernel/Env       the environment: five kinds of constant
src/Kernel/Cache     the mutable hash table the memo tables are made of
src/Kernel/Canon     stored canonical forms, for the arithmetic licence and --pin-std
src/Kernel/Check     inference, reduction, and definitional equality
src/Kernel/Inductive admitting one inductive family, and deriving its recursor
src/Front/Json       a JSON reader, streaming, for files larger than memory
src/Front/Mmap       the export as file-backed pages rather than as heap
src/Front/Scan       one cheap pass to find where each pool index dies
src/Front/Pool       the pools themselves, dropping entries at that point
src/Front/Export     the NDJSON line schema and the declarations it builds
src/Front/Lower      surface to core: the nesting compilation, and the flattening
src/Front/Hetero     deriving a mutual block whose types span universes
app/Main.hs          the command line
```

## License

Apache 2.0, the same license Lean and Mathlib use. See [`LICENSE`](LICENSE).

Two directories are not original to this repository and are redistributed under
their own terms: `refs/tests/` is the Lean Kernel Arena corpus, and
`refs/format_ndjson.md` is `leanprover/lean4export`'s format specification.

## References

`refs/lean-type-theory/` is Carneiro's thesis, cloned separately and not
committed:

```
git clone https://github.com/digama0/lean-type-theory refs/lean-type-theory
```

`refs/format_ndjson.md` is the export format specification, from
`leanprover/lean4export`.
