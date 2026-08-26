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
status is 0 for `ACCEPT`, 1 for `REJECT`, 2 for a bad command line.

## What is different about it

**It normalises the surface language away before checking anything.** The export
format offers rather more than a type theory needs: binder annotations, metadata,
theorems, opaque definitions, nested inductive types, exported recursors with
their reduction rules. `Front.Export` and `Front.Lower` reduce all of that to a
core of five kinds of constant and eleven expression formers, and only then does
the kernel run. Nested inductives are compiled into flat mutual blocks, and every
mutual block is then flattened into a single indexed family (SPEC §9), so the
core sees neither a nested occurrence nor a mutual one — it is a theory of one
inductive type, and one recursor. Recursors are not
believed — they are re-derived from the inductive specification and the exported
ones are required to match (SPEC §1, §8.7), so an export cannot smuggle in an
unwarranted large elimination or an extra iota rule.

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
| `--keep-proofs` | off | retain every proof term instead of sealing it (SPEC §12.10). A pure performance switch. |
| `--progress[=SECS]` | off | report on stderr as the file is checked, naming each declaration that took at least `SECS` seconds. |

## Tests

The arena corpus lives in `refs/tests/` (extracted from `refs/tests.tar.gz`),
laid out as `good/*.ndjson` and `bad/*.ndjson`:

```
bash tools/run-tests.sh                 # 186/186
bash tools/run-tests.sh validation      # the validation corpus below
```

`validation/` is a separate corpus of pathological cases built by a subagent that
*was* allowed to read Lean's source and issue tracker, as an adversarial check on
a kernel that was not. 832 of its 846 labelled cases get the label's verdict; the
other 14 are divergences SPEC §12 records and defends — eight on the arithmetic
licence (§12.6), three universe-polymorphic inductives whose fields satisfy the
universe condition under every assignment (§12.2), two nested occurrences at a
fixed index (§12.12), and one quotient package spelled under other names (§12.3,
which `--pin-std` catches).

`validation/disputed/` holds 35 further cases where eink0rn and official Lean are
expected to disagree and eink0rn is not obviously wrong. It accepts 22 and
rejects 13, and every one falls into a family SPEC §12 already argues: level
identities the complete `≤` decides (§12.2), files that redefine `Nat.add` and
then assert the standard fact about it (§12.6, in both directions), the line
schema (§12.8), and `Acc.rec` on a proof variable (§12.13).

### The Lean Kernel Arena exports

Whole-run wall clock and peak RSS, on one core of a GCP `n2` instance. The file
is parsed strictly before checking starts, which is most of the memory.

| corpus | declarations | verdict | time | peak RSS |
| --- | --- | --- | --- | --- |
| `init.ndjson` (325 MB) | 53,093 | ACCEPT | 3m 29s | 1.6 GB |
| `std.ndjson` (552 MB) | 90,778 | ACCEPT | 6m 0s | 3.3 GB |
| `cslib.ndjson` (2.1 GB) | 370,939 | ACCEPT | 22m 32s | 9.6 GB |
| `mathlib.ndjson` (5.6 GB) | 654,504 | ACCEPT | 2h 16m | 25 GB |

One mathlib theorem —
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_isAffine`
— accounts for 11 minutes of that on its own. The next slowest takes 48 seconds,
and only six declarations in the whole export take longer than 20.

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
src/Front/Export     the NDJSON pools and the declaration schema
src/Front/Lower      surface to core: the nesting compilation, and the flattening
app/Main.hs          the command line
```

## References

`refs/lean-type-theory/` is Carneiro's thesis, cloned separately and not
committed:

```
git clone https://github.com/digama0/lean-type-theory refs/lean-type-theory
```

`refs/format_ndjson.md` is the export format specification, from
`leanprover/lean4export`.
