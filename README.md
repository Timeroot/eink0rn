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
the kernel run. Nested inductives are compiled into flat mutual blocks (SPEC §9),
so the positivity checker never sees a nested occurrence. Recursors are not
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
a kernel that was not. `validation/disputed/` holds the cases where eink0rn and
official Lean disagree and eink0rn is not obviously wrong; SPEC §12.6 discusses
the arithmetic ones.

### The Lean Kernel Arena exports

| corpus | declarations | verdict |
| --- | --- | --- |
| `init.ndjson` (325 MB) | 53,093 | ACCEPT |
| `std.ndjson` (552 MB) | 90,778 | ACCEPT |
| `cslib.ndjson` (2.1 GB) | 370,939 | ACCEPT |
| `mathlib.ndjson` (5.6 GB) | | |

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
src/Kernel/Inductive admitting an inductive block, and deriving its recursor
src/Front/Json       a JSON reader, streaming, for files larger than memory
src/Front/Export     the NDJSON pools and the declaration schema
src/Front/Lower      surface to core, including the nesting compilation
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
