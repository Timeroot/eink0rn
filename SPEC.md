# The eink0rn core theory

This is the normative description of what `eink0rn` accepts. It is written to be
audited: every rule the kernel implements should appear here, and nothing that
does not appear here should be implemented. Where the code and this document
disagree, that is a bug in one of them, and finding out which is the point of
writing it down.

**Provenance.** The theory is Carneiro, *The Type Theory of Lean* (`refs/`),
specialised to the fragment the `lean4export` NDJSON format can express. No
existing kernel implementation was consulted. Section references below are to
the thesis. Where a rule is *not* in the thesis — because it is an artefact of
the export format, or an efficiency device, or a place where the thesis leaves a
choice open — this document says so explicitly and gives the justification.

**Reading order.** §1 says what the front end throws away before the core sees
anything. §2–§4 give the syntax and the level algebra. §5–§7 give the
judgements. §8 gives inductive types, which is where the interesting content is.
§9 gives the nesting compilation, §10 quotients. §11 states the implementation
invariants the rules quietly depend on, and §12 lists the deliberate divergences
from what official Lean would do.

---

## 1. Surface to core

`eink0rn` consumes `lean4export` NDJSON v3.1.0. The file is a sequence of pool
entries (`in` names, `il` levels, `ie` expressions) and declarations. Before the
kernel proper sees anything, `Front.Export` and `Front.Lower` reduce the surface
language to the core. This is the "normalise aggressively up front" half of the
design; the whole point is that the core has fewer cases to get wrong.

| Surface | Fate | Justification |
| --- | --- | --- |
| binder annotations (`implicit`, `strictImplicit`, `instImplicit`) | erased | elaboration hints; no logical content |
| `mdata` | erased | ditto |
| `thm` | statement checked to be in `Prop`, proof checked, then **sealed as an axiom** where §12.10 says nothing can ever look inside it | the core has no theorems; the `Prop` requirement is the only thing lost, so it is checked here |
| `opaque` | checked like a definition, then admitted as an **axiom** | it must not delta-unfold; an axiom is exactly a constant that does not |
| reducibility hints | **kept**, as the delta-unfolding order of §7 step 6 (§12.11) | scheduling advice, and advice is all it can be: no ordering changes which terms are convertible |
| safety flags (`isUnsafe`, `safety`) | **kept**: they select a quarantined fragment (§12.7) | an unsafe declaration skipped the termination check, so its type is not a claim the kernel can use |
| nested inductives | compiled to mutual blocks (§9.1), which are then flattened (§9.3) | the core's positivity judgement has no rule for nesting, and no rule for a block |
| mutual inductive blocks | compiled to one tag type and one family indexed by it (§9.3) | the core's inductive rule is the one-family rule |
| exported recursors | **re-derived and required to match** (§8.7) | see below |

The last row is a load-bearing design decision. The export contains recursors
with their reduction rules, and a kernel that took them on trust would accept
whatever eliminator the file cared to write down. `eink0rn` instead builds the
recursor its own way from the inductive specification, and then requires the
exported one to agree with it: same universe count, same parameter/motive/minor/
index counts, same `k` flag, definitionally equal type, and one definitionally
equal reduction rule per constructor with no rules left over. An export cannot
smuggle in an unwarranted large elimination, an extra iota rule, or a bogus `k`.

Agreeing with us is necessary and not sufficient: two independently derived rules
can be wrong in the same way, and a comparison would not notice. So every rule
the kernel derives is also typechecked against the type its own left-hand side
has, which is a claim about that rule alone and not about the exporter (§8.9).

The same holds for the block's *shape*: the set of recursor names in a block must
be exactly `{T.rec | T declared}` plus the auxiliaries nesting introduced (§9), so
an extra eliminator cannot be parked alongside the justified ones.

**Options.** Two flags move the verdict, and both default to the strictest
setting that does not reject a faithful export. Everything else in this document
describes the default configuration. `--keep-proofs` and `--progress` cannot
change a verdict at all.

| flag | default | effect |
| --- | --- | --- |
| `--nat-accel=off\|canonical\|verified\|always` | `canonical` | how much evidence the arithmetic shortcuts of §6.5 demand before firing. `always` is unsound and exists only to reproduce other kernels' behaviour. |
| `--pin-std=off\|warn\|error` | `off` | audit the standard constants against their stored forms (§12.5). Never affects soundness; `error` can reject files that are perfectly consistent. |
| `--keep-proofs` | off | retain every proof term instead of sealing it (§12.10). A pure performance switch: the sealed and unsealed kernels accept exactly the same files. |
| `--progress[=SECS]` | off | report on stderr as the file is checked, naming each declaration that took at least `SECS` seconds. |

---

## 2. Syntax

### 2.1 Names

```
n ::= [anonymous] | n.s | n.i | π_k              (s a string, i and k naturals)
```

Hierarchical, built from the anonymous root by string and numeral components,
plus one further root `π_k` per natural number. Names are compared structurally
and carry a cached hash. They have no meaning to the theory beyond identity —
with the exception of §12.1.

The `π_k` are the **private roots**. Nothing in the theory distinguishes them;
they exist because the front end has to invent constants and needs names the
file provably does not use. See §9.4.

### 2.2 Levels

```
l ::= 0 | succ l | max l l | imax l l | u        (u a level parameter)
```

### 2.3 Expressions

```
e ::= #i                     bound variable (de Bruijn index)
    | x!n                    local constant (checker-internal; never in the environment)
    | Sort l
    | c.{l̄}                  constant, with universe arguments
    | e e                    application
    | fun (b : e) => e
    | forall (b : e), e
    | let b : e := e; e
    | e.[T, i]               projection: field i of a T-structure
    | nat_lit n              natural-number literal
    | str_lit s              string literal
```

Representation is locally nameless: a binder that has been entered is replaced by
a fresh local constant `x!n` whose type lives in the local context. `b` ranges
over binder display names, which are cosmetic and never affect any judgement.

This is the *whole* term language. In particular the core has no `mdata`, no
binder info, no metavariables, and no universe metavariables.

---

## 3. Universe levels

A level denotes a function from assignments `ρ` of its parameters to naturals:

```
[[0]]ρ        = 0
[[succ l]]ρ   = [[l]]ρ + 1
[[max a b]]ρ  = max([[a]]ρ, [[b]]ρ)
[[imax a b]]ρ = 0                        if [[b]]ρ = 0
                max([[a]]ρ, [[b]]ρ)      otherwise
[[u]]ρ        = ρ(u)
```

`l₁ ≤ l₂` means `[[l₁]]ρ ≤ [[l₂]]ρ` for **every** `ρ`; `l₁ ≈ l₂` is `l₁ ≤ l₂ ∧ l₂ ≤ l₁`.
Lean has no cumulativity, so the typing rules only ever need `≈`, but `≈` is
decided through `≤`.

Two derived predicates are used by the inductive rules:

- `isDefinitelyZero l` ⟺ `l ≤ 0` — i.e. `Sort l` is a proposition under every assignment;
- `isDefinitelyNonZero l` ⟺ `1 ≤ l` — i.e. `Sort l` is never a proposition.

Note these are not complements: `u` is neither.

### 3.1 Deciding `≤`

`levelLeq a b` normalises both sides and decides `a ≤ b + d` (`d ∈ ℤ`) by:

```
a ≡ b and d ≥ 0                        ⇒ true
a = 0 and d ≥ 0                        ⇒ true
a = succ a'                            ⇒ a' ≤ b + (d-1)
b = succ b'                            ⇒ a  ≤ b' + (d+1)
a = max a₁ a₂                          ⇒ a₁ ≤ b + d  and  a₂ ≤ b + d
a has an irreducible `imax _ u`        ⇒ split on u
b has an irreducible `imax _ u`        ⇒ split on u
b = max b₁ b₂                          ⇒ a ≤ b₁ + d  or  a ≤ b₂ + d
a = 0                                  ⇒ d ≥ 0
b = 0                                  ⇒ false        (a is a parameter: unbounded)
a = u, b = v                           ⇒ u = v and d ≥ 0
otherwise                              ⇒ false
```

"Split on `u`" means: decide the goal with `u := 0` and with `u := succ u`, and
require both. Each branch strictly reduces the number of irreducible `imax`
nodes, so this terminates.

Every rule above is an **equivalence** except `max`-on-the-right, which is only
sufficient (`u ≤ max u v` is caught, but a genuinely disjunctive obligation could
in principle be missed). It is applied *last*, after `imax` case-splitting has
removed the shapes that would make the loss of information matter. Being
one-sided in the sufficient direction, its failure mode is rejecting a well-typed
file, never accepting an ill-typed one.

The `imax` case split is what makes this procedure complete on the identities
that Lean's own level normaliser is known to be incomplete on. See §12.2.

---

## 4. Environments

The core admits exactly five kinds of constant, plus the quotient primitives:

```
axiom  c.{ū} : T
def    c.{ū} : T := v
ind    T.{ū}                 an inductive family, always flat (§8)
ctor   c.{ū}                 a constructor of some family
rec    T.rec.{ū}             the recursor of some family
quot   one of the four quotient primitives (§10)
```

Declarations are **write-once**: re-declaring a name is a hard error. Every
constant's type is checked to be a well-formed type (`inferSortOf`) before it is
admitted, and every definition's value is checked against its type.

Definitions carry an unfolding *priority*, read from the export's `hints` field
(§12.11) and used only to decide which of two constants to unfold first. It
cannot affect what is convertible — only how fast the kernel notices — which is
why it is the one field the kernel takes from the file without checking it.

---

## 5. Typing

### 5.1 Contexts

A context assigns types to local constants. Because the representation is
locally nameless, inference threads a *de Bruijn environment* `Δ` — the list of
local constants the enclosing binders were opened with, innermost first, so that
`#i` denotes `Δ!!i`. See §11.1 for the invariant this satisfies.

### 5.2 Rules

Written with substitution, as if `Δ` were applied eagerly. `Γ` is the local
context and `Ū` the current declaration's universe parameters.

```
                    Γ(x) = T
(local)          ─────────────────
                  Γ ⊢ x : T


                 params(l) ⊆ Ū
(sort)        ────────────────────────
               Γ ⊢ Sort l : Sort (succ l)


              (c.{ū} : T) ∈ E     |l̄| = |ū|     params(l̄) ⊆ Ū
(const)     ───────────────────────────────────────────────────
                     Γ ⊢ c.{l̄} : T[ū := l̄]


              Γ ⊢ f : T     T ⟶*ʷʰⁿᶠ forall (x : A), B     Γ ⊢ a : A
(app)       ────────────────────────────────────────────────────────────
                              Γ ⊢ f a : B[x := a]


              Γ ⊢ A : Sort _        Γ, x : A ⊢ b : B
(lam)       ─────────────────────────────────────────────
              Γ ⊢ (fun (x : A) => b) : forall (x : A), B


              Γ ⊢ A : Sort l₁       Γ, x : A ⊢ B : Sort l₂
(pi)        ─────────────────────────────────────────────────
              Γ ⊢ (forall (x : A), B) : Sort (imax l₁ l₂)


              Γ ⊢ A : Sort _   Γ ⊢ v : A   Γ ⊢ b[x := v] : B
(let)       ────────────────────────────────────────────────────
                    Γ ⊢ (let x : A := v; b) : B


(nat)         Γ ⊢ nat_lit n : Nat
(str)         Γ ⊢ str_lit s : String
```

`(app)` requires `A` and the inferred type of `a` to be *definitionally* equal,
not syntactically; likewise everywhere a rule writes a specific type.

`(let)` **zeta-expands**: the body is typed with the value substituted, not with
`x` in the context. So `let` has no independent typing content — it is a sharing
device, and the kernel treats it as one everywhere.

### 5.3 Projections

`s.[T, i]` is the interesting rule.

```
   Γ ⊢ s : T p̄        T structure-like with unique ctor  mk : forall (p̄) (f₀ : F₀) … (f_{n-1} : F_{n-1}), T p̄
   0 ≤ i < n
   Fᵢ' = Fᵢ[p̄ := p̄][f₀ := s.[T,0], …, f_{i-1} := s.[T,i-1]]
   Γ ⊢ Fᵢ' : Sort sortF        Γ ⊢ T p̄ : Sort sortT        sortF ≤ imax sortF sortT
   and the same side condition for every earlier field whose projection actually
   occurs in the remainder of the telescope
──────────────────────────────────────────────────────────────────────────────────
   Γ ⊢ s.[T, i] : Fᵢ'
```

"Structure-like" means: exactly one constructor and no indices. That is the whole
content of the eta principle — an element of such a type *is* its constructor
applied to its fields — and it is all a projection needs. Whether the type is
recursive is beside the point here: recursion constrains what the *fields* may
mention, and this rule is about the *outermost* constructor. Lean's own libraries
project out of recursive structures (`Lean.Meta.Grind.AC.DiseqCnstr.lhs`, whose
type is one half of a mutual block), and there is nothing wrong with it.

One consumer does need the extra clause, and it is a reduction rule rather than a
typing rule: §6.3's eta expansion of a *stuck major premise*. See there.

**The side condition.** If `T p̄` is a proposition then all of its inhabitants are
convertible by proof irrelevance, so `(mk true).[T,0]` and `(mk false).[T,0]`
would be convertible — a projection out of a proposition may therefore only land
in a proposition. Quantified over all universe assignments, "`sortT = 0` implies
`sortF = 0`" is exactly

```
sortF ≤ imax sortF sortT
```

The condition applies to the field being projected *and* to every earlier field
whose projection is actually substituted into the rest of the telescope: reading
`s.[T,i]`'s type off a telescope instantiated with an *illegal* projection would
be reading it off a type that does not exist. An earlier field that nothing
downstream mentions is skipped, so a data field may sit between two proof fields
of a proposition without poisoning them.

This is stated as `imax` rather than as a case split on `sortT`. Doing it that
way, and having a `≤` that case-splits on `imax` (§3.1), is what closes the hole
by construction rather than by patching a special case; see §12.2.

---

## 6. Reduction

### 6.1 `whnfCore` — everything except delta

Repeatedly, on the head of the spine:

| rule | |
| --- | --- |
| **beta** | `(fun x => b) a ⟶ b[x := a]` (all leading lambdas peeled at once) |
| **zeta** | `(let x : A := v; b) ā ⟶ b[x := v] ā` |
| **proj** | `(mk p̄ f̄).[T, i] ⟶ fᵢ`, provided `mk`'s own inductive type is `T` |
| **iota (rec)** | §6.3 |
| **iota (quot)** | §6.4 |

The `proj` rule's side condition (`ctorInduct mk = T`) matters: without it a
projection could be reduced against a constructor of a *different* structure that
happens to be in head position.

### 6.2 `whnf` — with delta

`whnf` alternates `whnfCore` with **delta**: unfold the head constant when it is a
definition whose universe arity matches. Definitions declared `opaque` are
axioms and never unfold, and neither do proofs sealed under §12.10.

Unfolding substitutes the occurrence's universe arguments into the stored body
and applies it to the arguments the head had — and applies it by *contracting*
the beta redex, all binders at once, rather than handing `whnfCore` a body under
a spine for it to contract a binder at a time. The term is the same either way.
What differs is the number of reduction steps it took to get there, and the
budget of §7.4 is spent per step, so the difference decides how much of a
comparison is done before the budget runs out and a speculation gives up.

### 6.3 Iota for recursors

```
T_j.rec.{l̄} p̄ C̄ ē ī (c p̄ f̄)  ⟶  rule_c[l̄] p̄ C̄ ē f̄
```

where the major premise sits at position `|p̄| + |C̄| + |ē| + |ī|`, read off the
counts the recursor carries. A recursor the core derives has one motive (§8.7),
but the ones §9.3 derives for the members of a flattened block share one set of
motives `C̄` and one set of minor premises `ē` across all the members, exactly as
the export declares them; the prefix a rule is applied to is then the same for
every recursor of the block, and only the rules differ. This arithmetic covers
both because it never assumes `|C̄| = 1`. Arguments after the major premise are
re-applied.

Three things can make a non-constructor major premise usable:

**Literal expansion.** `nat_lit 0 ⟶ Nat.zero` and `nat_lit (n+1) ⟶ Nat.succ (nat_lit n)`.
For strings, write `⟦s⟧` for the character list `[Char.ofNat (nat_lit k₀), …]` of the
code points of `s` and `b` for `List.utf8Encode ⟦s⟧`; then

    str_lit s ⟶ String.ofByteArray b (ByteArray.IsValidUTF8.intro b ⟦s⟧ (Eq.refl.{1} ByteArray b))

A `String` is not a list of characters but the byte array a list of characters
encodes, paired with the evidence that it is one; the literal names the character
list and lets the file's own `List.utf8Encode` say what the bytes are. The evidence
is `Eq.refl`, so the expansion is well typed whatever that function computes, and
the kernel never has to have an opinion about UTF-8. Literals are abbreviations and
nothing more, and they expand only once the constants they abbreviate are checked to
be the ones they mean (§12.1).

**K-like reduction** (only when `k` is set on the recursor, §8.5). If the major
premise's type is `T p̄ ī`, then the canonical constructor application `mk p̄` has
that same type, so the (possibly neutral) major premise may be replaced by it.
The `isDefEq (majorTy, ctorTy)` guard is essential: without it `Eq.rec` would
reduce at `Eq a b` for non-convertible `a` and `b`.

**Structure eta on the major premise.** For a structure-like `T`, every element is
convertible to `T.mk s.[T,0] … s.[T,n-1]`, so a neutral major premise of structure
type still reduces.

This rule, alone among the ones that appeal to §5.3's structure-likeness, also
requires `T` to be **not recursive**, and the reason is termination rather than
soundness. Rewriting a stuck `s` to `T.mk s.[T,0] … ` lets iota fire; but if a
field is recursive then the rule it fires produces the recursor applied to
`s.[T,j]`, which is stuck again, and gets eta-expanded again, forever. The rule
would be sound; it would simply never stop. §7.2's eta is not exposed to this,
because it only fires against a side that already *is* a constructor application,
and descends into that side.

### 6.4 Iota for `Quot`

```
Quot.lift α r β f h (Quot.mk α r v)  ⟶  f v
Quot.ind  α r β h   (Quot.mk α r v)  ⟶  h v
```

### 6.5 Arithmetic on numerals

`Nat.ble 1114113 4294967296` is a single machine comparison and about a million
iota steps. A kernel that only knows the second reading cannot check
`Init.Prelude`, where bounds like `UInt32.size` are settled by `decide`. So the
numerals are computed on:

```
f ⌜a⌝      ⟶  ⌜f a⌝                    f = Nat.pred
f ⌜a⌝ ⌜b⌝  ⟶  ⌜f a b⌝                  f ∈ {Nat.add, Nat.sub, Nat.mul, Nat.pow,
                                            Nat.div, Nat.mod}
f ⌜a⌝ ⌜b⌝  ⟶  Bool.true / Bool.false   f ∈ {Nat.beq, Nat.ble, Nat.blt}
```

where `⌜n⌝` is *any* term the numeral reader (below) accepts, subtraction is
truncated, and division by zero gives `a / 0 = 0`, `a % 0 = a`. `Nat.pow`
declines when the answer would not fit in memory; that is not a correctness
matter — the slow path cannot finish such a case either — but it decides *how*
the kernel fails, by running out of time, which a caller can bound, rather than
out of memory, which it cannot.

None of these rules is on by default merely because it is listed here. Each one
has to be *licensed*, per operation and per environment; the rest of this section
is about what a licence costs. `div` and `mod` are licensed on weaker evidence
than the rest, and that is set out separately below.

**This rule is not keyed on the name.** `Nat.add` is a name, and a file that
defined it as multiplication would be handed an equation the theory does not
contain — `2 + 2 ≡ 5` — if the kernel were willing to say so on the strength of
the name alone. Every soundness bug of this shape has that cause: a constant the
kernel gives a meaning to without checking that the file gave it the same one.

So the licence is *derived*, once per environment, from the definition's own
declared type and defining equations. The stored specification each operation is
held against lives in one file, `Kernel.Canon`, so that the whole of what the
kernel believes about the standard library can be read in one sitting; nothing in
it is believed, and everything in it is something the kernel will check.

**What is stored is a specification, not a definition.** It is tempting to store
the canonical *body* of `Nat.add` and compare against that. It does not work, and
the reason is worth recording. An exported `Nat.add` is a `Nat.brecOn` over an
auto-generated matcher, with binder names carrying a hash of the module they were
elaborated in; two different recursion schemes over `Nat` compute the same
function but are not definitionally equal as open terms, so even a `≡` comparison
against a stored body would fail on a faithful export and would pin the
elaborator's mood on the day rather than the arithmetic. The stored form of an
operation is therefore its **type** together with its **defining equations**,
which is both stable across compiler versions and, unlike a body, a direct
statement of what the function computes.

For `Nat.add`, with `x`, `y` fresh locals of type `Nat`, the kernel checks

```
add x 0        ≡ x
add x (succ y) ≡ succ (add x y)
```

and nothing else. Both are ordinary conversion questions about open terms, and
conversion is stable under substitution, so they may be instantiated at any
closed terms. That settles every numeral case at the meta level, by induction
on `b`:

```
  add ⌜a⌝ ⌜0⌝    ≡ add ⌜a⌝ 0           (numeral reading)
                 ≡ ⌜a⌝                  (first equation at x := ⌜a⌝)
  add ⌜a⌝ ⌜k+1⌝  ≡ add ⌜a⌝ (succ ⌜k⌝)  (numeral reading)
                 ≡ succ (add ⌜a⌝ ⌜k⌝)  (second equation)
                 ≡ succ ⌜a+k⌝          (induction hypothesis)
                 ≡ ⌜a+k+1⌝             (numeral reading)
```

so `add ⌜a⌝ ⌜b⌝ ≡ ⌜a+b⌝` for all `a` and `b`, which is exactly what the rule
asserts. The other operations go the same way, from these equations and no
others:

| operation | declared type | equations | needs |
| --- | --- | --- | --- |
| `Nat.pred` | `Nat → Nat` | `pred 0 ≡ 0`, `pred (succ x) ≡ x` | |
| `Nat.add` | `Nat → Nat → Nat` | `add x 0 ≡ x`, `add x (succ y) ≡ succ (add x y)` | |
| `Nat.sub` | `Nat → Nat → Nat` | `sub x 0 ≡ x`, `sub x (succ y) ≡ pred (sub x y)` | `pred` |
| `Nat.mul` | `Nat → Nat → Nat` | `mul x 0 ≡ 0`, `mul x (succ y) ≡ add (mul x y) x` | `add` |
| `Nat.pow` | `Nat → Nat → Nat` | `pow x 0 ≡ succ 0`, `pow x (succ y) ≡ mul (pow x y) x` | `mul` |
| `Nat.beq` | `Nat → Nat → Bool` | the four constructor cases | |
| `Nat.ble` | `Nat → Nat → Bool` | the four constructor cases | |
| `Nat.blt` | `Nat → Nat → Bool` | `blt x y ≡ ble (succ x) y` | `ble` |
| `Nat.div` | `Nat → Nat → Nat` | *none statable* — probed instead, below | |
| `Nat.mod` | `Nat → Nat → Nat` | *none statable* — probed instead, below | |

An operation whose equations are stated in terms of another additionally requires
that one to have been licensed already, since the induction step appeals to its
numeral case. `blt` is settled by a single equation rather than four because it
says outright which comparison it is, and `ble` has by then been pinned to that
comparison.

**The declared type is checked too.** An equation is a conversion question, and
conversion does not care what type its two sides have. Equations alone would
therefore let a constant declared at `Foo → Foo → Foo` — whose two "equations"
happened to check, `Foo` being whatever it likes — have the kernel replace a term
of type `Foo` with a `Nat` numeral, which is a type error the kernel would have
introduced itself. So the declared type is compared against the stored one, and
an operation carrying universe parameters (the stored types have none) is
declined outright.

Two further properties make this safe rather than merely plausible. The equations
are written with the very constants the rule will emit — `Nat.succ`, `Nat.zero`,
`Bool.true` — so whatever those names happen to denote, the induction concludes
something about the term actually produced; no name is believed, only related to
itself. And failure is inert: an operation that does not check is not
accelerated, and reduces the slow way.

Checking the equations runs on a full budget (§7.4), since a conversion between
open terms either gets stuck quickly or does not, and a licence that depended on
what the asking caller had left would not be a property of the environment. The
answer is a property of the environment. While it is being established the
operation is recorded as *not* accelerated, so the conversion checks cannot appeal
to the rule they are establishing.

A licence, once granted, is remembered and carried forward to every later
declaration in the file. That is sound because a licence is established by
inspecting the declarations of finitely many named constants and declarations are
write-once (§4): no later line can change what those names mean, so a *yes* stays
a *yes* in every larger environment. A *no* is not carried forward — the constant
some dependency needed may simply not have been declared yet — so it is asked
again. Only the cost is affected either way; the verdict on a file is not.

**`div` and `mod` have no statable equations, and are licensed by probing.** An
exported `Nat.div` recurses on a fuel argument under a guard `0 < y`, so `div x y`
with `x` and `y` open gets stuck on a comparison it cannot decide; no rewriting of
the equation moves that, and there is nothing of the shape above for the kernel to
check. What such a definition *does* do is compute. Handed two numerals it reduces
to a numeral, by the file's own rules and with no help from the kernel. So instead
of an equation these two are held against a **probe battery**: a fixed list of
numeral pairs on which the file's own `div` and `mod` must reduce to the right
answers.

The battery is 169 exhaustive pairs — every `a`, `b` in `0 … 12`, so every relation
the two arguments can stand in appears, including both zero cases — followed by a
short irregular ladder past it, with dividends up to 128 chosen to include a
divisor of one, a divisor exceeding the dividend, equal pairs, exact quotients,
maximal remainders, powers of two and their neighbours, and a large zero divisor.
The ceiling is low deliberately: a fuel recursion costs about the square of the
dividend, so probing at the numerals this licence exists to make cheap would cost
exactly what the licence saves. For the same reason the probes, unlike the
equations, run on a *fixed* budget rather than a full one — they reduce closed
terms, which have no guarantee of getting stuck, and a definition that does not
compute must not be able to turn the attempt into an unbounded one. The budget is a
constant, so the answer is still a property of the environment; a starved probe
answers *no*, which only ever declines a shortcut.

**This is weaker than an equation licence, and is marked as such in the code.** An
equation between open terms settles every numeral case at once, by the induction
displayed above. A probe settles the one case it names. What the kernel supplies is
the extrapolation from the pairs tried to the rest, and that extrapolation is the
whole of what this licence assumes — nothing else here rests on an unchecked step.
Two things bound the risk. Every probe that passes is an equality the file's theory
already had, so on a file whose `div` really is division the shortcut adds no
definitional equality at all; and a file whose `div` differs from division
anywhere in the battery is declined outright, so the shortcut can only be wrong for
a definition contrived to agree on 185 named pairs and disagree elsewhere.

`Nat.le` has no entry for a plainer reason — it is an inductive family in `Prop`,
not a function, and has nothing to compute; the decidable comparisons that stand in
for it, `Nat.decLe` and `Nat.decLt`, reduce through `ble` and `blt`, which do.

**Modes.** `--nat-accel` selects how much evidence a licence requires. The
default demands the most that can be demanded without rejecting a faithful
export.

| `--nat-accel=` | licence requires | sound |
| --- | --- | --- |
| `off` | — nothing is ever accelerated | yes |
| `canonical` *(default)* | the stored type, the stored equations *or* probes, the dependencies, **and** that `Nat` and `Bool` are the standard inductive types | yes |
| `verified` | the stored type, the stored equations *or* probes, the dependencies | yes |
| `always` | the name | **no** |

The extra condition in `canonical` is that `Nat` is a parameter-free, index-free
inductive in `Type` whose constructors are exactly `Nat.zero : Nat` and
`Nat.succ : Nat → Nat` in that order, and — for the comparisons — that `Bool` is
likewise `Bool.false`, `Bool.true` in that order, each check being on arity,
constructor names and order, and `≡` on every type involved. That is not needed
for soundness, which the equations already carry, and it is what separates
`canonical` from `verified`: it is a statement about what the kernel is willing
to be *surprised* by. A file that reimplements `Nat` with a third constructor and
an `add` that still satisfies both equations is doing something the author of
this checker did not anticipate, and the default is to decline the shortcut and
unfold, rather than to be clever about a situation nobody designed for. Soundness
is unaffected either way; `verified` is available for anyone who wants the
shortcut on that file anyway.

`always` is the odd one out: it is the only mode that takes a name on trust, and
it is provided so that `eink0rn` can be made bug-compatible with a kernel that
does, for the purpose of *reproducing* a disagreement rather than resolving it.
It is not sound and is not a supported way to check a proof. It is also the only
mode that will accelerate an operation for which neither equations nor probes are
stored, which at present is no operation at all.

**Reading a numeral.** `⌜n⌝` is a `nat_lit`, or `Nat.zero`, or `Nat.succ`
applied to a numeral — folded back to an integer, and read up to `whnf`. Folding
is not a refinement: `Nat.decLt n m` is `Nat.decLe (Nat.succ n) m`, so a
comparison against a bound reaches the rule with one constructor already peeled
off, and accepting only bare literals would miss every `decide` in the prelude.
This is sound for the same reason the expansion in §6.3 is: it is used only
where §12.1's `Nat` shape check has passed, which is what makes `Nat.succ ⌜k⌝`
and `⌜k+1⌝` the same term as far as conversion is concerned.

The walk up the `succ`s is bounded, at 256. A tower a file writes by hand is one
or two deep, and a tower it can only have arrived at by counting is one the reader
should not be counting back down. Giving up returns the term unread, which costs
at most the shortcut on that term.

**The held numeral.** `Nat.add`, `Nat.sub`, `Nat.mul` and `Nat.pow` are all
exported as structural recursions on their *second* argument, and this is the one
place where the shape of the export leaks into what the kernel is willing to do.
Unfolding one of them counts that argument down. With both arguments numerals
that never happens, because the rule above fires first and answers in one step.
With the first argument open it happens in full: `x + ⌜k⌝` sets a `brecOn` going
that builds `k` levels of `Nat.below` before it can say anything, and what it
eventually says is that there is nothing to say — `x + ⌜k⌝` has no head
constructor to find. This is not hypothetical. A signed bit width appears in the
prelude as an offset of `2³¹` or `2⁶³` against an open term, and two billion steps
to learn that a term is stuck is the same thing as not terminating.

So a licensed operation from that list, applied to a numeral larger than 4096 in
the argument it recurses on, is **held**: `whnf` leaves the application alone
rather than delta-unfolding it. The two sides of a conversion are then compared
argument by argument, which is what they were always going to have to be compared
by.

Held is a property of the *application*, not of the constant, and everything that
asks "may delta take a step here" has to ask it of the application. A conversion
that asked only about the head would be told that a definition was there for the
unfolding, be handed the term back unchanged when it asked for the unfolding, and
ask again — for ever, on a budget that never moves because nothing reduces. So a
held application answers "no" to that question, exactly as a local constant or an
axiom does, and §7 reads it as rigid throughout.

Nothing about the theory changes. Declining to unfold removes reduction sequences
and so can only remove conversions, never add them; every judgement the kernel
still makes it made before. What the bound is a statement about is effort. Only a
*licensed* operation is held — without a licence the kernel has no reason to
believe the name recurses the way the equations say, and unfolds it like anything
else.

**What is lost, and where it is given back.** The conversions the hold removes
are those between an offset over a large numeral and the same offset written some
other way — most of all, `x + ⌜k+1⌝` against `Nat.succ (x + ⌜k⌝)`. That is not an
exotic term. `Char`'s bounds proofs are full of it: a lemma states
`x + ⌜57344⌝ + ⌜1⌝ ≤ ⌜1114112⌝` and is used where `x + ⌜57345⌝ ≤ ⌜1114112⌝` is
wanted; reduction gets the first side to `Nat.succ (x + ⌜57344⌝)`, because the
outer `+ ⌜1⌝` is small enough to unfold, and stops. §7's offset rule is what
relates the two, and it is stated only over held applications, so it gives back
exactly what the hold took.

---

## 7. Definitional equality

`isDefEq t s` first tries syntactic equality (cheap, hash-guarded), then
`whnfCore`s both sides, then loops:

1. **Binder congruence** — `Lam`/`Lam` and `Pi`/`Pi`: domains defeq and bodies
   defeq under a fresh local. *Definitive*: nothing else applies to a binder in
   whnf.
2. **Function eta** — `f ≡ fun x => f x`, tried in both directions. *Definitive*
   when either side is a lambda.
3. **Sorts and literals** — `Sort a ≡ Sort b` iff `a ≈ b`; literals by value;
   literal against constructor-headed term by expanding the literal.
   *Definitive*.
4. **Rigid spine congruence** — when the head is *not* a delta-unfoldable
   definition (a local, an axiom, a constructor, an inductive type, a stuck
   recursor, a stuck projection, or an arithmetic application the kernel has
   declined to unfold, §6.5), compare heads and arguments pairwise.
   *Positive only*: failure falls through.
5. **Proof irrelevance** — if `t`'s type is a proposition and `s`'s type is
   definitionally equal to it, `t ≡ s`. Preceded by the syntactic test of §7.5,
   which settles most pairs without inferring anything.
6. **Lazy delta** — unfold the side whose head definition has the greater
   unfolding priority (§12.11); when priorities are equal and both heads are the
   same constant, first try argument-wise congruence, and only unfold both if
   that fails.
7. When nothing can be unfolded, the **last resort** rules: projection
   congruence, the numeral-offset rule (§7.6), structure eta, and unit-like eta.

A round of step 6 that unfolds nothing is a round that ends the loop. This
sounds like a restatement of step 7 and is in fact the only thing keeping the
loop finite, because "the head is a definition" and "the definition will unfold"
are two different questions: an arithmetic application over a large numeral has
a definition for a head and is nevertheless held (§6.5). A round that answered
"unfolded, carry on" while handing back the terms it was given would have the
loop ask the identical question forever, on a budget that is never spent because
nothing is reducing. So step 6 reports what it did rather than what it intended,
a side that declines falls through to the other side, and only a round in which
neither side moved stops. The rigid reading of a held application in step 4 is
the other half of the same correction: a comparison that delta will not be
allowed to advance should get the congruence rule that a rigid pair gets, and
get it on the full budget rather than the speculative one.

### 7.1 Why this order

Rigid-spine congruence is tried *before* proof irrelevance and before delta. It
is not speculative (there is nothing else a rigid pair could reduce to), it costs
nothing when the heads differ, and getting it in early is what keeps the kernel
from inferring the type of every intermediate term of a long computation — which
is what proof irrelevance would otherwise do.

For a head that *is* a definition the same congruence *is* speculative, since the
two sides may only agree after unfolding, so it is left to step 6 where it can be
weighed against the priorities.

### 7.2 Structure eta and unit-like eta

- **Structure eta**: if one side is `mk p̄ f̄` for a structure-like type and the
  other has that type, compare each `fᵢ` with `other.[T, i]`.
- **Unit-like eta**: a structure with *no* fields has exactly one element up to
  conversion, so any two terms of that type are equal.

Both terminate on a recursive structure as well as on a flat one, unlike §6.3's
eta on a major premise. The rule only fires when one side is already a
constructor application, and it recurses into the fields *of that side*, which is
a finite term that gets strictly smaller.

### 7.3 The one-sided invariant

**Every call to `isDefEq` in the kernel is in a positive position.** A `False`
can only cause a rejection or a missed reduction; it can never cause an
acceptance. This is what licenses the incompleteness in steps 4 and 7, the
sufficient-only `max` rule in §3.1, and the budget in §7.4.

### 7.4 Fuel, waste, and `DStarved`

This is an efficiency device, not part of the theory, and it is the part most
worth being suspicious of — so, precisely:

Some comparisons are *speculative*: the caller is going to unfold and ask again if
the answer is no. Argument-wise congruence under equal heads (step 6) is the
example. The arguments the two sides disagree on may be exactly the ones that
unfolding the head is about to discard, and normalising them can cost arbitrarily
more than the comparison the caller actually wants.

So a speculative comparison runs under a step budget (`tcFuel`), drawn from a
running allowance for *wasted* work (`tcWaste`). When the budget runs out,
reduction stops where it stands and the comparison answers `False`.

A *step* is a **reduction** step — a beta, zeta, iota or projection rewrite, or a
delta unfolding — and nothing else. In particular the *descent* is free:
congruence walks into arguments without reducing anything, and none of that is
charged.

That asymmetry is deliberate and was measured. Charging a step per comparison
does bound the speculative subtree, and it bounds the wrong one: deep spines of
equal heads are exactly what congruence exists for, and a speculation that runs
out of budget part-way down one sends the loop off to unfold both heads instead —
the expensive thing the rule was there to avoid. On Mathlib's category theory
that is the difference between a file that checks in four minutes and one that
does not finish. The principle behind the asymmetry is that what a descent costs
is bounded by the terms in front of it, and shared subterms are compared once
because the answer is remembered (§11.4), whereas what a reduction costs is
bounded by nothing at all — one `Nat` numeral can ask for two billion steps.

The allowance is **credited**, not fixed. A declaration opens with 50000 steps
and earns one more for every eight reduction steps the checker performs outside a
speculation, to a ceiling of the same 50000. A fixed per-declaration allowance is
the wrong shape for this: it is generous on a one-line lemma and is gone in the
first instant of a machine-generated arithmetic certificate, and what happens when
it runs out is not that the checker goes a little slower — it stops speculating at
all, and every congruence that would have closed in a hundred steps is replaced by
unfolding both heads. The cap meant to stop a proof running away is then exactly
what makes it run away. Crediting says the affordable thing instead: dead ends may
consume a bounded fraction of the reduction the checker was going to do anyway,
whatever the size of the declaration, and the opening balance doubles as the most
that may be spent on any one speculation.

This is sound because **every rule that answers `True` is sound no matter how much
reduction preceded it**. A starved comparison can therefore only ever answer
`False`, and in a speculative position `False` means "not this way", not "not
equal". Nothing that is a proof stops being one; a speculation that would have
succeeded costs one unfolding and gets asked again with a fresh budget on the
next pass.

Two consequences are handled explicitly:

- Speculation that *pays off* is not charged against `tcWaste`; work that decided
  a comparison is work the checker would have had to do anyway. The budget bounds
  dead ends, not congruence.
- Rules that have to *infer a type* (K-like reduction, structure eta, unit-like
  eta, proof irrelevance) are skipped when the budget is exhausted. With no fuel
  left, reduction has stopped early, so the types they would read off are not the
  real ones; the honest answer is "no opinion" rather than a wrong one.
- `DStarved` is returned when the budget ran out before *anything* could be
  unfolded. It is not a statement about the terms — it says the round made no
  progress, so the loop must stop rather than ask the same question forever.
- An **error** raised inside a speculation is caught and read as `False`, and the
  state is rolled back. With the budget gone, reduction has stopped where it
  stands, so a type read off what it left behind can be anything at all —
  `(fun x => A → B) c` is not a function type until someone can afford the beta
  step — and a rule that reads types off terms must be able to answer "no
  opinion" rather than "this file is wrong". Nothing is hidden by this: every
  term a speculation compares is a subterm of something the declaration's own
  *unmetered* inference visits, and by §7.3 a `False` can only ever decline. A
  real error is therefore reported by the pass whose job it is, not by a
  shortcut that ran out of money.

The budget is therefore a completeness knob with no soundness content. Raising it
can only turn rejections into acceptances of things that were already provable;
lowering it can only turn acceptances into rejections.

### 7.5 Deciding "not a proof" without inferring a type

Step 5 is asked about nearly every pair the loop reaches, and it answers *no*
almost every time, because what is usually being compared is two values rather
than two proofs. Answering it the direct way costs two inferences and all the
reduction they set off, so the kernel first tries to rule the term out on sight.

A term `t` is a proof exactly when the type of its type is `Prop`. Write `u` for
the universe of `t`'s type — the level with `T(t) : Sort u`. Then `t` is a proof
iff `u ≈ 0`, so any argument that `u` is *definitely nonzero* rules step 5 out.

For a term whose head is a constant `c` declared `∀ x₁ .. xₙ, B`, that argument
can be made from declared types alone:

- if `B` is `Sort v`, then `u = v+1`, which is never zero;
- if `B` is a constant `d` applied to arguments and `d` is declared
  `∀ ȳ, Sort w`, then `u = w` with `c`'s level arguments substituted;
- if `B` is a *bound* variable `xⱼ` applied to arguments and `xⱼ` is declared
  `∀ z̄, Sort w`, then `u = w`.

The last case is what matters in practice: it is the shape of every eliminator
and every match auxiliary, whose result is a motive applied to its major
premise, and the motive's universe is written down in its own binder. The
middle case covers everything that computes — `Nat.mul a b`, `List.cons x xs` —
whose result is an inductive type whose universe is written down in *its*
declaration. A definition standing in the way is unfolded, because the class
hierarchy declares its output parameters `outParam (Type u)` rather than
`Type u`, and an argument whose type is a type is exactly what has to be
recognised. The answer is read off `c`'s declaration once and cached under `c`'s
name; the occurrence's own level arguments are substituted at each use.

The number of arguments does not enter into it, which is worth spelling out
because it looks like it should. Applying `c` to *fewer* than `n` arguments
gives a type `∀ rest, B`, whose universe is `imax _ u`; applying it to *more*
requires `B` to be a function type `∀ x:A, C`, whose universe `u` is
`imax (univ A) (univ C)`. An `imax` is zero exactly when its right argument is,
so in both directions "definitely nonzero" is preserved, and a single level per
constant answers for every arity.

Everything here is one-sided in the sense of §7.3: a *yes* ("not a proof") must
be right, and it is, being a chain of declared types and the `imax` rule; a *no*
costs only the slow route, which is the rule as stated.

### 7.6 The numeral-offset rule

A last-resort rule for the pairs §6.5's held numeral leaves stuck:

```
t ≡ s   when   t = b + ⌜k⌝,  s = b' + ⌜k⌝,  k > 0,  b ≡ b'
```

Each side is read as a base and a numeral offset by walking down through at most
256 layers of `Nat.succ e`, `Nat.add e ⌜k⌝` and `Nat.zero`, whnf'ing each layer
first — the terms reaching this rule have had their heads normalised and nothing
else, so the numeral is usually several unreduced instance projections down — and
stopping at whatever is left. A literal `⌜v⌝` reached on the way is `0 + v`. The
walk is bounded for the reason §6.5's `natShape` walk is: nothing stops a term
from being a deeper successor tower than anyone wants to count, and giving up
costs only this rule on this pair.

Three conditions keep it honest:

- **One of the two sides must be a held application.** That is the only way such
  a pair reaches a stuck comparison at all, so the reading is not attempted on
  every other last-resort pair, and the rule is doing nothing but undoing a
  specific refusal in the one place that refusal shows.
- **`Nat.add` must be licensed** in the sense of §6.5 — the file's own `Nat.add`
  must satisfy `x + 0 ≡ x` and `x + succ y ≡ succ (x + y)`. Those two equations
  are exactly the derivation this rule stands on. Without the licence `Nat.add`
  is not held either, and ordinary reduction handles the pair.
- **A zero offset is not a match.** Two terms with no arithmetic in them are
  every other rule's business.

Soundness is that derivation: given the two equations, `b + ⌜k⌝` and `b' + ⌜k⌝`
reduce to the same `k`-fold successor of `b` and `b'`, which are convertible by
assumption. The rule is *positive only*, like the rest of step 7 — a failure to
read a side as an offset, or offsets that differ, falls through rather than
concluding anything.

---

## 8. Inductive types

The core primitive is a **single flat family**: one type over a parameter
telescope, then a plain telescope of indices, ending in a sort. Neither of the
two structures the export format puts on top of that reaches here. Nesting is
compiled away by §9.1 into extra members of a mutual block, and the mutual block
is compiled away by §9.3 into two single families. So every rule below is stated
once, for one type — the case the thesis states before it generalises — and
`Kernel/Inductive.hs` reads the same way.

### 8.1 Why a single family, and not a mutual block

The thesis takes a mutual block as the primitive (§2.9). This kernel did the
same for most of its life, and the switch is worth recording, because three of
the four reasons on file were arguments *against* it.

The project's stated ambition was to compile mutual inductives away into a
single indexed type with projections. That was tried and, for a while, rejected:

- The encoding needs an index type (a finite enumeration of the block's members)
  that may not exist yet — mutual blocks appear in the prelude *before* anything
  to index them with;
- eliminating into `Sort u` from that index type requires it to large-eliminate,
  which is another obligation to discharge before the prelude has the machinery;
- the members of a block may in principle sit at *heterogeneous* universe levels
  — the types the file declares share one level, but §9.1 adds a member per
  nested occurrence and each of those stands for a container admitted elsewhere,
  at whatever level that container has — and a single type has one level.

The first two are answered by building the index type *in the same breath* as
the flattened family, in a scratch environment, out of nothing (§9.3.1): it is a
parameterised enumeration whose constructors have no recursive fields, so it
large-eliminates by §8.5 case 1 no matter what the prelude does or does not yet
contain.

The third is nearly vacuous. The universe condition of §8.4 already forces the
levels to agree in almost every case: a recursive field landing in member `k` has
sort `l_k`, and `imax(l_k, l_j) ≤ l_j` forces `l_k ≤ l_j` whenever `l_j` is not
zero; an auxiliary that recurses back into the block sits in a cycle with it, so
the two levels are equal. What escapes is a `Prop` nesting inside a data
container — `inductive A : Prop | mk : List A -> A` would put a `Prop` member
beside a `Type 0` auxiliary — and instrumenting the construction to report every
auxiliary level found **no** such block anywhere: 1 in `init`, 3 in `std`, 41 in
`cslib` and 200 across `refs/tests`, `tests` and `validation`, all at the
declared members' own level.

A fourth objection was asserted here for a while and was simply wrong: that a
*nested* block could not be flattened at all, because the export types its
constructors and recursors at the real container types and those can never be `F`
at a tag. The premise is true and the conclusion does not follow; §9.3.5 records
the argument and the mistake in it.

With all four answered, §9.3 flattens *every* block, the mutual case became
unreachable, and it is now gone from the core. What that deleted is one index —
"which member?" — threaded through everything: an owner on every constructor
shape, a target member on every recursive occurrence, a vector of motives where
there is now one motive, a vector of recursors built in lockstep with it, a
duplicate-name check across members, and the uniform-universe rule discussed
under §8.3. What it bought is that §8.5 case 2 no longer needs a side condition
saying "and only for one member", and that the reader of this section never has
to hold two levels of indexing at once.

The genuinely aggressive normalisation is still nesting, which is compiled away
completely (§9.1); flattening is what turns its output, and everything else,
into something this section can talk about.

### 8.2 Notation

Following the thesis, with parameters as ordinary context variables (the outer
`forall params` is put back at the very end):

```
t   : forall a::α, Sort l           the family
c   : forall b::β, t p̄[b]           a constructor
b_i : forall x::ξ_i, t π_i[b,x]     a recursive field
```

### 8.3 Admitting a family

1. The arity is a well-formed type, with at least as many leading `Pi` binders as
   it declares parameters, ending in a `Sort`.
2. The family is added to a scratch environment as an **axiom** of exactly its
   declared arity, and the constructors are checked against that. So a
   constructor may see only an opaque constant of the right arity where its own
   type should be — it cannot exploit anything about that type's contents.
3. Constructor analysis (§8.4).
4. Derived attributes (§8.5, §8.6).
5. Recursor construction (§8.7), whose derived type is itself type-checked as an
   audit.

**Where the uniform-resultant-universe rule went.** A mutual block is one
declaration with one set of motives and one set of minor premises shared by all
its members, read as a single family indexed by "which member?"; members at
different universes make that reading false, and the elaborators that produce
these files hold to it. When the core took blocks, it enforced that directly —
"every type the file *declared* in this block ends in the same sort, up to the
level equivalence of §3" — with an exemption for the members §9.1 adds, whose
levels are not the file's business.

The core no longer sees a block, so it no longer states the rule; and nothing is
lost, because §9.3 derives it from the ordinary typing of definitions. The
flattening builds one family `F` at one level and then *defines* each declared
member as `F` at a tag. A member declared at a different sort makes that
definition ill-typed — its body does not have its declared type — and the block
is rejected by the same check that rejects any other bad definition, with no
inductive-specific machinery at all. The derived version is *stricter* in one
respect: it does not grant §9.1's auxiliaries the exemption. That is one of the
three deliberate divergences of §9.3.4, and no file has ever needed the
exemption (§8.1).

### 8.4 The `ctor` judgement

Walking a constructor's type left to right, after peeling the parameters:

For each field `dom` with sort `l'`, where `l` is the sort the family ends in:

- **Universe condition**: `imax(l', l) ≤ l`. When `l = 0` this holds always — a
  proposition may quantify over anything. Otherwise it amounts to `l' ≤ l`.
- **Classification**: if the family does not occur in `dom`, the field is
  non-recursive. Otherwise `dom` must have the strictly positive shape
  `forall x::ξ, t p̄ π̄` where:
  - the family does not occur anywhere in `ξ` (no occurrence to the left of an
    arrow),
  - `t` is applied to the family's own parameter locals, unchanged,
  - `t`'s universe arguments are exactly the family's own,
  - the family does not occur in the indices `π̄`.

  Anything else — a negative occurrence, or the family under some other type
  constructor — is rejected. Neither a nested nor a mutual occurrence ever
  reaches here: §9 has already turned both into an index of a single family.

The result type must be `t p̄ ī`, with the same parameter and universe conditions,
and with the family not occurring in `ī`.

Field types are whnf'd before being peeled, so a field whose type is a definition
that only unfolds to a function type is still analysed correctly.

The "occurs in" of the classification is *syntactic*, and a syntactic occurrence
can be one that reduction is about to erase: the specialised containers §9.1
builds routinely have fields like `(fun (x : T) => True) v`, where the family `T`
survives only in the binder annotation of a redex. So whenever the syntactic
check fires — on a field's type, or on a binder type inside `ξ` — the term is
whnf'd and the check is asked again, and only an occurrence that survives
reduction is treated as one. This can only accept fields that the syntactic
reading would reject, and it accepts them because their types really are
convertible to types the family does not occur in.

### 8.5 Large elimination

The family eliminates into an arbitrary `Sort` when either:

1. `isDefinitelyNonZero l` — it is not a proposition under any assignment; **or**
2. it is a *subsingleton*: at most one constructor, each of whose fields is
   either a proof or is recovered from the result's indices. Formally, with the
   single constructor's shape `sh`, every field `f` satisfies

   ```
   isDefinitelyZero (sort of f)   ∨   f ∈ resultIndices(sh)
   ```

   A family with **no** constructors satisfies this vacuously: an empty
   proposition eliminates into anything.

Case 2 is what makes `Eq.rec`, `And.rec` and `Acc.rec` large-eliminating while
`Exists.rec` is not: `Exists.intro`'s witness is data that the result type
`Exists p` does not mention, so it must not be allowed to escape.

**Case 2 is a licence about one family, and now it is one by construction.** The
subsingleton licence is justified by reading the eliminator back as a function
that recovers the constructor's fields from the major premise and its indices —
proof irrelevance says there was nothing else to know. That argument is about one
family with one motive. When the core took mutual blocks, this case carried an
explicit "the block has exactly one member" side condition, because a block's
recursor also carries motives and minor premises for the *other* members, whose
constructors' data is recovered from nothing. There is now only ever one motive,
so the side condition has nothing left to exclude.

It has not, however, been quietly dropped: §9.3 would otherwise hand a whole
block the licence through the back door, since its flat family `F` *is* one
family. Two things stop that. `F` collects every member's constructors, so a
block with two constructors anywhere in it already fails "at most one
constructor". And for the residue — a block whose members contribute one
constructor between them — the flattening does not consult `F`'s answer at all:
it gives the block's own recursors §8.5 case 1 and nothing more (§9.3.4). The
rule is also applied after §9.1 has run, so a nested `Prop` loses the licence
too, which is right: the container field it nests under is data.

**"Is a proof" is read absolutely.** The field's sort must be zero under every
assignment, not merely whenever the family itself lands in `Prop`. The weaker,
relative reading `l' ≤ imax l' l` is tempting — it is what one reaches for to
justify a universe-polymorphic structure with fields at `u` and `v` — but it is
not the rule, and `refs/tests/good/tutorial/093_MaybeProp.mk.ndjson` settles it:

```
MaybeProp.{u} : Sort u
MaybeProp.mk  : PUnit.{u} → (PUnit.{u} = PUnit.{u}) → True → MaybeProp.{u}
MaybeProp.rec : one universe parameter, motive into Sort 0
```

The first field sits at `u`, and the exported recursor has no elimination
universe. The relative reading would grant one, since `u ≤ imax u u`.

Nothing is lost by the strict reading: the polymorphic structures one worries
about are covered by case 1. `PProd` and `PSigma` are declared at
`Sort (max 1 (max u v))`, which is provably non-zero, so they never reach the
subsingleton test.

### 8.6 The `k` flag

K-like reduction (§6.3) is available exactly when the family is
`isDefinitelyZero` and has exactly **one** constructor with **zero** fields. This
is the shape of `Eq`. (The old "and the block has one member" clause is, again,
structural now.)

### 8.7 Recursors

One recursor:

```
T.rec.{u, l̄} : forall params,
               forall (C : κ),          -- the motive
               forall e::ε,             -- one minor premise per constructor
               forall a::α,             -- the indices
               forall (z : T params a),
               C a z
```

with

```
κ   = forall a::α, T params a -> Sort u
ε_c = forall b::β, forall v::δ, C p̄[b] (c params b)
```

where the induction hypotheses `v` come after *all* the fields, one per recursive
field:

```
v_i : forall x::ξ_i, C π_i[b,x] (b_i x)
```

`u` is a fresh universe parameter under large elimination and `0` otherwise. Its
*name* is taken from the export when the export has one, purely so that the
derived type is literally the same term and comparisons are cheap; the name is
cosmetic.

The iota rule for constructor `c`:

```
T.rec params C ē p̄[b] (c params b)  ⟶  e_c b v̄
    where  v_i = fun x::ξ_i => T.rec params C ē π_i[b,x] (b_i x)
```

Right-hand sides are stored abstracted over `params, C, ē, fields`, in that order.

`RecInfo` still carries a motive *count*, which is now always 1 for a family the
core admits. It is not vestigial: the recursors §9.3 derives for the members of a
flattened block are one per member over a shared vector of motives, exactly as
the export declares them, and §6.3's arithmetic reads the count off the recursor
it is reducing rather than assuming either shape.

### 8.8 What the export must then agree with

Per §1: `all` lists exactly the block's declared types (not the recursors, and not
the nesting auxiliaries); the parameter, motive, index and minor counts match; the
`k` flag matches; the universe-parameter count matches; the type is definitionally
equal; and the rules match, **positionally**, in constructor order, each with the
same constructor name, the same field count and a definitionally equal right-hand
side. Constructor bookkeeping (`induct`, `idx`, `numParams`, `numFields`,
universe parameters) is checked the same way.

Positionally, and not by looking each declared rule's constructor up among the
derived ones: a permuted rule list is a file saying one thing and meaning another
(§12.9), and matching by name would also let a file repeat one constructor's rule
and drop another's while keeping the list the right length.

A declared recursor's universe parameters must also be *distinct*. They are
matched to the derived recursor's positionally, so a repeated name would make
that substitution ambiguous — `rec.{u,u}` could be read as either projection —
and the comparison would be deciding a question the file did not ask.

### 8.9 The rules must typecheck

Everything above is a check on a recursor's *type*: §8.7 derives it, typechecks
it, and §8.8 requires the export to declare the same one. Its reduction rules
get none of that. They are terms the kernel builds and then believes, and §8.8's
comparison is not a substitute, because it compares two terms neither of which
anything has typechecked: it catches the exporter disagreeing with us, and says
nothing whatever about the two of us being wrong together.

So each rule is checked on its own terms. For a recursor `t.rec` with parameters
`p̄`, motives `C̄`, minor premises `ē`, and a rule for constructor `c` with
fields `b̄`:

> reconstruct the left-hand side `t.rec p̄ C̄ ē ā (c q̄ b̄)`, where `ā` are the
> indices `c q̄ b̄` actually has; infer its type; and require
>
> `rhs p̄ C̄ ē b̄  :  that type`.

If the rule's right-hand side is not of the type its own left-hand side has,
then iota does not preserve typing and everything downstream of it is worthless,
whatever the exporter happened to write. This is checked for every recursor of
every block, on both admission paths.

The indices and the constructor's own parameters `q̄` are read off the major
premise's type rather than assumed to be the recursor's. They need not be: §9.1
replaces an auxiliary member's constructors by the real container's on the way
out, so an auxiliary recursor's rules are for `List.cons` at `List`'s parameters,
not for anything the block declared. Doing it this way is what turns the check
into a test of §9.1's transport as well — the substitution asserts that the
specialised copy may be retyped at the container, and here that assertion has to
typecheck.

---

## 9. Nested inductives

A nested inductive mentions itself underneath some *other*, already admitted, type
constructor:

```
inductive Syntax | node : SyntaxNodeKind -> Array Syntax -> Syntax | ...
```

The core has no rule for this: strict positivity (§8.4) only recognises an
occurrence as the head of a field's result. The standard reading is that
`Array Syntax` is a copy of `Array` specialised at `Syntax`, mutually recursive
with it — so that is literally what `Front.Lower` builds.

### 9.1 The transformation

1. **Discover.** Scan the block's constructor types (opened at the parameter
   locals) for subterms `C p̄ ī` where `C` is an already-admitted inductive type,
   `C` is applied to at least its parameters, the parameters are closed with
   respect to bound variables, and some member of the block occurs in them. Then
   scan the *specialised constructor types* of each container found, and repeat
   until nothing new appears. Every step moves to a container declared strictly
   earlier, so this terminates; the file's own `numNested` is used as a cap, and
   a mismatch is an error rather than a surprise.

   The scan stops *at* an occurrence: having reported `C p̄`, it looks only inside
   the indices `ī`, never inside `p̄`. Nothing is lost, because whatever is nested
   in `p̄` and actually matters reappears in `C`'s own constructor types once they
   are specialised at `p̄` — one round later rather than immediately. The queue of
   terms to scan is first in, first out, so the copies come out **breadth first**:
   the containers wrapping the block itself, then the containers wrapping those,
   and so on. Order is not cosmetic. It is the order of the auxiliary members,
   hence of the motives and minor premises of every recursor the block yields, and
   §8.8 requires the export's recursors to be the ones the kernel derived.

   A consequence of stopping at an occurrence is that a member buried in a
   parameter the container never uses gets no copy — correctly, since no
   constructor of the copy could mention it.

   An occurrence whose parameters mention a *bound* variable is deliberately
   skipped: the copy would have to depend on it and there is no such member. The
   block's own name is then left where it is, and strict positivity rejects it.

2. **Build.** Each distinct occurrence becomes an extra member of the block under
   an internal name `π.nested.k`, where `π` is the block's *private namespace*
   (§9.4), with the container's arity specialised at those arguments, and the
   container's constructors specialised likewise under names
   `π.nested.k.ctor.j`. The block is required to be nested only in the
   container's *parameters*: an index is not a positive position, and a member
   occurring in one would silently be dropped by the specialisation.

3. **Rewrite.** Every occurrence in the block's own constructor types is replaced
   by the corresponding auxiliary member applied to the block's parameters.

4. **Admit.** What remains is an ordinary flat mutual block, which §9.3 flattens
   in turn and §8 then handles with no special cases.

5. **Unnest.** After the recursors are derived, the internal names are replaced by
   the containers they stood for. An auxiliary is always applied to the block's
   parameters first, so the substitution beta-reduces on the spot and what comes
   back out is exactly the term the export wrote. The auxiliary members, their
   constructors, and their recursors are dropped; **nothing internal ever reaches
   the environment**. (§9.3 is the one construction of which that is not true.)

6. **Re-audit.** Unnesting rebuilds terms behind the kernel's back, so for a
   nested block every surviving recursor type is type-checked again in the final
   environment before the export is compared against it.

### 9.2 Why this is the right shape

Because the specialised copies go through the *same* positivity and universe
checks as everything else. Unsound nesting is caught by those checks and not by a
special case: nesting inside `fun a => a -> False` turns into a member with a
negative field, and the `ctor` judgement of §8.4 rejects it. There is no separate
"is this container acceptable to nest in?" predicate to get wrong.

### 9.3 Flattening a mutual block

§8.1 records why the core used to take a mutual block as primitive rather than
reducing it to a single indexed family. The first objection was that the reduction
needs a tag type, that a tag type needs to be admitted first, and that the obvious
way to admit it is with the very rule one was trying to avoid. That objection is
real but it is not fatal, because the tag type does not need the mutual rule — it
is a plain enumeration-with-arguments. This section takes the reduction seriously
and does it; §8.1 answers the other three objections.

**Every** block is flattened, so `Kernel.Inductive` is only ever handed one type.
The order is the one §9 already fixes: nesting is compiled first and flattening
runs on its output. §9.1 turns a declaration with `m` nested occurrences into a
block of `1 + m` members over specialised copies of the containers; §9.3 turns
any block of two or more members into two ordinary single inductive types. So the
guard is arithmetic —

```
flatten  ⟺  (types the file declared) + (auxiliaries §9.1 added)  >  1
```

— and a block that is already a single type goes straight through, because there
is nothing left to do to it. Every other shape, mutual or merely nested, is
flattened. §9.3.5 retracts the argument, published in an earlier edition of this
document, that the nested case was impossible.

#### 9.3.1 The construction

Given a block over shared parameters `p̄ :: π`

```
T_1 : ∀ p̄, α_1, Sort l    ...    T_n : ∀ p̄, α_n, Sort l
```

with constructors `c : ∀ p̄ b̄::β, T_j p̄ ā` — where `T_1 … T_n` are the members the
file declared followed by the auxiliaries §9.1 added — the checker admits two
ordinary single inductive types into a **scratch environment**, reads the block's
own constants off them, and throws the scratch environment away.

1. **The tag type.** One constructor per member, carrying that member's indices:

   ```
   Idx      : ∀ p̄, Sort v                 v = max 1 (sorts of every index of every α_j)
   Idx.mk_j : ∀ p̄ ā::α_j, Idx p̄
   ```

   `v` dominates every field's sort by construction, so §8.4's `imax(l',v) ≤ v`
   holds; and `v` is a `max` with `1`, so it is definitely non-zero and §8.5 case 1
   grants `Idx.rec` elimination into every sort. An arity may not mention its own
   block — the core checks arities in the environment the block is declared *in* —
   so `Idx` is admissible before anything else of the block exists.

2. **The flat type.** The block re-indexed by the tag:

   ```
   F : ∀ p̄, Idx p̄ → Sort l
   ```

   whose constructors are the block's own, with every occurrence `T_k p̄ ā` rewritten
   to `F p̄ (Idx.mk_k p̄ ā)`. The rewrite is syntactic, and requires the occurrence
   to be at the block's own parameters and fully applied to that member's indices —
   which is exactly what §8.4's `splitSelf` already required, so an occurrence the
   rewrite misses is one the core would have rejected. Any member name surviving
   the rewrite is an error.

3. **The members' stand-ins.** For as long as it takes to state step 4, each member
   is a *definition* in the scratch environment:

   ```
   T_j := fun p̄ ā => F p̄ (Idx.mk_j p̄ ā)      : ∀ p̄, α_j, Sort l
   ```

   checked at the arity the file declared. This is where the uniform-universe
   rule §8.3 used to state is paid for instead of assumed: `F` lands in whatever
   sort the *first* member does, and this definition typechecks only if the
   `j`-th member lands there too.

4. **The constructors, at the types the file wrote.** Two rewrites stand between
   the type `F`'s constructor was admitted at and the type the file declared, so
   there are two comparisons, both up to definitional equality. That unfolding the
   stand-ins of step 3 recovers the type *the block* gives a constructor is asked
   of every member, auxiliaries included. That §9.1's `applyAux` then recovers the
   type *the file* gives it is asked of the declared members only — an auxiliary's
   constructors are not in the file to compare against.

5. **The recursors**, one per member, derived from `F.rec` and **primitive**:
   `RecInfo`s carrying their own reduction rules, not definitions that unfold to a
   call of `F.rec`. Writing

   ```
   bigC := Idx.rec (fun i => F p̄ i → Sort u) C_1 … C_n
   ```

   for the term that turns the block's `n` motives into the one motive `F` has,
   `T_j.rec`'s type is `F.rec`'s own with the parameters peeled, the motive
   instantiated at `bigC`, and the block's `n` motives quantified back over; and
   each of its rules is `F.rec`'s corresponding rule beta-reduced at `bigC` and
   re-closed the same way. So the induction hypotheses are `F`'s, not a second
   implementation of §8.7.

   Both are then rewritten by three folding steps performed **by hand**:

   ```
   F p̄ (Idx.mk_j p̄ ā)               ~>  T_j p̄ ā
   bigC (Idx.mk_j p̄ ā) t            ~>  C_j ā t
   F.rec p̄ bigC ē (Idx.mk_j p̄ ā) t  ~>  T_j.rec p̄ C̄ ē ā t
   ```

   Each fires only on an occurrence in exactly the shape the construction put it
   in — at the block's own parameters, at `bigC` itself, at the very motive and
   minor-premise locals the term is stated over — so an accidental match is not
   possible; and every tag occurring in anything `F`'s admission produced is a
   literal `Idx.mk_j`, because step 2's rewrite is what put it there, so all three
   fire everywhere they must.

   Their standing is not the same, and it is worth separating. The first is step
   3's definition read right to left, so the two sides are definitionally equal in
   the scratch environment. The second is iota for `Idx.rec`, likewise. The third
   is neither: `F.rec` does not exist in the environment the file will be checked
   in and `T_j.rec` does not exist in the scratch one, so this is a *translation*
   between two environments and not an equation in either. What makes it right is
   that the result is the same term §8.7's rule construction would have produced
   for the block directly — `F.rec`'s minor premises are the block's, in member
   order and then constructor order, and its induction hypotheses land in the
   member the tag names. §9.3.3 says what checks that.

6. **Unnesting, and the audit.** §9.1's substitution puts the real containers back
   into the derived types and rules, exactly as it does for a block admitted the
   classic way. Then the checker demands that **no name this pass invented
   survives** anywhere in a derived recursor type or reduction rule — not `Idx`,
   `F`, their constructors or their recursors, and not §9.1's auxiliaries. If one
   does, the block is rejected as an internal error rather than admitted at a type
   naming a constant the caller cannot see.

7. **The environment.** What the caller gets back is the environment it handed in
   plus exactly the constants the file declared: the declared members as inductive
   types at their declared arities, their constructors at their declared types, and
   one recursor per member of the post-nesting block (`T.rec`, `T.rec_1`, …) as a
   primitive. The derived recursor types are typechecked once more there — for the
   reason §9.1's are, that they were rebuilt behind the kernel's back — and then
   compared against the file's own (§8.8).

Step 5's choice — recursors *derived from* `F.rec` rather than *defined in terms
of* it — is the load-bearing one, and §9.3.5 explains why.

#### 9.3.2 What this buys

**The uniform-universe rule stops being a rule.** Every member of a block lands
in the same sort — that used to be a step of §8.3, checked directly, with an
exemption for §9.1's auxiliaries. It is not checked here. It is *derived*, by
step 3, from the ordinary typing rule for definitions, and the checker reports
the failure in those terms. This is the fact the construction turns on: Lean's
exporter only ever emits blocks whose members share a universe, and that is
precisely the condition under which the flattening exists. The exemption goes
with it — here the auxiliaries pay the rule too, which is one of the three places
the front end is stricter than what it replaces (§9.3.4).

**Iota is one derivation instead of `n`.** The block's recursors are read off
`F.rec`'s single set of rules. The mutual recursion of §8.7 — an induction
hypothesis calling the recursor of *its own* member — is derived by ordinary
recursion on one type, and reappears in the finished rules only as a name.

**Elimination is decided by §8.5 case 1 alone.** A flattened block has two or more
members, so case 2 never applied to it anyway, and `isDefinitelyNonZero l` is the
whole rule. `F`, being one type, may qualify under case 2 where the block does
not; the recursors are built at the block's licence and not at `F`'s, so nothing
escapes.

**The core became a theory of one indexed family.** Every `CoreInd` reaching
`Kernel.Inductive` is a single family — the tag type, the flat type, or a
declaration that was already one type. The core's mutual machinery was therefore
running only at length one, and it has been deleted: §8.1 lists what went, and §8
is now stated for one type throughout. `Kernel/Inductive.hs` went from 499 lines
to 438, and `Front/Lower.hs` grew by 13 to hold the `CoreMember`-to-`CoreInd`
conversion that used to be implicit, so the strip is worth about 48 lines net;
against the pre-flattening kernel the module is 93 lines shorter. The flattening
as a whole is still not a saving — it costs some 485 lines net against the mutual
core it replaces — and the case for it is the three paragraphs above and §9.3.3,
not the line count.

One thing was genuinely given up. For as long as both front ends existed, the
mutual path was the *reference* the flattening was checked against: every claim
§9.3 makes about verdicts was backed by running both over the same files and
comparing. That comparison was run for the last time immediately before the
deletion — 1069 files across `refs/tests`, `tests` and `validation`, 0 differing
verdicts — and it can no longer be run from this tree. What is left as
independent evidence is the three-layer audit chain of §9.3.3, which does not
need a second implementation; recovering the stronger check means checking out
the pre-flattening revision and diffing verdicts against it.

**How often any of this happens.** Counts below are of *export blocks*, not of
Lean `mutual` commands: one `{"inductive": ...}` line, classified by whether its
`types` array holds more than one entry and whether it declares `numNested > 0`.
The two are independent, and the flattening fires on the sum. `a×b` in the last
column means `b` blocks of `a` members.

| corpus | blocks | single-type | single, nested | multi-type | multi, nested | flattened | members after §9.1 |
|---|---|---|---|---|---|---|---|
| `init` | 588 | 588 | 1 | 0 | 0 | 1 | 3×1 |
| `std` | 908 | 908 | 3 | 0 | 0 | 3 | 2×2, 3×1 |
| `cslib` | 4336 | 4324 | 38 | 12 | 3 | 50 | 2×12, 3×17, 4×7, 5×6, 6×3, 7×3, 9×1, 21×1 |
| `mathlib` | 6644 | 6631 | 38 | 13 | 3 | 51 | 2×14, 3×16, 4×7, 5×6, 6×3, 7×3, 9×1, 21×1 |

Nesting does not enlarge the *declared* part of a block: every multi-type block in
all four corpora consists of types the user wrote (`EqCnstr`/`EqCnstrProof`,
`ExBase`/`ExProd`/`ExSum`, `Lean.IR.Alt`/`FnBody`, …), never of an internally generated
auxiliary. It does enlarge the block that gets flattened, and that is where both
ends of the size distribution come from. A nested-but-not-mutual declaration such
as `inductive A : Prop | mk : Nonempty A -> A` arrives as a single-type block with
`numNested = 1` and is flattened at two members. The three blocks per corpus that
are both mutual and nested are the largest things the construction handles:
`Lean.Compiler.LCNF.{Alt,FunDecl,Cases,Code}` at 4 + 2 = 6 members, `Lean.IR.{Alt,
FnBody}` at 2 + 2 = 4, and `Lean.Meta.Grind.Arith.Cutsat.*` at 12 + 9 = 21. (An
earlier edition of this table reported those nesting counts as 8, 4 and 108. That
was a miscount: `numNested` is a property of the block, repeated on every entry of
`types`, so summing it over the members multiplies it by their number.)

`init` and `std` bound the fork's cost on the *common* path; the validation
corpus, where a hundred-odd files declare a mutual block on purpose, is where the
construction is actually exercised.

#### 9.3.3 What it costs

`Idx`, `F`, `Idx.rec` and `F.rec` are genuinely admitted, but into a scratch
environment that the construction drops on the way out. They never reach the
file's environment, and §12.7's barrier has nothing extra to guard. They are still
given names that cannot collide with anything — `π.idx`, `π.ty`, `π.idx.rec`,
`π.ty.rec` and `π.idx.mk.j` in the block's private namespace `π` (§9.4) — because
a file that had declared a constant of that name would otherwise collide with them
inside the scratch environment, and because step 6's audit is only worth running
if a surviving invented name could not have come from the file.

What remains is one extra inductive admission per flattened block (the tag type),
a second admission of the block itself in re-indexed form, and a second typecheck
of each derived recursor type in the final environment. On `init` and `std`, where
one and three blocks respectively are affected, it is not measurable — and the
measurement to make is of *allocation*, which for a single-threaded run of a
deterministic program is a deterministic number, rather than of wall clock, which
on a shared machine varies by several per cent between runs of the same binary.
Total bytes allocated over `init` moves from 227,386,318,400 before the fork to
227,379,978,936 after it, three thousandths of a per cent, in the noise of nothing
at all. That is what the table above predicts: 587 of `init`'s 588 blocks are
single types that go straight through, and the flattening never runs on them.

A cost-centre profile of the same run says the same thing from the other side:
there is no inductive-admission entry in it. Admitting the types of a file, which
is where every rule of §8 and every line of §9.3 is spent, does not appear among
the costs of checking one, because it happens once per declaration and everything
else happens once per reduction step.

The thing to audit is the by-hand fold of step 5: about sixty lines that rewrite,
outside the core, terms the core built, and whose correctness is implied by
nothing the core checked. Four things stand behind it, in increasing order of
what they catch.

- Step 6's *nothing invented survives* test. Cheap, and it catches a fold step
  that failed to fire: whatever it should have rewritten is still sitting there
  under a name the final environment does not have.
- Step 7's typecheck of each derived recursor *type* in the final environment.
- §8.9's typecheck of each derived reduction *rule*.
- §8.8's comparison of each derived reduction rule against the one the file
  declares, up to definitional equality.

An earlier edition of this section said that the last of these was the one
carrying the weight, and that this was not special pleading for the flattening
because **no** path in the kernel independently typechecked a recursor's
right-hand side. The observation was correct and the situation it described was
not defensible: §8.8 compares two terms neither of which anything has
typechecked, so it says nothing at all about a rule that both this kernel and
the exporter got wrong in the same way, and the only thing it really rules out
is a *disagreement*. §8.9 now typechecks every rule of every recursor, derived
or folded, against the type its own left-hand side has. That is an absolute
check and not a relative one, and it is what the fold now has to survive.

The alternative — not folding at all, and keeping `Idx` and `F` in the
environment so that the fold has nothing to rewrite — is what §9.5 is about. It
does not work, and the reason is worth reading before proposing it again.

#### 9.3.4 Deliberate divergences

What is left, after all that, on which this front end and a primitive-mutual one
disagree.

* **`indIsRecursive` is recomputed rather than read off `F`.** `F` knows only
  whether the *block* has a recursive field, and the flag is per member, so it is
  recovered by asking whether any member of the block occurs syntactically in one
  of this member's constructor types. Nothing that existed before the block was
  declared can mention a member of it, so an occurrence `whnf` would expose was
  already there syntactically and the test cannot under-report. It can over-report,
  on the erasable-redex fields of §8.4, and over-reporting costs only eta *during
  reduction* (§6.1) — a term getting stuck sooner, never a wrong reduction.

* **`Prop`-valued auxiliaries would be rejected.** §8.3 exempts §9.1's auxiliaries
  from the uniform-universe rule; step 3 does not, because it cannot. A block
  mixing a `Prop` member with a `Type` auxiliary — which needs a `Prop` nested
  inside a data container — is accepted by the classic path and refused here. §8.1
  records that no such block occurs in any corpus measured, so this is a divergence
  on paper only, but it is a real one.

* **Reduction is not more permissive.** Noted because an earlier version of this
  fork *was*: it wrapped the block's recursors around `F.rec`, and `F` — a single
  type — could qualify for the `k` rule of §8.6 where the block would not. That is
  gone. `F.rec` is not in the environment the file is checked in, and the recursors
  that are carry the block's `k` flag, which is false.

#### 9.3.5 A retracted impossibility argument

An earlier edition of this document argued that a *nested* block could not be
flattened, in any order, and concluded from that that "the export format requires
this kernel to have a mutual block as a primitive". Most of the argument is true
and the false step is instructive, so both are kept here.

The true part. `Lean.Syntax` in `init` has one declared type and two nested
occurrences, and the export commits to

```
Lean.Syntax.node : SourceInfo -> SyntaxNodeKind -> Array.{0} Syntax -> Syntax
Lean.Syntax.rec  : forall (motive_1 : Syntax -> Sort u)
                          (motive_2 : Array.{0} Syntax -> Sort u)
                          (motive_3 : List.{0} Syntax -> Sort u), ...
```

with reduction rules on `Array.mk`, `List.nil` and `List.cons` — the containers'
*real* constructors, not copies. (There are three recursors, `rec`, `rec_1` and
`rec_2`, one per member of the post-nesting block, all sharing those three
motives.) `Syntax.node` cannot be a constructor of a flat type in which `Syntax`
is `F p̄ (Idx.mk_1 p̄)`, because its third field would then be `Array (F p̄
(Idx.mk_1 p̄))` — an occurrence of the type being defined underneath another type
constructor, which is precisely what §8.4 rejects and §9 exists to remove. All of
that is correct, and it is why the two compilations run in the order they do: what
§9.3 flattens is the block that has the specialised copy of `Array Syntax` in that field, never the
block the file wrote.

The false step was the next one. §9.1 finishes by substituting the real containers
back into the constructor and recursor types it derived, and re-checking the
result; the claim was that after flattening there is nothing left to substitute,
because "the auxiliary's type occurs only as `F p̄ i` with `i` a *bound variable*,
instantiated to `Idx.mk_2 p̄` by the recursor's own reduction. The occurrence has
been absorbed into a binder, and a substitution cannot reach under it."

That is a true description of the *body* of a definition that wraps `F.rec`, and
of nothing else. It is not true of what actually has to be substituted:

- A recursor is a primitive. It has a type and a list of reduction rules and **no
  body** — so there is no term whose type must be preserved under the
  substitution, which is exactly the licence §9.1 already uses on the classic
  path.
- Its type names each member of the block *syntactically*. The motive for member
  `k` is `∀ ā, T_k p̄ ā → Sort u` and the major premise is `T_k p̄ ā`, both written
  with that member's own constant. `applyAux` reaches every one of them.
- The right-hand sides are in the same position: an induction hypothesis is
  `fun x̄ => T_k.rec p̄ C̄ ē π̄ (b x̄)`, with the member named outright.

So the substitution has plenty to reach, provided the block's recursors are
*derived from* `F.rec` rather than *defined in terms of* it. Deriving them is step
5, and this is why it is the load-bearing step. The absorbed-into-a-binder
phenomenon is real, but it is a property of the wrapper design the earlier fork
happened to use, not of flattening.

Two smaller claims fell with it and are also withdrawn. §5.3's projections and
§7.2's eta were said to need a side table — `envFlat`, `envUnflat`, and an
`unflatten` pass on the way out of `whnf` — but they needed it only because a
member had become a definition; members are inductive types again and the table is
gone. And §9.1's own need to read a container's arity and constructors was said to
need the same indirection; it is served by the ordinary environment lookup, for
the same reason.

### 9.4 Private namespaces

Both transformations invent constants, and an invented name has to be free: free
of everything the file declares, or the file could say something about a constant
the front end meant to keep to itself, and free of everything an earlier
transformation invented, or two blocks could collide with each other.

Rather than search for an unused name, the invented ones live somewhere the file
cannot write. §2's grammar of names is

>  `n ::= [anonymous] | n.s | n.i | π_k`

with the last a **private root**, one for each natural number `k`. The export
format has no syntax for it: the format's name pool starts at the anonymous name
and every later entry is built from an earlier one by appending a string or a
numeral (§13.1), so every name a file can mention is rooted at `[anonymous]`, and
`π_k.…` is not equal to any of them. Each inductive block is handed the next
unused `k` as it is lowered, and hangs everything it invents off `π_k`: §9.1's
specialised containers at `π_k.nested.j`, §9.3's two types at `π_k.idx` and
`π_k.ty`.

This is not a soundness argument about the constants themselves — they are
admitted by the same rules as any other, and §9.3.3's audit still insists none of
them survives into anything the caller gets back. It is what makes that audit
mean something: a private name found in a derived term is necessarily one this
pass put there.

### 9.5 Why the flat form is not kept

§9.3 builds `Idx` and `F`, reads the block's constants off them, and throws them
away. The obvious question is why: the flat form is the simplest shape the block
has — one inductive type, one recursor, no mutual anything — and it is the shape
the kernel just went to some trouble to construct. Keeping it would mean that
what *reduction* holds afterwards is that shape and not the block, which is a
stronger statement than "no mutual block reaches the core" and a better fit for
what §9 is for.

The construction is short. For a block §9.1 did not have to touch, admit `Idx`,
`F` and their recursors for real, install the file's constructors as `F`'s (which
they are, up to the type-level rewrite step 4 already checked), and make the
block's own constants definitions:

>  `T_j p̄ ā ≡ F p̄ (Idx.mk_j p̄ ā)`
>
>  `T_j.rec ≡ λ p̄ C̄ ē ā t. F.rec p̄ bigC ē (Idx.mk_j p̄ ā) t`

The first is exactly the stand-in of §9.3.1 step 4, already built and already
typechecked. The second is checked against the recursor type the block justifies
— a *stronger* obligation than §8.7 discharges for a primitive recursor, which is
handed its type by construction and never has a body to check. And the reduction
rules stop existing as terms this kernel builds: `T_j.rec` is a definition, what
it does is whatever δ and ι do to it, so the rule to compare against the export
(§8.8) is read back off `whnf` of the left-hand side. The sixty-line by-hand fold
of §9.3.1 step 5 disappears, and with it the audit obligations §9.3.3 lists.

It does not work, for one reason with two consequences.

**The members must become definitions, and there is no third option.** One might
hope to keep them as primitive inductive types and demote only the recursors. The
body of `T_j.rec` typechecks only if `T_j p̄ ā` and `F p̄ (Idx.mk_j p̄ ā)` are
convertible, and a primitive inductive type is convertible with nothing but
itself. So `T_j` is a definition or `F.rec` is unusable; keeping the flat form and
keeping the members inductive are mutually exclusive.

Two things dispatch on a member *being* an inductive type, and both of them fire
on real Lean output:

- **§5.3 projections.** `Proj T i s` requires `T` to be a structure-like
  inductive type and requires the inferred type of `s` to be headed by `T`. Under
  a kept flat form it is headed by `π.ty`. `cslib` rejects at
  `Lean.Meta.Grind.AC.DiseqCnstr.lhs`: *expected a value of type
  `Lean.Meta.Grind.AC.DiseqCnstr`, got `π.ty (π.idx.mk.0 …)`*. This is not a
  corner: of the blocks the construction applies to at all — 9 in cslib, 10 in
  mathlib — 7 in each have a member with one constructor and no indices.
- **§9.1's container lookup.** Deciding whether a *later* block is nested means
  finding an already-admitted inductive type in its constructors and reading off
  that type's arity and constructor list. A member of a kept-flat block is not
  one, so a block nested inside it is reported as having no nested occurrences at
  all and is rejected for disagreeing with its own `numNested`. Two cases in the
  validation corpus are exactly this shape.

Serving either one means carrying each member's arity, constructor list and
structure-likeness in a table beside the environment and consulting it wherever
`CInd` is consulted today — which is the `envFlat`/`envUnflat` indirection
§9.3.5 records the earlier fork needing and this one being rid of. That is not a
smaller kernel; it is one representation replaced by two and a compatibility
layer between them.

Two further observations settle it.

The construction only ever applies to a block §9.1 left alone, because `applyAux`
has to substitute a real container into a recursor's type and rules and a
definition's body is not something that substitution may rewrite (§9.3.5, same
argument in the other direction). So the fold survives for the nested majority
regardless — of the 50 blocks cslib flattens and the 51 mathlib flattens, 41 in
each are nested — and nothing is deleted, only branched. And the reach is nil
where it would be measured: `init` and `std` contain **no** block with more than
one declared type, so the performance question the construction raises is
answered by construction, not by a stopwatch.

What does survive from the attempt is its safety argument, and it survives
without it. The point of typechecking `T_j.rec`'s body was to put something
absolute behind the block's elimination rules; §8.9 now does that for every
recursor in the kernel, folded or primitive, by typechecking each reduction rule
against the type its own left-hand side has. The fold is audited; it just is not
replaced.

The construction above is implemented, and works as far as it can, on the branch
`flatten-keep`. It passes 186/186 of the arena corpus and 830/846 of the
validation corpus against 832/846 for this one, and rejects both cslib and
mathlib. It is kept because an argument of the form "this simpler thing does not
work" is worth more with the simpler thing next to it.

---

## 10. Quotients

`Quot` is the one piece of the theory that is neither an inductive type nor an
axiom: its eliminator computes, but only on `Quot.mk`, and unlike a derived
recursor it demands a proof that the function respects the relation. That extra
argument is exactly what keeps `Quot.sound` consistent, so the four primitives are
pinned down rather than taken on trust. Each declared primitive's type must be
definitionally equal to:

```
Quot.{u}   : forall (α : Sort u) (r : α → α → Prop), Sort u
Quot.mk.{u}: forall (α : Sort u) (r : α → α → Prop), α → Quot α r
Quot.lift.{u,v}
           : forall (α : Sort u) (r : α → α → Prop) (β : Sort v) (f : α → β),
             (forall a b, r a b → f a = f b) → Quot α r → β
Quot.ind.{u}
           : forall (α : Sort u) (r : α → α → Prop) (β : Quot α r → Prop),
             (forall a, β (Quot.mk α r a)) → forall q, β q
```

`Quot.sound` is *not* here. It is an ordinary axiom in the export and is admitted
as one; the kernel synthesises nothing for it. Only the four kinds above are
recognised, and only their stated types are accepted.

Note that the expected types refer to the names the file itself gave to `Quot` and
`Quot.mk`. `Quot.lift`'s statement additionally mentions `Eq` — a name the file
owns and the kernel does not synthesise — so before `Quot.lift` is admitted, `Eq`
is checked to be equality. Without that check the congruence premise is whatever
the file wants it to be, and the quotient is unsound; see §12.1.

---

## 11. Implementation invariants

These are not part of the theory, but the rules above are only correctly
implemented if they hold.

### 11.1 The `LEnv` invariant

Inference threads a de Bruijn environment instead of substituting at every
binder. The invariant is asymmetric:

- `inferM m Δ e` may be given an `e` that is *open* with respect to `Δ`;
- the type it returns is always *closed* — every variable in it is a local
  constant with an entry in the local context.

That is what makes the environment cheap: it is threaded down through `Lam` and
`Pi` without touching the body, and materialised only where a subterm has to be
handed to something that needs a real term (a binder type entering the context, an
argument being substituted into a dependent codomain, the structure of a
projection). Substituting instead, as §5.2 is written, is quadratic: a telescope
of `n` binders copies its body `n` times.

A term needing more variables than the environment supplies is rejected as a loose
bound variable, not silently renumbered.

### 11.2 The `InferMode` invariant

`Verify` is the real judgement of §5.2: every premise of every rule is checked.
`Assume` computes the *same type* but takes the premises on trust, walking only
the head spine and the binders.

`Assume` is sound to use exactly when the term is already known to typecheck,
because then the premises it skips are known to hold. That is a standing
invariant of `whnf` and `isDefEq`: a term only reaches them after `checkType` has
been through it — a subterm of a checked term is checked, and the types
`ensurePi`/`ensureSort` hand around are the types of checked terms. The
conversion checker leans on this heavily; proof irrelevance asks for the type of
both sides of every stuck comparison, and re-verifying those turns a linear check
into a quadratic one.

Note which premises are *not* skipped in `Assume`: the two sorts in `(pi)` are part
of the result, not a premise, so they are computed in either mode.

### 11.3 Terms are graphs

The export shares subterms, and so do lifting, instantiation and universe
instantiation. A term whose printed form is astronomically large routinely fits
in a few thousand nodes. Two caches keep the kernel working on the graph rather
than on its tree unfolding:

- every node caches its `looseBVarRange`, so de Bruijn plumbing can leave a closed
  subterm alone in constant time;
- every node caches a structural hash, which decides most inequalities in constant
  time.

Both are maintained by pattern synonyms, so nothing outside `Kernel.Expr` can set
a cache to a lie.

Names are shared the same way and cache a hash the same way, and their equality
is the same three-step test: pointer, then hash, then walk. The pointer step
earns its keep because the export interns names in a pool, so the constant a
reduction step looks up and the key stored for it in the environment are one
object, and every binder of a term that came from a file is a name some other
binder also has. None of this is load-bearing — an implementation that interned
nothing would decide exactly the same verdicts, only slower.

Each traversal also builds a memo table on the nodes it visits, so that a shared
node is rewritten once rather than once per path to it, and so that the *result*
is a graph too. Substitution and universe instantiation are the exception, and
only in how they start: almost every beta step rewrites a handful of nodes, and
almost every universe instantiation is asked about a declared type of a few dozen,
and setting up a table for either costs more than the walk. So the plain recursion
is tried first under a visit budget and the memoised traversal is kept for the
terms that exceed it. Exceeding the budget is exactly the symptom of the sharing
that makes a table worth having. The two compute the same term; they differ only
in how much of the *result* is shared, and below the budget there is nothing to
share.

### 11.4 Memoisation keys

Inference and `whnf` are memoised on `(term, local environment)`, keyed by hash and
matched by **structural equality**.

Matching by pointer alone is the tempting rule — the tables are asked millions of
questions on a hard declaration and a pointer test is one instruction — and it is
wrong, because it misses the repetition that actually happens. Reduction
*rebuilds*: a beta step substitutes into a body and hands back fresh nodes, so
the same subterm arrives at the table again and again as a different pointer with
the same shape. A pointer-matched table answers none of those, and on a
machine-generated proof that is the difference between having a memo and not
having one. It is what made one `Char` lemma in `init.ndjson` ask the same seven
pairs of stuck terms about a million times each, and never finish.

Structural equality is affordable because it is not the naive one. A bucket is
reached by hash, so the two candidates already agree on their hashes before
anything is walked; the comparison then tries pointer equality, and only then
walks — under the graph-aware `eqE` of §11.3, a plain recursion under a visit
budget with a memoised traversal taking over when the budget runs out. So
comparing two shared terms costs their graphs and not their tree unfoldings, and
the walk that a pointer test was avoiding is bounded by the same reasoning that
bounds every other traversal in the kernel.

The environment half of the key is just the innermost local, which identifies the
whole list: fresh locals are handed out from a counter that only ever grows and
are immediately consed onto one particular environment, so no id is ever the head
of two different ones. `whnf` takes no local environment — by §11.1 it is only
ever called on closed terms — so its half of the key is constant.

All three tables are invalidated when the global environment or the declaration's
universe parameters change, since both the inferred type and what a constant
unfolds to depend on them. Buckets are capped so a hash collision cannot turn the
table into a leak. Missing a hit only wastes time.

The tables are *mutable* — an array of buckets indexed by the low bits of the
key, doubling when it fills. A balanced tree of ten million entries answers a
lookup in some two dozen dependent pointer chases, essentially all of them cache
misses, and pays for an insertion by copying the path it came down; a hard
declaration asks and answers millions of these questions. Nothing else about the
tables changes: the same keys, the same test, the same cap on how long a
bucket may get. The mutation does not escape: the tables are made, used and
dropped inside one call, so checking the same declaration twice against the same
environment gives the same answer, and the checker's interface stays pure.

One more table is kept, on a different key. Delta and iota both work by taking a
body out of the environment and replacing that declaration's universe parameters
with the ones written at the occurrence, and a proof that unfolds the same
polymorphic constant ten thousand times asks for the same instantiation ten
thousand times. Those are memoised on `(stored body, universe arguments)` — the
body by pointer, since it comes from the environment and is stable for as long as
the table lives, and the arguments properly, being short. Unlike the three above,
this one survives the environment changing, because what it records is a fact
about a body and some levels and not about an environment.

The `whnf` memo has one extra condition. A starved reduction stops where it
stands and returns a term that is correct to **use** — a speculation reads a
failure to reduce as "not this way", never as "not equal" — but not correct to
**remember**, since a later caller with a real budget would be handed the
half-reduced term as if it were the normal form and could fail a comparison that
holds.

The condition is not "the reduction ran outside a speculation", which is the
obvious rule and much too coarse: inside a speculation is exactly where the same
dictionary is normalised for the twentieth time, so a memo that switches itself
off there switches itself off when it is worth the most. What matters is not
whether there *was* a budget but whether the budget was ever *reached*. So the
checker keeps a count of how many times reduction has stopped for want of fuel —
a number that only ever goes up within a declaration — and `whnf` reads it before
and after. If it did not move, nothing anywhere inside that call gave up early,
and what came back is the normal form however small the budget was. That is the
common case, and it is recorded. If it moved, the result is used and forgotten.

That leaves the waste allowance, which a nested speculation *can* exhaust, and
which therefore also affects how far an unmetered reduction gets. It needs no
guard: the allowance only ever decreases within a declaration, and resets
between them, so the first encounter with a node is the one with the most budget
and no later caller is handed a result computed with less than it had itself.
(In the other direction there is nothing to protect against. A cached result
that is *more* reduced than a caller could have managed is still reached by
reduction steps, so it is a correct answer, just a better one.)

Conversion is memoised too, on **pairs** of terms, matched the same way and
symmetrically: the key mixes the two hashes in an order that does not depend on
which side is which, and a hit is accepted either way round, because §7's relation
is symmetric and half the questions asked of it are the other half asked
backwards. Only pairs whose sides are both applications or projections are filed,
since anything else is settled by one equality test or by one look at a head.

This table is the one place where a *negative* answer is remembered, so it is
worth saying why that cannot cost soundness. Every `true` in it was produced by
the rules of §7 and stays true however much or little reduction preceded it, so
replaying one replays a derivation. A `false` can only ever *decline*: it makes
some check fail, and a check that fails rejects the file. So the table can cost
completeness and cannot cost acceptance of an unsound file — and to keep the
completeness cost at nothing that matters, the two answers are filed on different
terms. A `true` is recorded unconditionally: it was derived, and a derivation does
not stop being one because the derivation was cheap. A `false` is recorded only
when the comparison that produced it ran **outside every speculation**, since a
`false` reached by giving up says "not this way" and not "not equal". Entries are
*read* under any budget: a remembered answer is at least as good as what the
caller would have worked out for itself.

The starvation count of the previous paragraph is the wrong ticket here, and the
difference is worth spelling out, because using it looks safer and is in fact
ruinous. A speculation nested somewhere inside an unmetered comparison moves that
count whenever it declines — and by §7.4 it declines *often*, since the allowance
is meant to run dry on a hard declaration. Reading the count across the whole
comparison therefore reports "someone, somewhere in here, gave up", which on a
hard declaration is always, and the negative half of the table switches itself off
for exactly the declarations it exists for.

The count means something for `whnf` and nothing here, and the reason is what the
two calls leave behind. A starved reduction leaves a half-reduced *term*, and a
caller handed it cannot tell; that is a real hazard and the count is the right
guard for it. A declined speculation leaves only a `false`, and its caller reads
that `false` as "unfold and ask again" — which it then does, and unfolding
preserves conversion, so the answer the unmetered call finally reaches is the
answer congruence would have given it, only later. What the enclosing comparison
concluded is therefore its own conclusion and not a truncation of one.

One exposure survives, and is stated rather than hidden. K-like reduction (§6.3)
consults conversion to decide whether the major premise may be rebuilt, and a
speculation that declines inside *that* comparison does change a reduct: `whnf`
returns the eliminator unreduced. `whnf` will not remember that term, but an
unmetered conversion that fails because of it will remember its `false`. This is
the same completeness gap §7.4 already accepts — a starved speculation costs an
unfolding — with the retry removed, and like the rest of §7.4 it can only decline.

One consequence is worth noting, because it runs the safe way. A cached `false`
is returned without spending the waste allowance the original comparison spent,
so later speculations have more budget than they would have had, and the checker
becomes *more* complete than an uncached run, never less.

Without these memos, inference and reduction run over the term's tree unfolding,
which for a shared term is exponentially larger than the term. In practice the
`whnf` memo is what makes arithmetic proofs finish at all: the same dictionary —
`instHMul`, `instOfNat` — is reached from every operation in the expression.

### 11.5 One local per binder occurrence

A binder is opened by replacing its bound variable with a fresh local constant.
Done naively, "fresh" means a counter, and the same `Lam` node opened twice gets
two different locals — which makes the two bodies two different terms, so every
memo above misses, and a term whose graph has a few thousand nodes is walked as
though it were its tree.

So locals are *interned*: the local for a binder is remembered against the pair
`(the binder's type as stored, the enclosing scope)`, and opening the same binder
again in the same scope hands back the same local. The enclosing scope is the
local that the innermost enclosing binder was opened as — a token, not a list.

Interning locals is the one place in the kernel where a term's identity is reused
across contexts, so the invariant that makes it safe is worth stating. What must
never happen is one local occurring twice in the same telescope: abstracting over
it at the outer occurrence would capture the inner one. It cannot happen here.
A local is created once and filed under exactly one scope. If a lookup made while
somewhere inside `x`'s own body ever returned `x`, then `x` would have been filed
under a scope at or below itself in the binder chain — a scope that did not exist
when `x` was made. So no environment ever holds one local twice, and no
abstraction can capture the wrong occurrences.

The memos above are keyed on a term and so are discarded between declarations.
The §6.5 licences are not: they are facts about the *environment*, they are
expensive to establish — the `div` probe battery is the whole of §6.5's ladder —
and a positive one stays true as the environment grows, so they are stored in the
environment and travel with it. Only positive answers travel; see §6.5 for why
that is what makes it sound.

---

## 12. The name surface, and deliberate divergences

Recorded so that a disagreement with official Lean can be diagnosed rather than
patched. §12.1 is the part of the kernel that is *not* name-blind, and how each
name is earned; §12.2 onwards are places where `eink0rn` knowingly answers
differently from official Lean, in both directions: §12.2 and half of §12.6
accept more, §12.3, §12.4 and §12.7–§12.9 accept less.

### 12.1 Names with meaning

Four rules reach for a constant by *name* — a name the file chose, and could
have attached to something else. Each is therefore pinned: the shape is checked
before the rule fires, and if the check fails the rule is simply not available.
A name is never evidence.

| rule | names | pinned by |
| --- | --- | --- |
| literal typing (§5.2) and expansion (§6.3) | `Nat`, `Nat.zero`, `Nat.succ` | `Nat` is an inductive whose two constructors are nullary and unary, and `Nat.succ (nat_lit 0)` typechecks at `Nat` |
| string expansion (§6.3) | `String`, `String.ofByteArray`, `ByteArray`, `ByteArray.IsValidUTF8.intro`, `List.utf8Encode`, `Eq.refl`, `List`, `List.nil`, `List.cons`, `Char`, `Char.ofNat` | the `Nat` check, plus the constructor arities of `String.ofByteArray`, `List.nil` and `List.cons`, plus: the expansion of a one-character string typechecks at `String` |
| arithmetic (§6.5) | `Nat.pred`, `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.pow`, `Nat.beq`, `Nat.ble`, `Nat.blt`, `Bool.true`, `Bool.false` | the operation's own declared type and defining equations, per operation; under the default mode also the standard shape of `Nat` and `Bool` |
| arithmetic (§6.5), probed | `Nat.div`, `Nat.mod` | the same, but with the equations — which for these two cannot be stated — replaced by a fixed battery of numeral pairs the file's own definition must reduce correctly on |
| `Quot.lift`'s congruence premise (§10) | `Eq` | `Eq` is an inductive family of the shape of equality, with a single field-free constructor |

The stored forms all three rules compare against are collected in one module,
`Kernel.Canon`, so that the complete list of things `eink0rn` has an opinion about
can be audited without reading the checker. Nothing in that module is trusted:
it is a table of *claims to be checked*, and every entry is reached only through
a comparison whose failure disables a rule rather than accepting a file.

One witness suffices for the literal cases because every numeral's expansion has
the same shape — `Nat.succ` applied to a numeral — and differs only in the
numeral; likewise a one-character string exercises every constant of the string
expansion at exactly the types any string's expansion uses them at, since strings
differ only in the length of the character list and the numerals in it. A literal
over constants that are not the right shape keeps its type and stays opaque, which
is sound: an uninterpreted constant proves nothing.

Of the string constants only three are required to be *constructors*, and for one
reason: an expansion whose head is not a constructor is inert, so nothing that
wanted to see a constructor gets shown the wrong thing. The rest need only have the
right type. In particular the kernel forms no opinion about what `List.utf8Encode`
computes: the byte array is whatever that function says, and the evidence field is
the expansion's own `Eq.refl`, which is a proof, so no rule below can depend on the
answer. A file that defines `List.utf8Encode` as a constant function makes all its
string literals convertible to each other — and to nothing else, since §7 step 3
still holds two distinct `str_lit`s apart. That direction only ever refuses a
conversion, never grants one, so the file is checked against a weaker theory rather
than a wrong one.

The `Eq` check is the one with teeth, and it is worth spelling out why it is
needed. `Quot.lift`'s congruence premise is `forall a b, r a b → f a = f b`, and
that `=` resolves by name against whatever the file declared. So the file
chooses how strong its own obligation is. Declaring

```
Eq.refl : forall (α : Sort u) (x y : α), Eq α x y     -- second point a *field*
```

makes `Eq` the total relation, the premise vacuous, and every function liftable
across every relation; combined with a `Quot.sound` stated over a second,
faithful equality, it collapses `Bool` and proves `False`. So before `Quot.lift`
is admitted, `Eq` must be an inductive with two parameters, one index, one
universe parameter and a single constructor, and both its type and its
constructor's type must be definitionally equal to

```
Eq.{u}      : forall (α : Sort u), α → α → Prop
Eq.refl.{u} : forall (α : Sort u) (a : α), Eq α a a
```

What iota for `Quot.lift` actually needs is that `Eq α x y` be inhabited only
when `x ≡ y`, and that follows from the shape alone: the sole introduction form
takes no fields, so any inhabitant of `Eq α x y` whnfs to `Eq.refl α a` for some
`a`, and matching its type against `Eq α x y` forces `x ≡ a ≡ y`.

The constructor is found by *position* — the unique constructor of `Eq` — and
pinned by its *type*. Its name is not load-bearing and is not checked: an
equality whose constructor is called something else is still an equality, and
rejecting it would be a divergence with no soundness content behind it. (§12.5
is an opt-in audit that does check the name, on the different ground that a file
in which it differs is not the file it is claiming to be.)

`Eq` is the only constant the kernel *borrows* in this way; every other name in
the table above belongs to a rule that could in principle be dropped, whereas
the quotient package cannot state its own premise without it.

### 12.2 Level-algebra completeness

`levelLeq` case-splits fully on `imax` (§3.1) and so decides identities that
official Lean's normaliser does not. `eink0rn` will therefore *accept* files that
official Lean rejects on universe grounds. This is a deliberate,
thesis-faithful divergence in the permissive direction, and it is safe here
because the projection side condition of §5.3 is stated as an `imax` inequality
that the same complete procedure decides — so the extra power is used to close a
hole rather than to open one.

The place this is reachable from a file, rather than only from a term, is §8.4's
universe condition `imax(l', l) ≤ l` on an inductive whose own level `l` is a
variable or an `imax`. Three shapes it admits:

| declaration | field levels | conditions |
| --- | --- | --- |
| `W.{u} : Sort (max u 1) → Sort u` | `max u 1` | `imax (max u 1) u ≤ u` |
| `P.{u,v} : Sort (max u v) → Sort v → Sort (imax u v)` | `max u v`, `v` | `imax (max u v) (imax u v) ≤ imax u v`, `imax v (imax u v) ≤ imax u v` |
| `P.{u,v} : Sort u → Sort v → Sort (imax u v)` | `u`, `v` | `imax u (imax u v) ≤ imax u v`, `imax v (imax u v) ≤ imax u v` |

Every one of those inequalities holds under every assignment of the variables to
naturals, and the case split that proves it is the one `levelLeq` performs
anyway: split on whether the member's own level is zero. Where it is, the `imax`
on the left is `0` and the inequality is `0 ≤ 0`; where it is not, every `imax`
collapses to a `max` and what remains is true numerically — in row 1, `max u 1 ≤
u` is exactly the branch's own hypothesis `u ≥ 1`. A reading that will not split
on `u = 0` sees `max u 1 ≤ u` unguarded and refuses the declaration.

Admitting them is safe for the reason that makes the rule safe generally: a
universe-polymorphic declaration denotes the family of its instantiations, the
condition holds at each of them, and so each instantiation is one of the
monomorphic blocks §8 already admits. Nothing else in §8 loosens to match. In
particular the elimination decision does not: a member whose level is not
definitely nonzero gets large elimination only under §8.5's subsingleton clause,
which none of these satisfy, so each is admitted as the small-eliminating type
its own exported recursor declares it to be.

Two other places in a file reach the same procedure. A definition may state its
type in one spelling and its value in another — `fun x => x` at the type
`Sort (imax (max u v) w) → Sort (max (imax u w) (imax v w))` — and is accepted
because those are two spellings of one level, case split by case split. And
the uniform-universe requirement on a mutual block — now derived, by §9.3, from
the typing of the definitions that give the block's members back their names —
compares the members up to the level equivalence of §3 rather than syntactically,
so a block whose two members are declared at `max u v` and at `imax u (max u v)`
is one block rather than a heterogeneous one.

### 12.3 The quotient package is atomic

Quotient primitives are *checked* one at a time — each against the type §10
demands of its kind, stated over the type and constructor the file itself
declared. But the package is *admitted* whole or not at all: at the end of the
file, if any `quot` declaration appeared then there must be exactly one of each
of the four kinds `type`, `ctor`, `lift`, `ind`.

**Order within the package carries no meaning.** §10's expected types are stated
in terms of each other — `Quot.mk` lands in the quotient type, `Quot.ind`
quantifies over the class map — so a `quot` line that arrives before the sibling
its expected type needs is *held*, and retried when the next `quot` line arrives.
A file that writes `Quot.mk` before `Quot` is accepted, and every primitive is
still checked against the same expected type.

What is *not* deferred is the file's own dependency order. A held primitive is
retried only on another `quot` line, never at the end of the file, so the package
is admitted at the position of its last `quot` line and everything it borrows
from outside itself — `Quot.lift`'s premise mentions `Eq` (§12.1) — must have
been declared before that point, exactly as for any other declaration. A file
that puts `Quot.lift` ahead of `Eq` is rejected, with the reason the last attempt
gave.

This is a conformance rule, not a soundness rule, and the distinction matters
for auditing. Every proper fragment of the package is sound on its own — the
model of §10 interprets `Quot α r` as the set of equivalence classes and the two
eliminators as the functions that factor through it, and dropping an eliminator
only makes the type harder to use. Nothing is synthesised for a missing
primitive; a file with three of them proves strictly less than one with four.
The reason to reject it anyway is that the elaborator introduces the four
together and every real export carries them together, so three is a file
assembled by something that is not an exporter, and the cheapest honest response
is to say so rather than to proceed on a guess about the fourth.

The rule is stated on **kinds, not names**. Nothing in the theory cares what the
primitives are called: §10's expected types are built from the file's own
`type`- and `ctor`-kind declarations, so a package spelled `Q`, `Q.mk`, `Q.lift`,
`Q.ind` is still the package. What "exactly one" forbids is a *second* package,
or a second constructor for the same quotient type — the iota rule of §6.4 is
stated for one `ctor`, and two would make it ambiguous.

`Quot.sound` is deliberately outside this rule. It reaches the file as an
ordinary `axiom` line rather than a `quot` line, seven of the nine arena exports
that use quotients omit it entirely, and omitting it is a weakening. `--pin-std`
(§12.5) additionally audits the four *names*, which this rule does not.

### 12.4 Recursor names

The set of recursors a block may declare is pinned to `{T.rec}` plus the nesting
auxiliaries (§1). A block that named its recursor anything else would be
rejected even if the recursor were otherwise correct.

### 12.5 The standard-form audit (`--pin-std`)

Everything above is a rule about what the kernel is entitled to *do*. This one is
not: it decides nothing, it enables nothing, and with it off the checker's
verdicts are exactly what §1–§11 say they are. It answers a different question —
not "is this file consistent?" but "is this file about the things it appears to
be about?"

The motivation is that the three axioms Lean's mathematics rests on —
`Classical.choice`, `propext`, `Quot.sound` — are *asserted*, not proved. A kernel
cannot check them; it can only check that they are well-typed. But each is stated
over constants the file itself owns, so the way to weaken one is not to touch the
axiom at all. Leave it verbatim and redefine what it quantifies over. `propext`
over an `Iff` that is not bi-implication says nothing; `Classical.choice` over a
`Nonempty` that is not inhabitation says nothing; `Quot.sound` over an `Eq` that
is not equality says everything. Each such file is perfectly consistent and
perfectly sound — it is simply not about what its axiom names suggest.

`--pin-std` audits the transitive support of those three axioms, plus `False`
itself as the thing a smuggled definition would be aiming at:

| pinned | required to be |
| --- | --- |
| `False` | an inductive in `Prop`, no parameters, no indices, **no constructors** |
| `Eq` | `Eq.{u} : ∀ (α : Sort u), α → α → Prop`, two parameters and one index, with the single field-free constructor `Eq.refl.{u} : ∀ (α : Sort u) (a : α), Eq α a a` |
| `Iff` | `Iff : Prop → Prop → Prop` with the single constructor `Iff.intro`, two fields |
| `Nonempty` | `Nonempty.{u} : Sort u → Prop` with the single constructor `Nonempty.intro`, one field |
| `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` | quotient primitives of exactly those four kinds |
| `propext` | an axiom, no universe parameters, `∀ (a b : Prop), Iff a b → Eq.{1} Prop a b` |
| `Classical.choice` | an axiom, one universe parameter, `∀ {α : Sort u}, Nonempty α → α` |
| `Quot.sound` | an axiom, one universe parameter, `∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Eq (Quot r) (Quot.mk r a) (Quot.mk r b)` |

For an inductive the audit checks the universe-parameter count, parameter and
index counts, the constructor names *in order*, and `≡` on the type of the
inductive and of every constructor — that is, it checks strictly more than §12.1
does, and the extra it checks is exactly the identity information §12.1 rightly
declines to require. A name absent from the file is not audited; the audit is
about what a file says, not about what it omits.

The one thing checked that is not a per-name comparison: if a file declares any
of `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, it must declare all four. Note
that `Quot.sound` is *not* in that group. It is exported as an ordinary axiom
rather than as a quotient primitive, and appears only when something in the file
reaches it, so most exports that use quotients at all do not have it; requiring
it here would fire on perfectly ordinary files. The other four are introduced
together by the elaborator and exported together by every real export, and a file
with three of them has been edited by hand, whatever else is true of it.

Levels: `off` (the default) skips the audit entirely, `warn` reports mismatches on
stderr and accepts anyway, `error` rejects. `off` is the default because a
mismatch is not unsoundness — a file may legitimately define its own `Iff` for
reasons of its own — and a checker that conflated the two would be making a
claim it cannot support.

**Divergence.** Official Lean does not do this at all, so `--pin-std=error` can
reject files official Lean accepts. That is the intended behaviour of an opt-in
audit and not a claim about those files' consistency.

### 12.6 Arithmetic, in both directions

The licence discipline of §6.5 is the largest deliberate divergence in this
document, and it goes both ways. `eink0rn` computes on numerals when, and only
when, the file's own definitions say it may; a kernel that keys the same shortcut
on the name computes in a strictly different set of cases. Neither containment
holds.

*`eink0rn` accepts what a name-keyed kernel rejects.* Take a file that declares
`Nat.add` as something other than addition and then proves a theorem about it.
Its own definition is what `eink0rn` checks against, so the theorem goes through
if it is true of that definition. A kernel that substitutes machine addition for
the name is checking a different statement, and will report a contradiction that
is not in the file. Here `eink0rn` is not being lax: it is refusing to invent a
definitional equality the file never asserted.

*`eink0rn` rejects what a name-keyed kernel accepts.* This happens two ways, and
the first is what the whole discipline is for. Take the same file the other way
round: it defines `Nat.add` as `fun _ _ => 0` and then asserts `Nat.add 2 3 = 5`,
with `Eq.refl 5` as the proof. `eink0rn` checks the claim against the definition
the file gave, finds `0` against `5`, and rejects. A kernel that keys the
shortcut on the name computes `5` for the left-hand side and accepts — in an
environment where that same left-hand side unfolds to `0`. What the file has then
proved is `0 = 5`, and `Nat.noConfusion` turns that into `False`. The
redefinition does not have to be as blatant as this one, and it does not have to
be of `add`: the same file shape works for `sub`, `div`, `pow`, `beq` and `ble`,
and all that is really required is that whatever fixes the meaning of the
operation for the accelerator be something other than the environment the proof
is checked against. §6.5 is precisely the demand that those two never come apart,
and it is why this kernel can use machine arithmetic at all without also
maintaining a list of names it trusts.

The second way is a timeout rather than a verdict. An operation whose licence
does not check is not
accelerated and is unfolded instead, so a proof that a name-keyed kernel disposes
of in a machine multiplication is checked the slow way, and on the numerals such
proofs actually use it does not finish. `div` and `mod` are the interesting case,
because they are licensed on the weaker evidence of §6.5's probe battery: a file
whose `div` disagrees with division on any of the 185 probed pairs loses the
shortcut entirely, even for the pairs it gets right.

Both directions are mechanically reproducible. `--nat-accel=always` gives the
name-keyed behaviour exactly, so a file on which the two settings disagree
isolates the divergence to this rule and nothing else, and the disagreement can be
inspected rather than argued about. That is the entire reason an unsound mode is
shipped.

### 12.7 The unsafe fragment

The export format marks a declaration exempt from termination checking in two
places: `isUnsafe : bool` on `axiom`, `opaque`, `inductive` and its constructors
and recursors, and `safety : "safe" | "unsafe" | "partial"` on `def`. (`partial`
is `unsafe` with a friendlier surface syntax; the two are the same thing here.
`thm` has no such field: there is no unsafe theorem.) A declaration so marked was
accepted by the elaborator *without* the check that makes its type mean anything:

```
unsafe def loop : False := loop
```

is a well-formed input to the elaborator, and a proof of `False` to anything that
reads its type and ignores the flag.

So the flag is not erased with the other elaboration hints. It decides which of
two fragments the declaration joins.

**The unsafe fragment.** An unsafe declaration is admitted like this:

1. its declared type is checked to be a type;
2. it enters the environment as an **axiom** — so no rule of §6 ever unfolds it,
   and it contributes no definitional equalities;
3. its name is recorded in the environment's unsafe set;
4. its value, if it has one, is set aside and checked against its declared type
   **after the last line of the file**.

Step 4 is what makes the exemption precise. The exemption `unsafe` buys is
termination and nothing else, so the value is typechecked exactly as a safe one
would be — the only difference is *when*. By the end of the file every unsafe
constant is present as an axiom of its declared type, so `loop`'s body
typechecks (the `loop` on the right is the axiom), and so does a mutual group in
which `m01` calls `m02` and `m02` calls `m01`, for which no declaration order
works at all. Deferring is what stands in for the well-founded recursion the
elaborator did not demand. The check catches a call with the wrong number of
universe arguments, a reference to a constant the file never declares, and every
other way a body can be wrong that is not about termination.

An unsafe **inductive block** is admitted as a set of axioms: each type former,
each constructor and each recursor becomes an uninterpreted constant of its
declared type. Positivity is not checked — `UI.mk : (UI → UI) → UI` is exactly
what the marker exists to allow — no recursor is derived, and the declared
`rules`, `numParams`, `cidx` and `k` are discarded, because there is nothing left
to consult them. A recursor for a non-positive type is a proof of `False`
waiting to happen; here it is a name with a type and no reduction behaviour.

A block is unsafe *as a whole* or not at all: if the flags on its types,
constructors and recursors disagree, the file is rejected. There is no coherent
reading of a mixture. A safe constructor of an unsafe type is a safe way into the
unsafe fragment, and an unsafe constructor of a safe type would have the kernel
derive a recursor whose minor premises quantify over a constructor it has
quarantined.

**The barrier.** One rule connects the two fragments, and everything rests on it:

> A safe declaration may not mention an unsafe constant — not in its type, not
> in its value.

An unsafe constant is an axiom whose witness nobody checked, so it is exactly as
strong as its own statement: `loop : False` *is* a proof of `False` to anything
allowed to write it down. The unsafe fragment is therefore a separate,
presumed-inconsistent environment that the safe one cannot see, and the safe
fragment's soundness argument is unchanged from §5–§11.

Transitivity is free. If safe `A` mentions safe `B` which mentions unsafe `C`,
then `B` was rejected when it was read and `A` never gets its turn — so one
non-recursive scan of each declaration's own type and value is a complete check.
The scan covers `Expr.proj`, whose structure name is a reference to a declaration
just as a `const` node is. It does not need to cover numerals and string
literals: their typing and expansion rules (§5.2, §6.3) fire only against
constants that match a stored canonical *inductive* shape, and an unsafe `Nat` is
an axiom, which fails that test before the barrier is reached.

This costs nothing on faithful input. Every declaration in all 186 arena exports
carries `isUnsafe: false` and `safety: "safe"`.

**Divergence.** Official Lean keeps unsafe declarations in a separate
environment extension and enforces the same barrier, so a well-formed file
behaves the same way. Two differences remain: `eink0rn` requires an inductive
block's flags to be uniform, and it permits an unsafe declaration to refer
forward to a constant declared later in the file. The second is a consequence of
deferring, and restricting it would need the mutual group's membership taken on
trust from the `all` field while buying nothing — the safe fragment cannot see
any of these names either way.

### 12.8 The line schema is exact

Every line of the file is validated against the format before anything reads it.
A line is one JSON object; it carries exactly one *tag* naming what it is
(`str`, `num`, a level or expression constructor, `meta`, or one of the six
declaration kinds), pool lines carry exactly one index key (`in`, `il`, `ie`) and
declaration lines carry none, and the object under the tag has **exactly** the
key set the format defines for it — every key present, no key twice, and no key
besides. Enumerated fields (`binderInfo`, `safety`, `kind`, `hints`) must be one
of the spelled-out values. Every number is a natural: there is no field in the
format for which a negative has a reading.

This is stricter than a reader needs to be to get the right answer on a
well-formed file, and that is the point. A line carrying a field the format does
not define was not written by an exporter, and a reader that ignores it is
deciding on its own what the line meant. A *missing* field is worse, because then
every reader downstream invents a default — and the fields most likely to go
missing (`isUnsafe`, `binderInfo`, `safety`) are exactly the ones whose default a
forger would like to choose. Accepting a file has to mean accepting the file that
was written, not the largest sublanguage of it this checker happens to
understand.

The one exception is the `meta` header. Its sub-objects vary between real
exports and the kernel has no stake in any of them, so it is checked only to be a
lone well-formed `meta` line and is then discarded.

The erasures of §1 happen *after* this. `binderInfo`, `hints` and `mdata` are
required to be present and well-formed, and are then thrown away, because
"absent" and "present and irrelevant" are different claims about a file.

**Divergence.** Official Lean's reader is tolerant of extra and missing fields
in places where the value does not change its behaviour.

### 12.9 Redundant bookkeeping must be true

Several fields restate something the kernel derives for itself. The format calls
`isRec` and `isReflexive` "informational"; no rule in this kernel reads either
off the file. They are checked anyway, on the principle of §1: a number or flag
the export supplies and nobody verifies is a place where a file can say one thing
and mean another, and the cost of closing it is one comparison.

| field | derived from |
| --- | --- |
| `numParams`, `numIndices`, `numFields`, `numMotives`, `numMinors`, `nfields` | the telescopes of §8.3–§8.7 |
| `all` | the members of the block |
| `isRec` | some constructor of the block has a recursive field |
| `isReflexive` | some constructor has a recursive field *under a binder*, as `Acc.intro`'s `forall y, r y x → Acc r y` does |
| `k` | §8.6 |
| the recursor's type and rules | re-derived outright (§8.8) |

`isRec` and `isReflexive` are read as describing the **block**, not the member.
The two readings differ only on a mutual block — a member with no recursive field
of its own inside a block that has one — and the block reading is the one that
means something: the members of a block are admitted together and their
recursors call each other, so that member's recursor recurses whether or not its
own constructors do. Every member of a recursive block is therefore required to
declare `isRec = true`, and likewise for `isReflexive`. Nesting auxiliaries count
towards the block's answer, but they have no `isRec` field of their own to check.

Agreement was confirmed on every inductive declaration in the arena corpus,
including the 654,504-declaration `mathlib` export.

**Divergence.** Official Lean recomputes these fields and overwrites them rather
than comparing, so a file whose bookkeeping is wrong is accepted there and
rejected here.

### 12.10 Proof bodies are sealed

A checked theorem normally enters the environment as a definition, and a
definition delta-unfolds. This kernel instead **discards the proof and admits an
axiom** whenever it can show that no reduction rule could ever look inside it.
`--keep-proofs` turns this off; it changes nothing but the timings.

The argument is that a proof is used in exactly three ways, and each one can be
ruled out from the *statement* alone.

- **Compared with another term.** Never needs the value. A proof can only be
  convertible with another proof, and §7 step 5 settles any comparison between
  two proofs from their types. Sealing a proof does not even weaken step 4: an
  axiom is a rigid head, so `thm ā ≡ thm b̄` still goes through congruence.
- **Major premise of a recursor.** This is the case that can need the value, so
  it is the one the test is about.
- **Target of a projection.** Same, and it reduces to the same test.

Write `C` for the head of the statement's conclusion, after stripping its
`forall`s and head-normalising. The proof is sealed when `C` is an inductive type
and any of:

| condition | why nothing can be waiting on the value | examples |
| --- | --- | --- |
| `C` has no constructors | there is no iota rule to fire and no field to project | `False`, `Empty` |
| `C` does not admit large elimination (§8.5) | `C.rec`'s motive lands in `Prop`, so every term a stuck `C.rec` blocks is *itself* a proof, and step 5 answers for it. A projection is in the same position: §5.3 only admits one whose field is a proof, and a type with a data field is exactly a type that does not eliminate largely | `Or`, `Exists`, `Nonempty`, `Nat.le` |
| `C` has the `k` flag (§8.6) | K-like reduction rebuilds the constructor application from the major premise's *type*, so iota fires with the value untouched | `Eq`, `HEq`, `True` |

Anything else is kept — including a conclusion that is a variable, a sort, a
quotient, or a constant that head normalisation could not resolve.

One class *must* be kept, and it is worth naming: a `Prop` that eliminates
largely **and** has fields is one whose recursor needs to see a real constructor
before it can produce the data it promised. `Acc` is the important one — sealing
a proof of `Acc r a` would stop well-founded recursion from unfolding — and
`And`, `Iff` and `WellFounded` have the same shape. Structure eta (§7.2) does not
rescue them: it replaces the major premise with `C.mk h.[C,0] .. h.[C,n]`, whose
fields are projections that are themselves stuck on the value we would have
thrown away.

This is a completeness claim, not a soundness one, and it is one-sided in the
safe direction either way: a proof that should have been kept can only cause a
reduction to get stuck, and a stuck reduction can only cause a rejection (§7.3).

**Divergence.** None observed. Official Lean keeps theorem values, so a file that
this kernel rejects for want of an unfolding it sealed away would be a
divergence; none of the arena corpus, the pathological corpus, or `init`
contains one.

### 12.11 Reducibility hints are believed

The `hints` field of a `def` is the one thing this kernel reads out of the file
and does not check. It is safe to read precisely because there is nothing to
check: it orders `isDefEq`'s step 6, and **the order in which two definitions are
unfolded cannot change which terms are convertible**. When neither side wins,
both are unfolded; when one wins, unfolding it still makes progress, and the
environment is acyclic, so every ordering — including a deliberately perverse
one — decides the same questions. It decides them at very different speeds, and
that is the whole of what a hint is for.

The order, greatest first:

| hint | priority | meaning |
| --- | --- | --- |
| `abbrev` | highest | the elaborator judged this too thin to be worth keeping folded |
| `regular n` | by `n` | `n` exceeds the height of everything the value mentions, so unfolding the taller of two constants is what lets the shorter be reached from both sides |
| `opaque` | lowest | leave this one alone |

A `thm` carries no `hints` field, and one that survives §12.10 is given `opaque`:
a proof is the last thing worth looking inside.

Earlier versions computed the height themselves, as `1 + max` over the
definitions a value mentions. That agrees with `regular n` on every export
`lean4export` produces, but it costs a traversal of every value in the file and
it has no answer for `abbrev`.

**Divergence.** None possible. Two runs that differ only in this field accept and
reject exactly the same files.

### 12.12 Nesting at a fixed index

§9 compiles a nested occurrence away by specialising the container at the
arguments it was actually applied to. Nothing in that construction asks where
those arguments came from, and in particular it does not ask that the block
member appear at the family's own index variables. So an indexed family that
nests itself at a *constant* index —

```
T : Nat -> Type
T.leaf : T 0
T.node : (n : Nat) -> List (T 0) -> T 0
```

— is compiled exactly as a nested occurrence at a variable index would be. §9.1
discovers `List (T 0)` (the container's parameter is closed with respect to bound
variables, and a member occurs in it), adds one auxiliary member for it with
`nil`- and `cons`-shaped constructors, and rewrites `T.node`'s field to mention
the auxiliary. What reaches §9.3 is the flat mutual block `T` together with that
auxiliary, and what reaches §8 is that block flattened. Its `cons` field is
`T 0`: a recursive occurrence of a block member, applied to an index in which no
member of the block occurs, which is exactly and all that §8.4 asks of the
flattened family. The block is strictly positive, it is admitted with no
special case, and the two recursors the file declares are checked against the two
the construction derives.

The soundness argument is §9.2's, unchanged, because the construction is
unchanged. The auxiliary is an ordinary inductive type — `List` specialised at
one closed type — the flat block is an ordinary mutual inductive, and the
recursor is the one §8.7 derives from that block, re-typechecked in the final
environment by §9.1's last step.
A constant index is not a weaker input to any of this than a variable one; if
anything it is a more specific one.

The divergence, then, is permissive and this kernel is on the right side of it:
files of this shape are sound and are accepted. A nesting compiler that
recognises the occurrence only when the member appears applied to the family's
own indices sees `T 0` as something other than the family and refuses. `eink0rn`
never needs that recognition, because it never re-uses the container's own
recursor for the specialised copy — it builds a fresh member and derives
everything about it from scratch.

One detail of the same family is worth naming separately, because it is a
divergence about equality rather than about nesting. A constructor may state its
result index as a closed term that is only *convertible* to the index the
recursor's minor premises use — `T.node ... : T (List.length [])` against a
recursor written at `T 0`. §8.4 asks only that the family not occur in the index, so the constructor is analysed as written; the derived recursor
carries `List.length []` where the export carries `0`; and §8.8 compares the two
up to definitional equality, which is what the rest of this kernel does
everywhere else and what makes the comparison meaningful rather than syntactic.

### 12.13 A proof is not a constructor

`Acc r a` is a proposition, so by §7's proof irrelevance any two of its
inhabitants are convertible, and it is tempting to let a *variable* proof
`a : Acc r n` stand in for a constructor application `Acc.intro n h` and so let
`Acc.rec` fire on it. This kernel does not. §6.3 lists the three ways a
non-constructor major premise becomes usable and `Acc` qualifies for none of
them: its recursor is not `k`-like, and the type is recursive, which rules out
eta on the major premise for the termination reason given there. A definition by
well-founded recursion therefore does not unfold when applied to a proof whose
shape it cannot see, and a file that asks for `f 1 a = f 0 (Acc.inv a h)` to hold
by `Eq.refl`, with `a` a bound variable, is rejected.

This is the restrictive direction, and the restriction is the right one. Firing
the rule would mean inventing the constructor's fields — here the `h` that
`Acc.intro` carries — and different inventions compute different results.
Irrelevance makes the proofs *equal*; it does not make them *known*, and a
recursor eliminating out of `Prop` (§8.5) is precisely a place where the
difference is observable. Well-founded definitions still compute wherever their
`Acc` argument is a closed term, which is every place in the arena corpus where
one is asked to.
