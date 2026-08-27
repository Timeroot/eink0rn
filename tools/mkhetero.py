#!/usr/bin/env python3
"""Write .ndjson exports for heterogeneous-universe mutual inductive blocks.

lean4export can never emit one: the elaborator refuses the block long before the
export runs.  So the material SPEC.md §9.6 is tested against has to be written by
hand, and this is the writer.

Terms are built in a named IR and converted to de Bruijn on the way out; the
three pools are filled on demand and shared by content.  A block is described by
its members, and the constructor types, the recursor types and every iota rule
are derived from that description with the same conventions §8.7 uses -- all
fields, then one induction hypothesis per recursive field in field order.

    python3 tools/mkhetero.py [outdir]      # default: tests

writes <outdir>/good/hetero-*.ndjson and <outdir>/bad/hetero-*.ndjson.
"""

import json
import os
import sys

# -- levels ---------------------------------------------------------------------

ZERO = ("zero",)


def P(n):
    return ("param", n)


def SUCC(l):
    return ("succ", l)


def MAX(a, b):
    return ("max", a, b)


def IMAX(a, b):
    return ("imax", a, b)


def TYPE(k):
    """The level of `Type k`, i.e. `Sort (k+1)`."""
    l = ZERO
    for _ in range(k + 1):
        l = SUCC(l)
    return l


PROP = ZERO


def nonzero(l):
    """SPEC §8.5 case 1: is this level nonzero under every assignment?"""
    if l[0] == "succ":
        return True
    if l[0] == "max":
        return nonzero(l[1]) or nonzero(l[2])
    if l[0] == "imax":
        return nonzero(l[2])
    return False


# -- expressions ----------------------------------------------------------------

_fresh = [0]


def fresh(prefix="x"):
    _fresh[0] += 1
    return "%s%d" % (prefix, _fresh[0])


def S(l):
    return ("sort", l)


def K(n, us=()):
    return ("const", n, tuple(us))


def V(n):
    return ("var", n)


def A(f, *args):
    e = f
    for a in args:
        e = ("app", e, a)
    return e


def PI(n, t, b):
    return ("pi", n, t, b)


def LAM(n, t, b):
    return ("lam", n, t, b)


def ARROW(t, b):
    return PI(fresh("_"), t, b)


def PIS(tele, body):
    for n, t in reversed(list(tele)):
        body = PI(n, t, body)
    return body


def LAMS(tele, body):
    for n, t in reversed(list(tele)):
        body = LAM(n, t, body)
    return body


# -- the writer -----------------------------------------------------------------

META = {
    "exporter": {"name": "tools/mkhetero.py", "version": "3.1.0"},
    "format": {"version": "3.1.0"},
    "lean": {"githash": "0" * 40, "version": "4.29.1"},
}


class Out(object):
    def __init__(self):
        self.lines = [json.dumps({"meta": META}, sort_keys=True)]
        self.names = {(): 0}
        self.levels = {ZERO: 0}
        self.exprs = {}
        self._n = 1
        self._l = 1
        self._e = 0

    # pools
    def name(self, s):
        return self._name(tuple(s.split(".")) if s else ())

    def _name(self, parts):
        if parts in self.names:
            return self.names[parts]
        pre = self._name(parts[:-1])
        i = self._n
        self._n += 1
        self.names[parts] = i
        self.lines.append(
            json.dumps({"in": i, "str": {"pre": pre, "str": parts[-1]}}))
        return i

    def level(self, l):
        if l in self.levels:
            return self.levels[l]
        t = l[0]
        if t == "succ":
            body = {"succ": self.level(l[1])}
        elif t == "max":
            body = {"max": [self.level(l[1]), self.level(l[2])]}
        elif t == "imax":
            body = {"imax": [self.level(l[1]), self.level(l[2])]}
        elif t == "param":
            body = {"param": self.name(l[1])}
        else:
            raise ValueError(l)
        i = self._l
        self._l += 1
        self.levels[l] = i
        body["il"] = i
        self.lines.append(json.dumps(body, sort_keys=True))
        return i

    def expr(self, tag, payload):
        key = (tag, json.dumps(payload, sort_keys=True))
        if key in self.exprs:
            return self.exprs[key]
        i = self._e
        self._e += 1
        self.exprs[key] = i
        self.lines.append(json.dumps({tag: payload, "ie": i}, sort_keys=True))
        return i

    # terms
    def conv(self, e, ctx=()):
        t = e[0]
        if t == "var":
            ctx = list(ctx)
            for i in range(len(ctx) - 1, -1, -1):
                if ctx[i] == e[1]:
                    return self.expr("bvar", len(ctx) - 1 - i)
            raise KeyError("unbound variable %r" % (e[1],))
        if t == "sort":
            return self.expr("sort", self.level(e[1]))
        if t == "const":
            return self.expr("const", {"name": self.name(e[1]),
                                       "us": [self.level(u) for u in e[2]]})
        if t == "app":
            return self.expr("app", {"fn": self.conv(e[1], ctx),
                                     "arg": self.conv(e[2], ctx)})
        if t in ("pi", "lam"):
            _, n, ty, body = e
            ti = self.conv(ty, ctx)
            bi = self.conv(body, list(ctx) + [n])
            return self.expr("forallE" if t == "pi" else "lam",
                             {"name": self.name(n), "type": ti, "body": bi,
                              "binderInfo": "default"})
        raise ValueError(e)

    # declarations
    def decl(self, tag, payload):
        self.lines.append(json.dumps({tag: payload}, sort_keys=True))

    def axiom(self, name, lvls, ty):
        self.decl("axiom", {"name": self.name(name),
                            "levelParams": [self.name(l) for l in lvls],
                            "type": self.conv(ty),
                            "isUnsafe": False})

    def write(self, path):
        with open(path, "w") as h:
            h.write("\n".join(self.lines) + "\n")


# -- blocks ---------------------------------------------------------------------
#
# A member is
#   {"name": str, "indices": [(nm, ty)], "sort": level, "ctors": [ctor]}
# a constructor is
#   {"name": str, "fields": [field], "idx": [expr]}
# and a field is either
#   ("plain", nm, ty)                       or
#   ("rec", nm, member, [(nm, ty)], [expr])
# the latter standing for `forall xi, t_member params idx`.


def plain(nm, ty):
    return ("plain", nm, ty)


def rec(nm, member, xis=(), idx=()):
    return ("rec", nm, member, list(xis), list(idx))


def emit_block(out, blk, bad=()):
    """Emit one `inductive` declaration line for the block."""
    lvls = blk.get("levels", [])
    params = blk.get("params", [])
    ms = blk["members"]
    us = [P(l) for l in lvls]
    nps = len(params)
    names = [m["name"] for m in ms]
    pv = [V(n) for n, _ in params]
    nctors = [len(m["ctors"]) for m in ms]

    def field_ty(f):
        if f[0] == "plain":
            return f[2]
        _, _, mem, xis, idx = f
        return PIS(xis, A(K(mem, us), *pv, *idx))

    def field_tele(c):
        return [(f[1], field_ty(f)) for f in c["fields"]]

    def ctor_ty(i, c):
        return PIS(params, PIS(field_tele(c),
                               A(K(names[i], us), *pv, *c["idx"])))

    # -- the types and the constructors
    is_rec = any(f[0] == "rec" for m in ms for c in m["ctors"] for f in c["fields"])
    is_refl = any(f[0] == "rec" and f[3]
                  for m in ms for c in m["ctors"] for f in c["fields"])
    if "refl" in bad:
        is_refl = not is_refl

    types = []
    ctors = []
    for i, m in enumerate(ms):
        types.append({
            "name": out.name(m["name"]),
            "levelParams": [out.name(l) for l in lvls],
            "type": out.conv(PIS(params, PIS(m["indices"], S(m["sort"])))),
            "numParams": nps,
            "numIndices": len(m["indices"]),
            "all": [out.name(x) for x in names],
            "ctors": [out.name(c["name"]) for c in m["ctors"]],
            "numNested": 0,
            "isRec": is_rec,
            "isReflexive": is_refl,
            "isUnsafe": False,
        })
        for k, c in enumerate(m["ctors"]):
            ctors.append({
                "name": out.name(c["name"]),
                "levelParams": [out.name(l) for l in lvls],
                "type": out.conv(ctor_ty(i, c)),
                "induct": out.name(m["name"]),
                "cidx": k,
                "numParams": nps,
                "numFields": len(c["fields"]),
                "isUnsafe": False,
            })

    # -- the elimination universe (SPEC §8.5 case 1, member by member)
    large = [nonzero(m["sort"]) for m in ms]
    elim = "u"
    while elim in lvls:
        elim = elim + "'"
    reclps = ([elim] + lvls) if any(large) else list(lvls)
    recus = [P(x) for x in reclps]

    def elim_lvl(i):
        if "motive" in bad and not large[i]:
            return P(elim) if any(large) else SUCC(ZERO)
        return P(elim) if large[i] else ZERO

    # -- the motives and minor premises, shared by every recursor of the block
    mvs = ["motive_%d" % (i + 1) for i in range(len(ms))]
    motive_tele = []
    for i, m in enumerate(ms):
        kappa = PIS(m["indices"],
                    ARROW(A(K(names[i], us), *pv, *[V(n) for n, _ in m["indices"]]),
                          S(elim_lvl(i))))
        motive_tele.append((mvs[i], kappa))

    def ihs_of(c, build):
        out_ = []
        for f in c["fields"]:
            if f[0] != "rec":
                continue
            _, nm, mem, xis, idx = f
            j = names.index(mem)
            out_.append(build(nm, j, xis, idx))
        return out_

    evs = []
    minor_tele = []
    for i, m in enumerate(ms):
        for k, c in enumerate(m["ctors"]):
            nm = "minor_%d_%d" % (i + 1, k + 1)
            ihts = ihs_of(c, lambda fn, j, xis, idx: PIS(
                xis, A(V(mvs[j]), *idx, A(V(fn), *[V(x) for x, _ in xis]))))
            body = A(V(mvs[i]), *c["idx"],
                     A(K(c["name"], us), *pv, *[V(f[1]) for f in c["fields"]]))
            eps = PIS(field_tele(c),
                      PIS([("ih_%d" % (q + 1), t) for q, t in enumerate(ihts)], body))
            evs.append(nm)
            minor_tele.append((nm, eps))

    prefix = list(params) + motive_tele + minor_tele

    # -- one recursor per member
    recs = []
    for i, m in enumerate(ms):
        ivs = [V(n) for n, _ in m["indices"]]
        major = A(K(names[i], us), *pv, *ivs)
        concl = PIS(m["indices"], PI("t", major, A(V(mvs[i]), *ivs, V("t"))))
        rules = []
        for k, c in enumerate(m["ctors"]):
            absk = sum(nctors[:i]) + k
            if "iota" in bad:
                absk = 0
            ihs = ihs_of(c, lambda fn, j, xis, idx: LAMS(
                xis, A(K(names[j] + ".rec", recus), *pv,
                       *[V(x) for x in mvs], *[V(x) for x in evs], *idx,
                       A(V(fn), *[V(x) for x, _ in xis]))))
            rhs = LAMS(prefix,
                       LAMS(field_tele(c),
                            A(V(evs[absk]), *[V(f[1]) for f in c["fields"]], *ihs)))
            rules.append({"ctor": out.name(c["name"]),
                          "nfields": len(c["fields"]),
                          "rhs": out.conv(rhs)})
        recs.append({
            "name": out.name(names[i] + ".rec"),
            "levelParams": [out.name(x) for x in reclps],
            "type": out.conv(PIS(prefix, concl)),
            "all": [out.name(x) for x in names],
            "numParams": nps,
            "numIndices": len(m["indices"]),
            "numMotives": len(ms),
            "numMinors": sum(nctors),
            "rules": rules,
            "k": False,
            "isUnsafe": False,
        })

    out.decl("inductive", {"types": types, "ctors": ctors, "recs": recs})


# -- a prelude the examples draw on ---------------------------------------------

NAT = {
    "members": [{
        "name": "Nat", "indices": [], "sort": TYPE(0),
        "ctors": [
            {"name": "Nat.zero", "fields": [], "idx": []},
            {"name": "Nat.succ", "fields": [rec("n", "Nat")], "idx": []},
        ],
    }],
}


def prelude(out, lt=False):
    emit_block(out, NAT)
    if lt:
        out.axiom("Lt", [], ARROW(K("Nat"), ARROW(K("Nat"), S(PROP))))


# -- the cases ------------------------------------------------------------------

def two_member():
    """§6 of the design note: the two-member minimum.

        mutual inductive G : Prop | base | fromH (h : H)
               inductive H : Type 1 | mk (g : G)
    """
    return {"members": [
        {"name": "G", "indices": [], "sort": PROP, "ctors": [
            {"name": "G.base", "fields": [], "idx": []},
            {"name": "G.fromH", "fields": [rec("h", "H")], "idx": []}]},
        {"name": "H", "indices": [], "sort": TYPE(1), "ctors": [
            {"name": "H.mk", "fields": [rec("g", "G")], "idx": []}]},
    ]}


def three_member():
    """§7: three members, real payloads, a data-to-data edge across the gap."""
    return {"members": [
        {"name": "A", "indices": [], "sort": PROP, "ctors": [
            {"name": "A.fromB", "fields": [rec("b", "B")], "idx": []},
            {"name": "A.fromC", "fields": [rec("c", "C")], "idx": []}]},
        {"name": "B", "indices": [], "sort": TYPE(0), "ctors": [
            {"name": "B.fromA",
             "fields": [plain("n", K("Nat")), rec("a", "A")], "idx": []},
            {"name": "B.wrap", "fields": [rec("b", "B")], "idx": []}]},
        {"name": "C", "indices": [], "sort": TYPE(2), "ctors": [
            {"name": "C.fromA", "fields": [rec("a", "A")], "idx": []},
            {"name": "C.higherUniv",
             "fields": [plain("n", K("Nat")), plain("t", S(TYPE(0)))],
             "idx": []},
            {"name": "C.pair", "fields": [rec("b", "B"), rec("c", "C")],
             "idx": []}]},
    ]}


def indexed_prop():
    """§8: an indexed, Acc-shaped Prop member beside a Type 3 one."""
    return {"members": [
        {"name": "WA", "indices": [("i", K("Nat"))], "sort": PROP, "ctors": [
            {"name": "WA.intro",
             "fields": [plain("n", K("Nat")),
                        rec("h", "WA",
                            [("m", K("Nat")),
                             ("lt", A(K("Lt"), V("m"), V("n")))],
                            [V("m")])],
             "idx": [V("n")]},
            {"name": "WA.fromV", "fields": [rec("v", "V")],
             "idx": [K("Nat.zero")]}]},
        {"name": "V", "indices": [], "sort": TYPE(3), "ctors": [
            {"name": "V.mk",
             "fields": [plain("n", K("Nat")), rec("w", "WA", [], [V("n")])],
             "idx": []},
            {"name": "V.num", "fields": [plain("k", K("Nat"))], "idx": []}]},
    ]}


def polymorphic():
    """A Prop member cycling with a data member at a universe parameter."""
    return {"levels": ["v"], "members": [
        {"name": "PP", "indices": [], "sort": PROP, "ctors": [
            {"name": "PP.mk", "fields": [rec("d", "DD")], "idx": []}]},
        {"name": "DD", "indices": [], "sort": SUCC(P("v")), "ctors": [
            {"name": "DD.mk", "fields": [rec("p", "PP")], "idx": []}]},
    ]}


def disjoint_data():
    """Heterogeneous with no Prop member at all: two unrelated data SCCs."""
    return {"members": [
        {"name": "XX", "indices": [], "sort": TYPE(0), "ctors": [
            {"name": "XX.z", "fields": [], "idx": []},
            {"name": "XX.s", "fields": [rec("x", "XX")], "idx": []}]},
        {"name": "YY", "indices": [], "sort": TYPE(1), "ctors": [
            {"name": "YY.z", "fields": [plain("t", S(TYPE(0)))], "idx": []},
            {"name": "YY.s", "fields": [rec("y", "YY")], "idx": []}]},
    ]}


def parameterised():
    """The same shape, carrying a parameter through both members."""
    return {"params": [("al", S(TYPE(0)))], "members": [
        {"name": "QP", "indices": [], "sort": PROP, "ctors": [
            {"name": "QP.mk", "fields": [rec("d", "QD")], "idx": []}]},
        {"name": "QD", "indices": [], "sort": TYPE(0), "ctors": [
            {"name": "QD.mk",
             "fields": [plain("a", V("al")), rec("p", "QP")], "idx": []}]},
    ]}


def choice_gap():
    """A functional recursive field from a Prop member into a data member.

    Rebuilding the Prop recursor's minor premise would need choice: the shadow
    hands back `forall n, Sig (D) (motive)` and the block's minor wants
    `forall n, D`.  §9.6 declines it.
    """
    return {"members": [
        {"name": "GP", "indices": [], "sort": PROP, "ctors": [
            {"name": "GP.mk",
             "fields": [rec("f", "GD", [("n", K("Nat"))], [])], "idx": []}]},
        {"name": "GD", "indices": [], "sort": TYPE(0), "ctors": [
            {"name": "GD.mk", "fields": [rec("p", "GP")], "idx": []}]},
    ]}


def data_cycle():
    """A data-data cycle whose members are at different levels: ill-typed."""
    return {"members": [
        {"name": "CX", "indices": [], "sort": TYPE(0), "ctors": [
            {"name": "CX.mk", "fields": [rec("y", "CY")], "idx": []}]},
        {"name": "CY", "indices": [], "sort": TYPE(1), "ctors": [
            {"name": "CY.mk", "fields": [rec("x", "CX")], "idx": []}]},
    ]}


def bad_field():
    """Heterogeneous, and one member breaks §8.4's own field condition."""
    return {"members": [
        {"name": "FP", "indices": [], "sort": PROP, "ctors": [
            {"name": "FP.mk", "fields": [rec("d", "FD")], "idx": []}]},
        {"name": "FD", "indices": [], "sort": TYPE(0), "ctors": [
            {"name": "FD.mk",
             "fields": [plain("t", S(TYPE(0))), rec("p", "FP")], "idx": []}]},
    ]}


CASES = [
    # (verdict, name, block, prelude-needs-Lt, doctoring)
    ("good", "hetero-two-member", two_member, None, ()),
    ("good", "hetero-three-member", three_member, "nat", ()),
    ("good", "hetero-indexed-prop", indexed_prop, "lt", ()),
    ("good", "hetero-polymorphic", polymorphic, None, ()),
    ("good", "hetero-disjoint-data", disjoint_data, None, ()),
    ("good", "hetero-parameterised", parameterised, None, ()),
    ("bad", "hetero-choice-gap", choice_gap, "nat", ()),
    ("bad", "hetero-data-cycle", data_cycle, None, ()),
    ("bad", "hetero-bad-field", bad_field, None, ()),
    ("bad", "hetero-large-prop-motive", two_member, None, ("motive",)),
    ("bad", "hetero-wrong-iota", three_member, "nat", ("iota",)),
    ("bad", "hetero-wrong-reflexive", indexed_prop, "lt", ("refl",)),
]


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "tests"
    for verdict, name, mk, pre, bad in CASES:
        out = Out()
        if pre:
            prelude(out, lt=(pre == "lt"))
        emit_block(out, mk(), bad=bad)
        d = os.path.join(root, verdict)
        os.makedirs(d, exist_ok=True)
        path = os.path.join(d, name + ".ndjson")
        out.write(path)
        print(path)


if __name__ == "__main__":
    main()
