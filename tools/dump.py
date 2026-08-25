#!/usr/bin/env python3
"""Human-readable dump of a lean4export .ndjson file. Debug aid only."""
import json, sys

def load(path):
    names={0:"[anon]"}; levels={0:"0"}; exprs={}; decls=[]; meta=None
    raw_e={}
    for line in open(path):
        line=line.strip()
        if not line: continue
        o=json.loads(line)
        if "meta" in o and "ie" not in o: meta=o["meta"]; continue
        if "in" in o:
            i=o["in"]
            if "str" in o:
                p=o["str"]["pre"]; s=o["str"]["str"]
                names[i]=s if p==0 else names.get(p,"?%d"%p)+"."+s
            else:
                p=o["num"]["pre"]; s=str(o["num"]["i"])
                names[i]=s if p==0 else names.get(p,"?%d"%p)+"."+s
            continue
        if "il" in o:
            i=o["il"]
            if "succ" in o: levels[i]="(%s+1)"%levels.get(o["succ"],"?")
            elif "max" in o: a,b=o["max"]; levels[i]="max(%s,%s)"%(levels.get(a,"?"),levels.get(b,"?"))
            elif "imax" in o: a,b=o["imax"]; levels[i]="imax(%s,%s)"%(levels.get(a,"?"),levels.get(b,"?"))
            elif "param" in o: levels[i]=names.get(o["param"],"?")
            continue
        if "ie" in o: raw_e[o["ie"]]=o; continue
        decls.append(o)
    return meta,names,levels,raw_e,decls

def mkpp(names,levels,raw_e):
    memo={}
    def pp(i,binders=()):
        o=raw_e.get(i)
        if o is None: return "<missing e%d>"%i
        if "bvar" in o:
            k=o["bvar"]
            return binders[k] if k<len(binders) else "#%d"%k
        if "sort" in o: return "Sort %s"%levels.get(o["sort"],"?")
        if "const" in o:
            c=o["const"]; us=c["us"]
            n=names.get(c["name"],"?")
            return n+(".{%s}"%",".join(levels.get(u,"?") for u in us) if us else "")
        if "app" in o:
            a=o["app"]; return "(%s %s)"%(pp(a["fn"],binders),pp(a["arg"],binders))
        if "lam" in o or "forallE" in o:
            k="lam" if "lam" in o else "forallE"
            b=o[k]; nm=names.get(b["name"],"_"); nm=nm if nm!="[anon]" else "_"
            nm=nm.split("._@")[0]
            sym="fun" if k=="lam" else "forall"
            return "(%s (%s : %s), %s)"%(sym,nm,pp(b["type"],binders),pp(b["body"],(nm,)+binders))
        if "letE" in o:
            b=o["letE"]; nm=names.get(b["name"],"_").split("._@")[0]
            return "(let %s : %s := %s; %s)"%(nm,pp(b["type"],binders),pp(b["value"],binders),pp(b["body"],(nm,)+binders))
        if "proj" in o:
            p=o["proj"]; return "(%s.proj%d %s)"%(names.get(p["typeName"],"?"),p["idx"],pp(p["struct"],binders))
        if "natVal" in o: return "lit#%s"%o["natVal"]
        if "strVal" in o: return "lit%r"%o["strVal"]
        if "mdata" in o: return pp(o["mdata"]["expr"],binders)
        return "<?%s>"%list(o)
    return pp

def main(path, only=None):
    meta,names,levels,raw_e,decls=load(path)
    pp=mkpp(names,levels,raw_e)
    N=lambda i: names.get(i,"?%d"%i)
    L=lambda ls: (".{%s}"%",".join(N(x) for x in ls)) if ls else ""
    for d in decls:
        k=next(iter(d)); v=d[k]
        if only and k!=only: continue
        if k in ("axiom",):
            print("axiom %s%s : %s"%(N(v["name"]),L(v["levelParams"]),pp(v["type"])))
        elif k in ("def","thm","opaque"):
            print("%s %s%s : %s :=\n    %s"%(k,N(v["name"]),L(v["levelParams"]),pp(v["type"]),pp(v["value"]) if "value" in v else "<none>"))
        elif k=="quot":
            print("quot[%s] %s%s : %s"%(v["kind"],N(v["name"]),L(v["levelParams"]),pp(v["type"])))
        elif k=="inductive":
            print("inductive-block:")
            for t in v["types"]:
                print("  type %s%s : %s"%(N(t["name"]),L(t["levelParams"]),pp(t["type"])))
                print("    numParams=%d numIndices=%d numNested=%d isRec=%s isRefl=%s all=%s ctors=%s"%(
                    t["numParams"],t["numIndices"],t["numNested"],t["isRec"],t["isReflexive"],
                    [N(x) for x in t["all"]],[N(x) for x in t["ctors"]]))
            for c in v["ctors"]:
                print("  ctor %s%s : %s"%(N(c["name"]),L(c["levelParams"]),pp(c["type"])))
                print("    induct=%s cidx=%d numParams=%d numFields=%d"%(N(c["induct"]),c["cidx"],c["numParams"],c["numFields"]))
            for r in v["recs"]:
                print("  rec %s%s : %s"%(N(r["name"]),L(r["levelParams"]),pp(r["type"])))
                print("    nParams=%d nIndices=%d nMotives=%d nMinors=%d k=%s all=%s"%(
                    r["numParams"],r["numIndices"],r["numMotives"],r["numMinors"],r["k"],[N(x) for x in r["all"]]))
                for rl in r["rules"]:
                    print("    | %s (nfields=%d) => %s"%(N(rl["ctor"]),rl["nfields"],pp(rl["rhs"])))
        print()

if __name__=="__main__":
    main(sys.argv[1], sys.argv[2] if len(sys.argv)>2 else None)
