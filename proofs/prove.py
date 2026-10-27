#!/usr/bin/env python3
"""Discharge every lemma in lemmas.json with two independent backends
(CBMC's SAT backend and Z3 via SMT-LIB2). A lemma is PROVED only when
both backends report VERIFICATION SUCCESSFUL with unwinding assertions on."""
import json, subprocess, sys, time, re, os, resource
# Memory safety for the host: few workers, hard per-process address-space cap.
WORKERS = int(os.environ.get("PROVE_JOBS", "2"))
MEM_GB = int(os.environ.get("PROVE_MEM_GB", "4"))

def _limit():
    b = MEM_GB << 30
    resource.setrlimit(resource.RLIMIT_AS, (b, b))
from concurrent.futures import ThreadPoolExecutor
ROOT = os.path.dirname(os.path.abspath(__file__))
# proofs/ lives at the top of the ngtcp2 tree (../lib); fall back to a
# sibling checkout at ../src/lib for out-of-tree use.
SRC = next(p for p in (os.path.join(ROOT, "..", "lib"),
                       os.path.join(ROOT, "..", "src", "lib"))
           if os.path.isdir(p))
FLAGS = ["--bounds-check", "--pointer-check", "--signed-overflow-check",
         "--pointer-overflow-check", "--undefined-shift-check",
         "--div-by-zero-check", "--unwinding-assertions", "--object-bits", "12"]
BACKENDS = {"sat": ["--external-sat-solver", "cadical", "--slice-formula"], "z3": ["--z3", "--slice-formula"]}

def key(l):
    return l.get("id", l["name"])

def run(lemma, backend, timeout):
    cmd = ["cbmc", "--function", "harness", "-DHAVE_CONFIG_H",
           "-I" + os.path.join(ROOT, "include"), "-I" + SRC,
           "-I" + os.path.join(SRC, "includes")] + FLAGS + BACKENDS[backend]
    if "unwind" in lemma:
        cmd += ["--unwind", str(lemma["unwind"])]
    for k, v in lemma.get("unwindset", {}).items():
        cmd += ["--unwindset", f"{k}:{v}"]
    cmd += lemma.get("extra", [])
    cmd += [os.path.join(ROOT, "harness", lemma["name"] + ".c"),
            os.path.join(ROOT, "stubs", "unreachable.c")]
    cmd += [os.path.join(SRC, f) for f in lemma["src"]]
    cmd += [os.path.join(ROOT, "stubs", f) for f in lemma.get("stubs", [])]
    t = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, preexec_fn=_limit)
        out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return {"status": "TIMEOUT", "secs": timeout}
    secs = round(time.time() - t, 2)
    fails = re.findall(r"^\[([^\]]+)\] (.*): FAILURE$", out, re.M)
    m = re.search(r"\*\* (\d+) of (\d+) failed", out)
    total = int(m.group(2)) if m else None
    if p.returncode < 0 or "std::bad_alloc" in out or "Out of memory" in out:
        return {"status": "OOM", "secs": secs, "failures": [], "obligations": 0, "tail": out[-300:]}
    if "VERIFICATION SUCCESSFUL" in out:
        st = "PROVED"
    elif "VERIFICATION FAILED" in out:
        st = "REFUTED"
    else:
        st = "ERROR"
    return {"status": st, "secs": secs, "failures": fails,
            "obligations": total or len(re.findall(r": SUCCESS$", out, re.M)),
            "tail": out[-1500:] if st == "ERROR" else ""}

def main():
    import threading
    from concurrent.futures import as_completed
    lemmas = json.load(open(os.path.join(ROOT, "lemmas.json")))
    only = set(sys.argv[1:])
    if only:
        lemmas = [l for l in lemmas if key(l) in only or l["name"] in only]
    rp = os.path.join(ROOT, "results.json")
    old = json.load(open(rp)) if os.path.exists(rp) else {}
    lock = threading.Lock()
    pending = {}
    def done(l, b, r):
        with lock:
            k = key(l)
            pending.setdefault(k, {"lemma": l})[b] = r
            e = pending[k]
            if all(x in e for x in BACKENDS):
                v = {x: e[x]["status"] for x in BACKENDS}
                vals = set(v.values())
                if len(vals) == 1:
                    e["verdict"] = vals.pop()
                elif vals == {"PROVED", "REFUTED"}:
                    e["verdict"] = "DISAGREE"  # a real soundness alarm
                else:
                    e["verdict"] = "INCOMPLETE"  # one backend ran out of time/memory
                print(f"{e['verdict']:9} {k:40} sat={e['sat']['secs']}s z3={e['z3']['secs']}s "
                      f"obligations={e['sat']['obligations']}", flush=True)
                for x in BACKENDS:
                    for f in e[x].get("failures", []):
                        print(f"    [{x}] {f[0]}: {f[1]}", flush=True)
                    if e[x]["status"] == "ERROR":
                        print(e[x]["tail"], flush=True)
                old[k] = e
                json.dump(old, open(rp, "w"), indent=1)
    jobs = [(l, b) for l in lemmas for b in BACKENDS]
    with ThreadPoolExecutor(max_workers=WORKERS) as ex:
        futs = {ex.submit(run, l, b, l.get("timeout", 1800)): (l, b) for l, b in jobs}
        for f in as_completed(futs):
            l, b = futs[f]
            done(l, b, f.result())

if __name__ == "__main__":
    main()
