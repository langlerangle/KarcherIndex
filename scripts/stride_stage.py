#!/usr/bin/env python3
"""Apply the STRIDED import-only staging transform to the full ProdEnergyP family, in place.

For each leaf ProdEnergyP{i} with i >= W, inject ONE private `import KsIndexLean.ProdEnergyP{i-W}`
directly after the `public import KsIndexLean.ProdAccessor` anchor. This creates W independent build
chains (residue classes i mod W), so at most W heavy leaves are ready to elaborate at once — WITHOUT
the linear transitive-import accumulation of a gate-chain: leaf i transitively (build-order) imports
only its own chain (~ceil(count/W) leaves), not all prior leaves. No gate modules. Bodies/statements
byte-identical apart from the one added private import; the glue's public re-exports are untouched, so
visibility is preserved.

Validates (nonzero exit on any failure): every leaf present; anchor occurs exactly once; each diff is
exactly one added import; the ProdEnergyP subgraph is acyclic and max heavy-leaves-per-layer <= W;
reports the max transitive-subgraph accumulation. Does NOT compile Lean or measure.

Usage: stride_stage.py --repo <root> --leaf-start 0 --leaf-count 257 --width 8
"""
import argparse, os, re, sys, json, difflib, collections

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument("--repo", required=True)
ap.add_argument("--leaf-start", type=int, default=0)
ap.add_argument("--leaf-count", type=int, default=257)
ap.add_argument("--width", type=int, default=8)
a = ap.parse_args()

def fail(m): print("VALIDATION FAILURE:", m, file=sys.stderr); sys.exit(2)

KI = os.path.join(a.repo, "KsIndexLean")
if not os.path.isdir(KI): fail(f"no KsIndexLean/ under {a.repo}")
if a.width < 1: fail("width must be >= 1")
S, C, W = a.leaf_start, a.leaf_count, a.width
idxs = list(range(S, S + C))
for i in idxs:
    if not os.path.isfile(os.path.join(KI, f"ProdEnergyP{i}.lean")): fail(f"missing leaf ProdEnergyP{i}")
ANCHOR = "public import KsIndexLean.ProdAccessor\n"

# idempotency guard: refuse if already strided (any leaf already imports its i-W predecessor)
for i in idxs:
    if i - W >= S:
        t = open(os.path.join(KI, f"ProdEnergyP{i}.lean")).read()
        if f"import KsIndexLean.ProdEnergyP{i-W}\n" in t:
            fail(f"already strided (ProdEnergyP{i} imports ProdEnergyP{i-W}); refusing to double-apply")

for i in idxs:
    p = os.path.join(KI, f"ProdEnergyP{i}.lean"); txt = open(p).read()
    if txt.count(ANCHOR) != 1: fail(f"ProdEnergyP{i}: anchor occurs {txt.count(ANCHOR)} times")
    if i - W >= S:  # import the previous leaf in this residue chain
        gate = f"KsIndexLean.ProdEnergyP{i-W}"
        new = txt.replace(ANCHOR, ANCHOR + f"import {gate}\n", 1)
        added = [l for l in difflib.unified_diff(txt.splitlines(), new.splitlines(), lineterm="")
                 if l.startswith("+") and not l.startswith("+++")]
        removed = [l for l in difflib.unified_diff(txt.splitlines(), new.splitlines(), lineterm="")
                   if l.startswith("-") and not l.startswith("---")]
        if added != [f"+import {gate}"] or removed:
            fail(f"ProdEnergyP{i}: diff not exactly one added import (added={added} removed={removed})")
        open(p, "w").write(new)

# static validation: acyclic + concurrency cap + accumulation, over the ProdEnergyP subgraph
imp = re.compile(r'(?m)^\s*(?:public\s+)?import\s+(KsIndexLean\.ProdEnergyP\d+)')
def deps(i): return [int(re.search(r'(\d+)$', d).group(1))
                     for d in imp.findall(open(os.path.join(KI, f"ProdEnergyP{i}.lean")).read())]
dep = {i: set(deps(i)) for i in idxs}
built = set(); layers = []; guard = 0
while len(built) < len(idxs) and guard < 100000:
    guard += 1
    ready = [i for i in idxs if i not in built and dep[i] <= built]
    if not ready: break
    layers.append(ready); built |= set(ready)
if len(built) != len(idxs): fail(f"cycle/unbuildable ({len(built)}/{len(idxs)})")
maxw = max(len(L) for L in layers)
if maxw > W: fail(f"concurrency cap not met: {maxw} > W={W}")
cache = {}
def cl(i):
    if i in cache: return cache[i]
    s = set(); st = list(dep[i])
    while st:
        x = st.pop()
        if x in s: continue
        s.add(x); st += dep[x]
    cache[i] = s; return s
max_acc = max(len(cl(i)) for i in idxs)

print(json.dumps({"leaf_start": S, "leaf_count": C, "width": W, "n_layers": len(layers),
                  "max_concurrent": maxw, "max_transitive_accumulation": max_acc, "gates": 0}))
print(f"OK: strided ProdEnergyP{S}..{S+C-1} (n={C}) W={W}, acyclic, max_concurrent={maxw}<=W, "
      f"max_transitive_accumulation={max_acc} (chain depth), one private import/leaf, bodies identical.",
      file=sys.stderr)
