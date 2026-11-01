"""Generate upper-bound certificate data and baseline Lean proof templates.

The supported configurations are the prototype (M=64, CH=32) and production
(M=8192, CH=128). The source root must contain the pinned trial input modules.
Output goes into a new directory, never an existing checkout directory.
Generated integers remain untrusted until Lean checks their consuming proofs;
this script neither runs Lean nor certifies the resulting spectral sign.
Committed production energy and tail proofs contain later optimizations and
are not reproduced byte for byte. See negsign_generator_record.json; do not
overwrite those proofs with the baseline templates emitted here.

Example from the repository root:
  python3 -I scripts/negsign_generator.py --M 64 --CH 32 --prefix Proto \
    --source-root KsIndexLean --outdir /tmp/negsign-prototype-new

Generation is separate from the expensive, explicitly requested certificate build.
"""
import argparse
import hashlib
import re
from pathlib import Path

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--M', type=int, required=True, choices=[64, 8192])
ap.add_argument('--CH', type=int, required=True, choices=[32, 128])
ap.add_argument('--prefix', required=True)
ap.add_argument('--source-root', type=Path, required=True,
                help='directory containing the pinned Lean trial input modules')
ap.add_argument('--outdir', type=Path, required=True,
                help='new output directory; parent must already exist')
a = ap.parse_args()
if (a.M, a.CH) not in [(64, 32), (8192, 128)]:
    ap.error('supported (M, CH) pairs are (64, 32) and (8192, 128)')
if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', a.prefix):
    ap.error('prefix must start with an uppercase ASCII letter and contain only letters, digits or underscores')
root = a.source_root
INPUT_HASHES = {
    'AlphaTrialIntegerData.lean': '72a160cd856488f61fe164d08006e937d63b46bac9e8dc93d08e7a3ccecff9e1',
    'AlphaRemarkTrial.lean': 'a2bf002a828202b41a085bbf7a71c014426c77fee81ab92167bed4b70bc662e8',
}
input_text = {}
for name, expected in INPUT_HASHES.items():
    try:
        data = (root / name).read_bytes()
    except OSError as error:
        ap.error(f'cannot read {name}: {error}')
    if hashlib.sha256(data).hexdigest() != expected:
        ap.error(f'{name}: input hash mismatch; review changes before updating the pinned generator')
    input_text[name] = data.decode('utf-8')
M, CH, PX = a.M, a.CH, a.prefix
N = M + 4                      # coverage includes shifted endpoint samples
NE = N + 1                     # entries 0..N per stream
NCH = (NE + CH - 1) // CH
out = a.outdir
try:
    out.mkdir()                # exclusive creation; existing outputs are never overwritten
except OSError as error:
    ap.error(f'cannot create fresh output directory: {error}')
BS = [2161809, 2838191]

# exact integer streams
tab = {}
for f, B in enumerate(BS):
    for r in [0, 1]:
        xs = [10**30]
        for n in range(N):
            xs.append((B - 5000000*(r+2*n))*xs[-1] // (B + 5000000*(r+2*n+2)))
        tab[f, r] = xs

def write(name, body):
    # Templates put all imports first. Emit the module-system interface without
    # changing the arithmetic data or proof bodies.
    imports = list(re.finditer(r'^import\b[^\n]*\n', body, re.M))
    if imports:
        end = imports[-1].end()
        header = body[:end]
        if re.sub(r'^import\b[^\n]*\n', '', header, flags=re.M).strip():
            raise ValueError('non-import content before final import: ' + name)
        body = ('module\n\n' + re.sub(r'^import ', 'public import ', header, flags=re.M)
                + '\n@[expose] public section\n\n' + body[end:])
    else:
        body = 'module\n\n@[expose] public section\n\n' + body
    (out / f'{name}.lean').write_text(body)
    print('wrote', name, len(body))

# --- data modules (one per stream) ---
for f in range(2):
    for r in range(2):
        xs = tab[f, r]
        s = f'/-! Generated stream data (family {f}, parity {r}); untrusted until checked. -/\n'
        s += f'namespace KsIndex.NegSign{PX}\n'
        chs = []
        for j in range(NCH):
            nm = f'c{f}{r}_{j}'
            chs.append(nm)
            s += f'def {nm} : Array Int := #[' + ','.join(map(str, xs[j*CH:(j+1)*CH])) + ']\n'
        s += f'def s{f}{r} : Array (Array Int) := #[' + ','.join(chs) + ']\n'
        s += f'end KsIndex.NegSign{PX}\n'
        write(f'{PX}DataF{f}R{r}', s)

# --- accessor ---
s = f'''import KsIndexLean.{PX}DataF0R0
import KsIndexLean.{PX}DataF0R1
import KsIndexLean.{PX}DataF1R0
import KsIndexLean.{PX}DataF1R1
import KsIndexLean.AlphaTrialTableData

/-! Two-level accessor over the generated streams. -/
namespace KsIndex.NegSign{PX}

def t (B : ℤ) (r n : ℕ) : ℤ :=
  (((if B = {BS[0]} then (if r = 0 then s00 else s01)
    else (if r = 0 then s10 else s11))[n / {CH}]?.getD #[])[n % {CH}]?.getD 0)

end KsIndex.NegSign{PX}
'''
write(f'{PX}Accessor', s)

# --- stream checks: per-stream block theorems + step assembly; then valid ---
BPB = 8   # blocks per check-part file
for f in range(2):
    for r in range(2):
        B = BS[f]
        blocks = []
        for j in range(NCH):
            off = j*CH
            ln = min(CH, N - off)
            if ln > 0:
                blocks.append((f'block{f}{r}_{j}', off, ln))
        nparts = (len(blocks) + BPB - 1) // BPB
        partof = {}
        for pi in range(nparts):
            s2 = f'import KsIndexLean.{PX}Accessor\n'
            s2 += f'set_option linter.style.longLine false\n'
            s2 += f'/-! Block checks, stream ({f},{r}), part {pi}. -/\n'
            s2 += f'namespace KsIndex.NegSign{PX}\n'
            for nm, off, ln in blocks[pi*BPB:(pi+1)*BPB]:
                partof[nm] = pi
                if off == 0:
                    idx, idx1 = 'm.val', 'm.val + 1'
                else:
                    idx, idx1 = f'{off} + m.val', f'{off} + m.val + 1'
                s2 += (f'theorem {nm} : ∀ m : Fin {ln}, t {B} {r} ({idx1}) =\n'
                       f'    ({B} - 5000000 * (({r} : ℤ) + 2 * ({idx}))) * t {B} {r} ({idx}) /\n'
                       f'      ({B} + 5000000 * (({r} : ℤ) + 2 * ({idx}) + 2)) := by decide +kernel\n')
            if pi == 0:
                s2 += f'theorem zero{f}{r} : t {B} {r} 0 = 10 ^ 30 := by decide +kernel\n'
            s2 += f'end KsIndex.NegSign{PX}\n'
            write(f'{PX}CheckF{f}R{r}P{pi}', s2)
        s2 = ''.join(f'import KsIndexLean.{PX}CheckF{f}R{r}P{pi}\n' for pi in range(nparts))
        s2 += f'/-! Step assembly for stream ({f},{r}). -/\n'
        s2 += f'namespace KsIndex.NegSign{PX}\n'
        s2 += f'theorem step{f}{r} : ∀ n < {N}, t {B} {r} (n + 1) =\n'
        s2 += f'    ({B} - 5000000 * (({r} : ℤ) + 2 * n)) * t {B} {r} n /\n'
        s2 += f'      ({B} + 5000000 * (({r} : ℤ) + 2 * n + 2)) := by\n'
        s2 += '  intro n hn\n'
        for bi, (nm, off, ln) in enumerate(blocks):
            hi = off + ln
            last = (bi == len(blocks) - 1)
            if off == 0:
                s2 += f'  by_cases h0 : n < {hi}\n'
                s2 += f'  · exact {nm} ⟨n, h0⟩\n'
            else:
                body = (f'have e : {off} + (n - {off}) = n := by omega\n'
                        f'    rw [← e]\n'
                        f'    exact {nm} ⟨n - {off}, by omega⟩\n')
                if not last:
                    s2 += f'  by_cases h{off} : n < {hi}\n'
                    s2 += f'  · ' + body
                else:
                    s2 += f'  · ' + body
        s2 += f'end KsIndex.NegSign{PX}\n'
        write(f'{PX}StepF{f}R{r}', s2)

# --- valid-table assembly ---
s = f'''import KsIndexLean.{PX}StepF0R0
import KsIndexLean.{PX}StepF0R1
import KsIndexLean.{PX}StepF1R0
import KsIndexLean.{PX}StepF1R1

/-! The generated table is a valid coefficient table at coverage N = {N}. -/
namespace KsIndex.NegSign{PX}
open KsIndex.AlphaRemarkTrial

theorem valid : ValidCoefficientTable {N} t := by
  intro i r hr
  have hnum : numerator i = {BS[0]} ∨ numerator i = {BS[1]} := by
    by_cases hi : i.val < 12
    · exact Or.inl (by simp [numerator, hi])
    · exact Or.inr (by simp [numerator, hi])
  interval_cases r
  · rcases hnum with h | h <;> rw [h]
    · exact ⟨zero00, fun n hn => step00 n hn⟩
    · exact ⟨zero10, fun n hn => step10 n hn⟩
  · rcases hnum with h | h <;> rw [h]
    · exact ⟨zero01, fun n hn => step01 n hn⟩
    · exact ⟨zero11, fun n hn => step11 n hn⟩

end KsIndex.NegSign{PX}
'''
write(f'{PX}Valid', s)
print('stage 1 done: NCH =', NCH, 'N =', N)

# ===================== Stage 2: energy chunks + window glue =====================
import re as _re
def _vector(file, name):
    s = input_text[file].split('def '+name, 1)[1].split('![', 1)[1].split(']', 1)[0]
    return [int(x) for x in _re.findall(r'-?\d+', s)]
coeff = _vector('AlphaTrialIntegerData.lean', 'coefficientNumerator')
shifts = _vector('AlphaRemarkTrial.lean', 'shift')

def cellAZE(i, k):
    k = abs(k); p = k % 2; n = k // 2; f = int(i >= 12)
    A = tab[f, p][n]
    Z = (719689657 if f == 0 else 738631771) if p else 10**9
    D = (3 if f == 0 else 2) if p else 0
    return A, Z, abs(A)*D + n*(abs(Z)+D)
def samp(k):
    A = E = 0
    for i in range(25):
        a_, z_, e_ = cellAZE(i, k + shifts[i])
        A += coeff[i]*a_*z_; E += abs(coeff[i])*e_
    return A, E
def energy(lo, hi, aa, bb):      # window n in [lo, hi] inclusive
    P = R = 0
    for n in range(lo, hi+1):
        A, E = samp(2*n+bb); pnum = (6*n+aa)**2 - 4; q = abs(6*n+aa)
        P += pnum*A*A//q; R += abs(pnum)*E*(2*abs(A)+E)//q + 2
    return P, R

ECH = 64
# chunk boundaries over [-M, M]
bounds = list(range(-M, M+1, ECH)) + [M+1]
chunks = [(bounds[i], bounds[i+1]-1) for i in range(len(bounds)-1)]
comp = {'P': (1, 0), 'Mm': (4, 1)}
cvals = {}
for tag, (aa, bb) in comp.items():
    for j, (lo, hi) in enumerate(chunks):
        P, R = energy(lo, hi, aa, bb)
        cvals[tag, j] = (lo, hi, P, R)
        s = f'import KsIndexLean.{PX}Accessor\n'
        s += f'/-! Energy chunk {tag}{j}: window [{lo},{hi}] of component (a,b)=({aa},{bb}). -/\n'
        s += f'namespace KsIndex.NegSign{PX}\nopen KsIndex.AlphaRemarkTrial\n'
        s += f'def w{tag}{j} : Finset ℤ := Finset.Ioc ({lo-1}) ({hi})\n'
        s += f'theorem e{tag}{j}_c : tableEnergyNumerator t w{tag}{j} {aa} {bb} = ({P} : ℤ) := by decide +kernel\n'
        s += f'theorem e{tag}{j}_r : tableEnergyRadius t w{tag}{j} {aa} {bb} = ({R} : ℤ) := by decide +kernel\n'
        s += f'end KsIndex.NegSign{PX}\n'
        write(f'{PX}Energy{tag}{j}', s)

# window glue: unions, totals, coverage, and the table bound at s = spectralLower
from fractions import Fraction as F
sL = F(12387574, 10**7)
totP = sum(cvals['P', j][2] for j in range(len(chunks))); totPR = sum(cvals['P', j][3] for j in range(len(chunks)))
totM = sum(cvals['Mm', j][2] for j in range(len(chunks))); totMR = sum(cvals['Mm', j][3] for j in range(len(chunks)))
W = (F(totP) + F(totPR) + sL*sL*(F(totM) + F(totMR))) / F(10)**102
imports = ''.join(f'import KsIndexLean.{PX}Energy{tag}{j}\n' for tag in comp for j in range(len(chunks)))
s = imports + f'import KsIndexLean.{PX}Valid\nimport KsIndexLean.NegSignRationalTails\nimport KsIndexLean.AlphaRemarkEndpoints\n'
s += 'set_option maxHeartbeats 1000000\n'
s += f'/-! Window aggregation and the finite-window bound at s = spectralLower. -/\n'
s += f'namespace KsIndex.NegSign{PX}\nopen KsIndex.AlphaRemarkTrial CircleQ\n'
s += f'def window : Finset ℤ := Finset.Icc (-{M} : ℤ) {M}\n'
nch = len(chunks)
s += (f'lemma window_Ioc : window = Finset.Ioc ({-(M+1)} : ℤ) {M} := by\n'
      f'  ext x; simp [window, Finset.mem_Icc, Finset.mem_Ioc]; omega\n')
Bs = [chunks[0][0] - 1] + [hi for (_, hi) in chunks]   # Ioc boundaries
for tag, (aa, bb) in comp.items():
    ws = [f'w{tag}{j}' for j in range(nch)]
    alldefs = ', '.join(ws)
    tot = totP if tag == 'P' else totM
    totr = totPR if tag == 'P' else totMR
    for kind, fn, tv in (('c', 'tableEnergyNumerator', tot), ('r', 'tableEnergyRadius', totr)):
        hyps = '\n'.join(f'  have h{j} := e{tag}{j}_{kind}' for j in range(nch))
        hs = ' '.join(f'h{j}' for j in range(nch))
        s += f'theorem window_{tag}_{kind} : {fn} t window {aa} {bb} = ({tv} : ℤ) := by\n'
        s += hyps + '\n'
        s += f'  simp only [{fn}, {alldefs}] at {hs} ⊢\n'
        s += f'  rw [window_Ioc]\n'
        for j in range(nch - 1):
            a, b = Bs[j], Bs[j+1]
            s += (f'  rw [show Finset.Ioc ({a} : ℤ) ({M} : ℤ) = '
                  f'Finset.Ioc ({a} : ℤ) ({b} : ℤ) ∪ Finset.Ioc ({b} : ℤ) ({M} : ℤ) from '
                  f'(Finset.Ioc_union_Ioc_eq_Ioc (by norm_num) (by norm_num)).symm, '
                  f'Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_refl _))]\n')
        for g in range(0, nch, 32):
            s += '  rw [' + ', '.join(f'h{j}' for j in range(g, min(g+32, nch))) + ']\n'
        s += '  norm_num\n'
    s += '\n'
s += f'''theorem window_covered_P : ∀ n ∈ window, SampleCovered {N} (2 * n + 0) := by
  intro n hn
  have hb := Finset.mem_Icc.mp hn
  apply sampleCovered_of_bound
  omega
theorem window_covered_M : ∀ n ∈ window, SampleCovered {N} (2 * n + 1) := by
  intro n hn
  have hb := Finset.mem_Icc.mp hn
  apply sampleCovered_of_bound
  omega
theorem window_bound :
    (∑ n ∈ window, CircleQ.sigP n * ‖trial n‖ ^ 2) +
      KsIndex.AlphaRemark.spectralLower ^ 2 *
        ∑ m ∈ window, CircleQ.sigM m * ‖CircleQ.convS trial m‖ ^ 2 ≤
      (({W.numerator} / {W.denominator} : ℚ) : ℝ) := by
  have h := finite_trial_energy_le_table valid window window
    KsIndex.AlphaRemark.spectralLower (by simpa using window_covered_P) window_covered_M
  refine h.trans ?_
  rw [window_P_c, window_P_r, window_Mm_c, window_Mm_r, KsIndex.AlphaRemark.spectralLower]
  push_cast
  norm_num
end KsIndex.NegSign{PX}
'''
write(f'{PX}WindowGlue', s)
print('stage 2 done: chunks/component =', nch, 'W =', float(W))

# ===================== Stage 3: tails + mini-assembly =====================
# ℚ mirrors of the Lean defs (must match NegSignRationalTails exactly)
def expQ(i): return F(4323618, 10**7) if i < 12 else F(5676382, 10**7)
def coQ(i): return F(coeff[i], 10**12)
def pwQ(i, j): return 3*coQ(i)*coQ(j) / (2*(expQ(i)+expQ(j)))
def leadUQ(cen, rad):
    return sum(pwQ(i,j)*(cen[i]*cen[j]) + abs(pwQ(i,j))*(abs(cen[i])*rad[j]+abs(cen[j])*rad[i]+rad[i]*rad[j])
               for i in range(25) for j in range(25))
def errUQ(rq, c, cen, rad):
    return sum(abs(c - 3*(expQ(j)*rq[i]+expQ(i)*rq[j])/(expQ(i)+expQ(j))) *
               ((coQ(i)**2*(abs(cen[i])+rad[i])**2/(4*expQ(i)*rq[i])
                 + coQ(j)**2*(abs(cen[j])+rad[j])**2/(4*expQ(j)*rq[j]))/2)
               for i in range(25) for j in range(25))
def qlit(q):  # ℚ literal
    return f'({q.numerator} : ℚ)' if q.denominator == 1 else f'({q.numerator} / {q.denominator} : ℚ)'

TAILS = [('Pp', 2*M+2, 6*M+7, +1), ('Pn', 2*M+2, 6*M+5, -1),
         ('Mp', 2*M+3, 6*M+10, +1), ('Mn', 2*M+1, 6*M+2, -1)]
tailvals = {}
for T, K, c, sg in TAILS:
    ks = [K + sg*shifts[i] for i in range(25)]
    cen, rad, AZE = [], [], []
    for i in range(25):
        A, Z, E = cellAZE(i, ks[i])
        AZE.append((A, Z, E))
        cen.append((F(ks[i]) + expQ(i)) * F(A*Z, 10**39))
        rad.append((F(ks[i]) + expQ(i)) * F(E, 10**39))
    LV, EV = leadUQ(cen, rad), errUQ([F(k) for k in ks], F(c), cen, rad)
    tailvals[T] = (LV, EV)
    s = f'import KsIndexLean.{PX}Valid\nimport KsIndexLean.NegSignEndpointBridge\n'
    s += f'/-! Tail {T}: K = {K}, c = {c}, sign {sg:+d}. -/\n'
    s += 'set_option maxHeartbeats 2000000\nset_option linter.style.longLine false\n'
    s += f'namespace KsIndex.NegSign{PX}\nopen KsIndex.AlphaRemarkTrial PowerArc\n'
    s += f'def k{T} : Fin 25 → ℤ := ![' + ','.join(map(str, ks)) + ']\n'
    s += f'def kq{T} : Fin 25 → ℚ := ![' + ','.join(map(str, ks)) + ']\n'
    s += f'noncomputable def r{T} : Fin 25 → ℝ := fun i => ((k{T} i : ℤ) : ℝ)\n'
    s += f'def cen{T} : Fin 25 → ℚ := ![' + ','.join(qlit(q) for q in cen) + ']\n'
    s += f'def rad{T} : Fin 25 → ℚ := ![' + ','.join(qlit(q) for q in rad) + ']\n'
    for i in range(25):
        A, Z, E = AZE[i]
        s += (f'theorem he{T}_{i} : |tailEndpoint r{T} {i} - ((cen{T} {i} : ℚ) : ℝ)| ≤ ((rad{T} {i} : ℚ) : ℝ) :=\n'
              f'  tailEndpoint_interval_table valid (fun _ => rfl) (by decide) {i} (by decide)\n'
              f'    (A := {A}) (Z := {Z}) (E := {E})\n'
              f'    (by decide +kernel) (by decide +kernel) (by decide +kernel)\n'
              f'    (by decide +kernel) (by decide +kernel)\n')
    s += f'theorem he{T} : ∀ i, |tailEndpoint r{T} i - ((cen{T} i : ℚ) : ℝ)| ≤ ((rad{T} i : ℚ) : ℝ) := by\n'
    s += '  intro i\n  fin_cases i\n'
    for i in range(25):
        s += f'  · exact he{T}_{i}\n'
    s += (f'theorem lead{T} : tailLeading r{T} ≤ ((tailLeadingUpperQ cen{T} rad{T} : ℚ) : ℝ) :=\n'
          f'  tailLeading_le_Q r{T} cen{T} rad{T} (by decide +kernel) he{T}\n')
    s += (f'theorem err{T} : tailError r{T} (({c} : ℚ) : ℝ) ≤\n'
          f'    ((tailErrorUpperQ kq{T} {c} cen{T} rad{T} : ℚ) : ℝ) :=\n'
          f'  tailError_le_Q r{T} kq{T} {c} cen{T} rad{T}\n'
          f'    (fun i => by fin_cases i <;> norm_num [r{T}, k{T}, kq{T}])\n'
          f'    (by decide +kernel) (by decide +kernel) he{T}\n')
    s += f'theorem leadVal{T} : tailLeadingUpperQ cen{T} rad{T} = {qlit(LV)} := by decide +kernel\n'
    s += f'theorem errVal{T} : tailErrorUpperQ kq{T} {c} cen{T} rad{T} = {qlit(EV)} := by decide +kernel\n'
    s += f'end KsIndex.NegSign{PX}\n'
    write(f'{PX}Tail{T}', s)

sl2 = sL*sL
TP = tailvals['Pp'][0]+tailvals['Pp'][1]+tailvals['Pn'][0]+tailvals['Pn'][1]
TM = tailvals['Mp'][0]+tailvals['Mp'][1]+tailvals['Mn'][0]+tailvals['Mn'][1]
GRAND = W + TP + sl2*TM
print('stage 3 tails done; GRAND =', float(GRAND))

# ===================== Stage 3b: mini-assembly =====================
cQ = {'Pp': 6*M+7, 'Pn': 6*M+5, 'Mp': 6*M+10, 'Mn': 6*M+2}
TPq = tailvals['Pp'][0]+tailvals['Pp'][1]+tailvals['Pn'][0]+tailvals['Pn'][1]
TMq = tailvals['Mp'][0]+tailvals['Mp'][1]+tailvals['Mn'][0]+tailvals['Mn'][1]
s = (f'import KsIndexLean.{PX}WindowGlue\n'
     + ''.join(f'import KsIndexLean.{PX}Tail{T}\n' for T, _, _, _ in TAILS))
s += f'''/-! Assembly of the finite-window and tail bounds at spectralLower.
The theorem bounds the trial circle form by an explicit rational at M = {M}.
Its sign is established separately by the consuming spectral-sign theorem. -/
set_option maxHeartbeats 1000000
namespace KsIndex.NegSign{PX}
open KsIndex.AlphaRemarkTrial CircleQ

theorem qform_le_grand :
    Qform KsIndex.AlphaRemark.spectralLower trial ≤ (({GRAND.numerator} / {GRAND.denominator} : ℚ) : ℝ) := by
  have hA := qform_trial_le_window_add_tails KsIndex.AlphaRemark.spectralLower {M} (by norm_num)
  have hIcc : (Finset.Icc (-({M} : ℕ) : ℤ) ({M} : ℕ)) = window := by
    rw [window]; norm_num
  have hwP : (∑ n ∈ window, sigP n * sample (2 * n) ^ 2)
      = ∑ n ∈ window, sigP n * ‖trial n‖ ^ 2 :=
    Finset.sum_congr rfl fun n _ => by
      rw [trial_eq_sample, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hwM : (∑ m ∈ window, sigM m * sample (2 * m + 1) ^ 2)
      = ∑ m ∈ window, sigM m * ‖convS trial m‖ ^ 2 :=
    Finset.sum_congr rfl fun m _ => by
      rw [convS_eq_sample, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hIcc, hwP, hwM] at hA
  have ePp : (fun i => ((2 * ({M} : ℕ) + 2 + shift i : ℤ) : ℝ)) = rPp := by
    funext i; fin_cases i <;> norm_num [rPp, kPp, shift]
  have ePn : (fun i => ((2 * ({M} : ℕ) + 2 - shift i : ℤ) : ℝ)) = rPn := by
    funext i; fin_cases i <;> norm_num [rPn, kPn, shift]
  have eMp : (fun i => ((2 * ({M} : ℕ) + 3 + shift i : ℤ) : ℝ)) = rMp := by
    funext i; fin_cases i <;> norm_num [rMp, kMp, shift]
  have eMn : (fun i => ((2 * ({M} : ℕ) + 1 - shift i : ℤ) : ℝ)) = rMn := by
    funext i; fin_cases i <;> norm_num [rMn, kMn, shift]
  rw [ePp, ePn, eMp, eMn] at hA
  have c1 : (6 * (({M} : ℕ) : ℝ) + 7) = (({cQ['Pp']} : ℚ) : ℝ) := by norm_num
  have c2 : (6 * (({M} : ℕ) : ℝ) + 5) = (({cQ['Pn']} : ℚ) : ℝ) := by norm_num
  have c3 : (6 * (({M} : ℕ) : ℝ) + 10) = (({cQ['Mp']} : ℚ) : ℝ) := by norm_num
  have c4 : (6 * (({M} : ℕ) : ℝ) + 2) = (({cQ['Mn']} : ℚ) : ℝ) := by norm_num
  rw [c1, c2, c3, c4] at hA
  have hlPp := leadPp; have hePp := errPp
  have hlPn := leadPn; have hePn := errPn
  have hlMp := leadMp; have heMp := errMp
  have hlMn := leadMn; have heMn := errMn
  rw [leadValPp] at hlPp; rw [errValPp] at hePp
  rw [leadValPn] at hlPn; rw [errValPn] at hePn
  rw [leadValMp] at hlMp; rw [errValMp] at heMp
  rw [leadValMn] at hlMn; rw [errValMn] at heMn
  have hW := window_bound
  have hTM : ((tailLeading rMp + tailError rMp (({cQ['Mp']} : ℚ) : ℝ))
      + (tailLeading rMn + tailError rMn (({cQ['Mn']} : ℚ) : ℝ)))
      ≤ (({TMq.numerator} / {TMq.denominator} : ℚ) : ℝ) := by
    have he : ((tailLeadingUpperQ cenMp radMp : ℚ) : ℝ) = ((tailLeadingUpperQ cenMp radMp : ℚ) : ℝ) := rfl
    push_cast at hlMp heMp hlMn heMn ⊢
    linarith
  have hTMs := mul_le_mul_of_nonneg_left hTM
    (sq_nonneg KsIndex.AlphaRemark.spectralLower)
  have hfinal : (({W.numerator} / {W.denominator} : ℚ) : ℝ)
      + ((tailLeading rPp + tailError rPp (({cQ['Pp']} : ℚ) : ℝ))
        + (tailLeading rPn + tailError rPn (({cQ['Pn']} : ℚ) : ℝ)))
      + KsIndex.AlphaRemark.spectralLower ^ 2 *
          (({TMq.numerator} / {TMq.denominator} : ℚ) : ℝ)
      ≤ (({GRAND.numerator} / {GRAND.denominator} : ℚ) : ℝ) := by
    rw [KsIndex.AlphaRemark.spectralLower]
    push_cast at hlPp hePp hlPn hePn ⊢
    nlinarith [hlPp, hePp, hlPn, hePn]
  calc Qform KsIndex.AlphaRemark.spectralLower trial
      ≤ _ := hA
    _ ≤ _ := add_le_add (add_le_add hW (le_refl _)) (le_refl _)
    _ ≤ _ := add_le_add (le_refl _) hTMs
    _ ≤ _ := hfinal

end KsIndex.NegSign{PX}
'''
write(f'{PX}Assembly', s)
print('stage 3b done; GRAND =', float(GRAND))
