module

public import KsIndexLean.EndChartTransport
public import KsIndexLean.Surface

@[expose] public section


open Complex
open scoped Real
noncomputable section
namespace KsIndex.B2
open KsIndex.EndChart

/-! ### Angular sector classifier -/

/-- The `−π`-anchored `m`-fold angular sector index of `ζ` (the explicit witness inside
`exists_mem_powSector`): `⌈(arg ζ + π)/(2π/m)⌉ − 1`, as a `ℕ`. The ceiling-minus-one
convention matches the `Ioc` windows of `powSector` and the `(−π,π]` branch of `arg`.
Windows anchored at another angle require rotating the input before classification. -/
def powSectorIndex (m : ℕ) (ζ : ℂ) : ℕ :=
  (⌈(Complex.arg ζ + π) / (2 * π / m)⌉ - 1).toNat

/-- The classifier lands in `Fin m`'s range (`0 ≤ · < m`), for `m > 0`. -/
lemma powSectorIndex_lt {m : ℕ} (hm : 0 < m) (ζ : ℂ) : powSectorIndex m ζ < m := by
  obtain ⟨h1, h2⟩ := Complex.arg_mem_Ioc ζ
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : (0 : ℝ) < 2 * π / m := by positivity
  have hx0 : 0 < (Complex.arg ζ + π) / (2 * π / m) := div_pos (by linarith) hL
  have hxm : (Complex.arg ζ + π) / (2 * π / m) ≤ m := by
    rw [div_le_iff₀ hL]
    have hmL : (m : ℝ) * (2 * π / m) = 2 * π := by field_simp
    rw [hmL]; linarith
  have hc1 : 1 ≤ ⌈(Complex.arg ζ + π) / (2 * π / m)⌉ := Int.ceil_pos.mpr hx0
  have hc2 : ⌈(Complex.arg ζ + π) / (2 * π / m)⌉ ≤ (m : ℤ) :=
    Int.ceil_le.mpr (by exact_mod_cast hxm)
  unfold powSectorIndex
  omega

/-! ### A common domain for end patches and seams -/

/-- Fixed data for the end analysis around a single puncture `p`: positive multiplicity `m`,
`|p|=1` (puncture on the unit circle), and a chart radius `ρ` with `ρ^m < 2` — the exact bound
making the inside patch a *proper* curved sublevel set (`−r^m/2 ∈ (−1,0)`, so `cos < −r^m/2` is
satisfiable). Avoidance of other punctures requires a separate coverage hypothesis. -/
structure EndDomain (m : ℕ) (p : ℂ) (ρ : ℝ) : Prop where
  hm : 0 < m
  hp : Complex.normSq p = 1
  hρ : 0 < ρ
  hρ2 : ρ ^ m < 2

/-- Interior chart points of the small domain: nonzero (the origin is the puncture preimage,
excluded until removability), within radius `ρ`, with end-chart image nonzero (so the inversion
`σ = 1/w̄` used by the reflected glue is defined on the seam). -/
def EndDomain.Mem {m : ℕ} {p : ℂ} {ρ : ℝ} (_D : EndDomain m p ρ) (ζ : ℂ) : Prop :=
  ζ ≠ 0 ∧ ‖ζ‖ < ρ ∧ endChart p m ζ ≠ 0

/-- On the domain the inside-patch threshold `−‖ζ‖^m/2` lies strictly in `(−1, 0)`: the curved
inside-patch angular inequality therefore has a threshold strictly between the extrema
of cosine. This lemma bounds the threshold; it does not count the seam crossings. -/
lemma EndDomain.threshold_mem {m : ℕ} {p : ℂ} {ρ : ℝ} (D : EndDomain m p ρ) {ζ : ℂ}
    (hζ : D.Mem ζ) : -1 < -(‖ζ‖ ^ m / 2) ∧ -(‖ζ‖ ^ m / 2) < 0 := by
  obtain ⟨hζ0, hζρ, _⟩ := hζ
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have hpow : ‖ζ‖ ^ m < 2 := by
    have hlt : ‖ζ‖ ^ m < ρ ^ m := pow_lt_pow_left₀ hζρ (norm_nonneg ζ) D.hm.ne'
    linarith [D.hρ2]
  have hpos : 0 < ‖ζ‖ ^ m := by positivity
  exact ⟨by linarith, by linarith⟩

/-- The pulled-back-circle locus:
`|endChart p m ζ|² − 1 = 2 Re(p̄ ζ^m) + |ζ|^{2m}` for `|p|=1`. The sign of the
LHS partitions inside (`<0`) / outside (`>0`). -/
lemma endChart_normSq_sub_one {p : ℂ} (hp : Complex.normSq p = 1) (m : ℕ) (ζ : ℂ) :
    Complex.normSq (endChart p m ζ) - 1
      = 2 * ((starRingEnd ℂ p) * ζ ^ m).re + Complex.normSq ζ ^ m := by
  have hconj : (p * (starRingEnd ℂ) (ζ ^ m)).re = ((starRingEnd ℂ p) * ζ ^ m).re := by
    rw [← Complex.conj_re ((starRingEnd ℂ p) * ζ ^ m)]
    congr 1
    rw [map_mul, Complex.conj_conj]
  rw [endChart, Complex.normSq_add, map_pow, hp, hconj]
  ring

/-- Inside characterization: `endChart p m ζ` is in the open disk iff the
locus expression is negative — the sign of §boundary partitions inside/outside. -/
lemma endChart_mem_disk_iff {p : ℂ} (hp : Complex.normSq p = 1) (m : ℕ) (ζ : ℂ) :
    Complex.normSq (endChart p m ζ) < 1
      ↔ 2 * ((starRingEnd ℂ p) * ζ ^ m).re + Complex.normSq ζ ^ m < 0 := by
  rw [← endChart_normSq_sub_one hp m ζ, sub_lt_zero]

/-- The end-chart image lies outside the closed disk exactly when the locus expression is positive. -/
lemma endChart_notMem_closedDisk_iff {p : ℂ} (hp : Complex.normSq p = 1) (m : ℕ) (ζ : ℂ) :
    1 < Complex.normSq (endChart p m ζ)
      ↔ 0 < 2 * ((starRingEnd ℂ p) * ζ ^ m).re + Complex.normSq ζ ^ m := by
  rw [← endChart_normSq_sub_one hp m ζ, sub_pos]

/-- The locus expression `L_p(ζ) = 2 Re(p̄ ζ^m) + |ζ|^{2m}`; its sign is the inside/outside
partition (`< 0` inside, `> 0` outside, `= 0` the pulled-back circle). -/
def locusExpr (p : ℂ) (m : ℕ) (ζ : ℂ) : ℝ :=
  2 * ((starRingEnd ℂ p) * ζ ^ m).re + Complex.normSq ζ ^ m

/-- Polar form of the locus, with its radial dependence explicit.
`L_p(ζ) = ‖ζ‖^m · (2 cos(m·argζ − argp) + ‖ζ‖^m)` for `|p|=1`. The inside region `L_p<0` is thus the
*curved* `cos(m·argζ − argp) < −‖ζ‖^m/2` — the r-dependent patch membership (NOT a fixed angular
width). Exp route: `ζ^m = ‖ζ‖^m·exp(m·argζ·I)` exactly (no `arg(ζ^m)` branch issue). -/
lemma locusExpr_polar {p : ℂ} (hp : ‖p‖ = 1) (m : ℕ) (ζ : ℂ) :
    locusExpr p m ζ
      = ‖ζ‖ ^ m * (2 * Real.cos ((m : ℝ) * Complex.arg ζ - Complex.arg p) + ‖ζ‖ ^ m) := by
  have hpc : (starRingEnd ℂ) p = Complex.exp (-(Complex.arg p : ℂ) * I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I p, hp, Complex.ofReal_one, one_mul]
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hζm : ζ ^ m = (↑(‖ζ‖ ^ m) : ℂ) * Complex.exp ((↑((m : ℝ) * Complex.arg ζ) : ℂ) * I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ζ]
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hre : ((starRingEnd ℂ) p * ζ ^ m).re
      = ‖ζ‖ ^ m * Real.cos ((m : ℝ) * Complex.arg ζ - Complex.arg p) := by
    rw [hpc, hζm, ← mul_assoc, mul_comm (Complex.exp _) (↑(‖ζ‖ ^ m) : ℂ), mul_assoc,
      ← Complex.exp_add]
    rw [show -(Complex.arg p : ℂ) * I + ↑((m : ℝ) * Complex.arg ζ) * I
          = (↑((m : ℝ) * Complex.arg ζ - Complex.arg p) : ℂ) * I from by push_cast; ring]
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hns : Complex.normSq ζ ^ m = (‖ζ‖ ^ m) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; ring
  unfold locusExpr
  rw [hre, hns]
  ring

/-- `L_p` is invariant under multiplication by `ρ` when `ρ^m=1` and `|ρ|²=1`.
These hypotheses allow `ρ=1` and `m=0`; no exact rotation order or component count is asserted. -/
lemma locusExpr_rotation {p : ℂ} {m : ℕ} {ρ : ℂ} (hρ : ρ ^ m = 1)
    (hρn : Complex.normSq ρ = 1) (ζ : ℂ) :
    locusExpr p m (ρ * ζ) = locusExpr p m ζ := by
  simp only [locusExpr, mul_pow, hρ, one_mul, map_mul, hρn]

/-! ### Patch sets and rotation invariance -/

/-- Inside patch set: `endChart p m ζ` strictly inside the disk (`locusExpr < 0`). -/
def Inside (p : ℂ) (m : ℕ) : Set ℂ := {ζ | locusExpr p m ζ < 0}
/-- Outside patch set (`locusExpr > 0`). -/
def Outside (p : ℂ) (m : ℕ) : Set ℂ := {ζ | 0 < locusExpr p m ζ}
/-- Seam locus (`locusExpr = 0` = pulled-back circle). -/
def Seam (p : ℂ) (m : ℕ) : Set ℂ := {ζ | locusExpr p m ζ = 0}

/-- Membership bridge: `ζ ∈ Inside` iff `endChart p m ζ` is in the open disk (`|p|=1`). -/
lemma mem_Inside_iff {p : ℂ} (hp : Complex.normSq p = 1) (m : ℕ) (ζ : ℂ) :
    ζ ∈ Inside p m ↔ Complex.normSq (endChart p m ζ) < 1 :=
  (endChart_mem_disk_iff hp m ζ).symm

/-- Boundary membership: `ζ ∈ Seam` iff `endChart p m ζ` lies on the unit circle (`|p|=1`) — the
seam is the pulled-back circle `endChart⁻¹(|w|=1)`. -/
lemma mem_Seam_iff {p : ℂ} (hp : Complex.normSq p = 1) (m : ℕ) (ζ : ℂ) :
    ζ ∈ Seam p m ↔ Complex.normSq (endChart p m ζ) = 1 := by
  change locusExpr p m ζ = 0 ↔ Complex.normSq (endChart p m ζ) = 1
  rw [locusExpr, ← endChart_normSq_sub_one hp m ζ, sub_eq_zero]

/-- Inside-patch membership in polar coordinates. For `ζ ≠ 0` the end-chart image is *strictly inside*
the disk iff the lifted angle satisfies the curved inequality `cos(m·argζ − argp) < −‖ζ‖^m/2`. The
bound is `r`-dependent (`r = ‖ζ‖`): the patch is NOT a fixed angular wedge. `m`-generic and free of
the `arg` cut — the `ζ^m = ‖ζ‖^m e^{im argζ}` identity in `locusExpr_polar` holds across the branch,
so `m = 1` and either side of the `(−π,π]` cut are the same proof. -/
lemma Inside_iff_cos {p : ℂ} (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0) :
    ζ ∈ Inside p m
      ↔ Real.cos ((m : ℝ) * Complex.arg ζ - Complex.arg p) < -(‖ζ‖ ^ m / 2) := by
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hpos : 0 < ‖ζ‖ ^ m := by positivity
  change locusExpr p m ζ < 0 ↔ _
  rw [locusExpr_polar hp]
  constructor
  · intro h; nlinarith [h, hpos]
  · intro h; nlinarith [h, hpos]

/-- Companion: the end-chart image is strictly *outside* iff `cos(m·argζ − argp) > −‖ζ‖^m/2`. -/
lemma Outside_iff_cos {p : ℂ} (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0) :
    ζ ∈ Outside p m
      ↔ -(‖ζ‖ ^ m / 2) < Real.cos ((m : ℝ) * Complex.arg ζ - Complex.arg p) := by
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hpos : 0 < ‖ζ‖ ^ m := by positivity
  change 0 < locusExpr p m ζ ↔ _
  rw [locusExpr_polar hp]
  constructor
  · intro h; nlinarith [h, hpos]
  · intro h; nlinarith [h, hpos]

/-- Multiplication by a unit complex number satisfying `ρ^m=1` preserves membership
in the inside patch. The hypotheses do not require `ρ` to have exact order `m`. -/
lemma mem_Inside_rotation {p : ℂ} {m : ℕ} {ρ : ℂ} (hρ : ρ ^ m = 1)
    (hρn : Complex.normSq ρ = 1) (ζ : ℂ) : ρ * ζ ∈ Inside p m ↔ ζ ∈ Inside p m := by
  change locusExpr p m (ρ * ζ) < 0 ↔ locusExpr p m ζ < 0
  rw [locusExpr_rotation hρ hρn]

lemma mem_Outside_rotation {p : ℂ} {m : ℕ} {ρ : ℂ} (hρ : ρ ^ m = 1)
    (hρn : Complex.normSq ρ = 1) (ζ : ℂ) : ρ * ζ ∈ Outside p m ↔ ζ ∈ Outside p m := by
  change 0 < locusExpr p m (ρ * ζ) ↔ 0 < locusExpr p m ζ
  rw [locusExpr_rotation hρ hρn]

/-! ### End fields with a prescribed region index -/

/-- The chart-side field given a w-loop-region index `idx : ℂ → ZMod (2m)`: on each region,
`Surface.glue u (idx ζ)` already reads copy `idx ζ` inside the disk and copy `idx ζ + 1` reflected
outside. The function `idx` is supplied as an argument; this definition imposes no
continuity or compatibility conditions on it. -/
def endFieldWith {m : ℕ} (p : ℂ) (u : ZMod (2 * m) → ℂ → ℂ)
    (idx : ℂ → ZMod (2 * m)) (ζ : ℂ) : ℂ :=
  Surface.glue u (idx ζ) (endChart p m ζ)

end KsIndex.B2
