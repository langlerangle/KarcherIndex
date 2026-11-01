module

/-
# End-field witnesses

The end-field construction assigns disk copies through an angular index.
Its regularity argument separates local constancy off the seam from matching
of the two smooth germs at the seam. The same germ identities transport the
real and imaginary Jacobi equations. Lp transport and geometric coverage are
separate parts of the construction used for near-puncture bounds.
-/
public import KsIndexLean.EndChartPDE
public import KsIndexLean.B2Foundation
public import KsIndexLean.EndFieldGlue
public import KsIndexLean.EndFieldDomain
public import KsIndexLean.LapRealBridge
public import KsIndexLean.EnergySmooth

@[expose] public section


noncomputable section
open Complex Filter Topology
open scoped ContDiff
namespace KsIndex.EndField
open KsIndex.Surface KsIndex.EndChart KsIndex.B2 KsIndex.PunctureRemoval KsIndex.FaithfulInjection

/-- The end chart `σ_c(ζ) = p + ζ^m` is `C²` (indeed `C^∞`) everywhere. -/
lemma contDiffAt_endChart (p : ℂ) (m : ℕ) (ζ₀ : ℂ) : ContDiffAt ℝ 2 (endChart p m) ζ₀ :=
  (show ContDiff ℝ 2 (endChart p m) from contDiff_const.add (contDiff_id.pow m)).contDiffAt

/-- **C² of the end field off the seam.**  Where `idx` is locally constant and the chart image
`endChart ζ₀` is strictly inside or strictly outside the unit circle, `endFieldWith p u idx` is
`C²` at `ζ₀` — it equals `glue u (idx ζ₀) ∘ endChart` there, `C²` by the `glue_contDiffAt`
trilogy composed with the (smooth) chart.  No seam matching needed off the circle. -/
lemma endField_contDiffAt_offSeam {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hsmu : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (p : ℂ) (idx : ℂ → ZMod (2 * m)) {ζ₀ : ℂ}
    (hidx : ∀ᶠ ζ in 𝓝 ζ₀, idx ζ = idx ζ₀)
    (hoff : ‖endChart p m ζ₀‖ < 1 ∨ 1 < ‖endChart p m ζ₀‖) :
    ContDiffAt ℝ 2 (endFieldWith p u idx) ζ₀ := by
  have hgC2 : ContDiffAt ℝ 2 (glue u (idx ζ₀)) (endChart p m ζ₀) := by
    rcases hoff with h | h
    · exact glue_contDiffAt_disk hsmu (idx ζ₀) h
    · exact glue_contDiffAt_exterior hsmu (idx ζ₀) h
  have hcomp : ContDiffAt ℝ 2 (fun ζ => glue u (idx ζ₀) (endChart p m ζ)) ζ₀ :=
    hgC2.comp ζ₀ (contDiffAt_endChart p m ζ₀)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hidx] with ζ hζ
  simp only [endFieldWith, hζ]

/-! ### The radius-corrected angular index `idx`

`idx ζ = c + 2·⌊(T−A)/2π⌋` with `T = m·argζ − argp` and the RADIUS-dependent correction
`A(ζ) = arccos(−‖ζ‖^m/2)`.  The floor jumps only across `T = A (mod 2π)` — a curved seam,
since `A` depends on `‖ζ‖` — which is exactly the `a₂`-family (reflected-germ) branch; the
`a₁`-family `T = −A` gives step 0 (direct germ).  The principal-arg cut cancels in `ZMod(2m)`
(a `2πq` arg shift moves the floor by `mq`, `idx` by `2mq ≡ 0`). -/

/-- The radius-dependent angular threshold `A(ζ) = arccos(−‖ζ‖^m/2)`. -/
def angA (m : ℕ) (ζ : ℂ) : ℝ := Real.arccos (-‖ζ‖ ^ m / 2)

/-- The lifted chart angle `T(ζ) = m·argζ − argp`. -/
def angT (p : ℂ) (m : ℕ) (ζ : ℂ) : ℝ := (m : ℝ) * Complex.arg ζ - Complex.arg p

/-- The curved sector count `J(ζ) = ⌊(T−A)/2π⌋`. -/
def angJ (p : ℂ) (m : ℕ) (ζ : ℂ) : ℤ :=
  ⌊(angT p m ζ - angA m ζ) / (2 * Real.pi)⌋

/-- The radius-corrected angular copy-assignment. -/
def endIdx (m : ℕ) (c : ZMod (2 * m)) (p : ℂ) (ζ : ℂ) : ZMod (2 * m) :=
  c + 2 * ((angJ p m ζ : ℤ) : ZMod (2 * m))

/-- **`A(ζ) ∈ (π/2, π)`** on the common domain: `−‖ζ‖^m/2 ∈ (−1, 0)` (from `ζ≠0` and `‖ζ‖^m<2`,
the `EndDomain.threshold_mem` bounds), and `arccos` carries that interval into `(π/2, π)`. -/
lemma angA_mem {m : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0) (hb : ‖ζ‖ ^ m < 2) :
    Real.pi / 2 < angA m ζ ∧ angA m ζ < Real.pi := by
  have hpos : 0 < ‖ζ‖ ^ m := pow_pos (norm_pos_iff.mpr hζ) m
  rw [angA]
  exact ⟨Real.pi_div_two_lt_arccos.mpr (by linarith), Real.arccos_lt_pi.mpr (by linarith)⟩

/-- **Principal-arg shift compatibility.**  Recomputing `endIdx` with the
angle `arg ζ` replaced by a `2πq`-shifted lift leaves it unchanged: the shift moves the floor by
`m·q` (`Int.floor_add_intCast`), hence `idx` by `2m·q ≡ 0` in `ZMod (2m)`.  This is why the
principal-arg cut carries no discontinuity. -/
lemma endIdx_arg_invariant {m : ℕ} (c : ZMod (2 * m)) (p ζ : ℂ) (q : ℤ) :
    c + 2 * ((⌊((m : ℝ) * (Complex.arg ζ + 2 * Real.pi * (q : ℝ)) - Complex.arg p - angA m ζ)
        / (2 * Real.pi)⌋ : ℤ) : ZMod (2 * m)) = endIdx m c p ζ := by
  have hshift : ((m : ℝ) * (Complex.arg ζ + 2 * Real.pi * (q : ℝ)) - Complex.arg p - angA m ζ)
      / (2 * Real.pi) = (angT p m ζ - angA m ζ) / (2 * Real.pi) + ((m : ℤ) * q : ℤ) := by
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    rw [angT]; push_cast; field_simp; ring
  rw [hshift, Int.floor_add_intCast]
  have hzero : (2 : ZMod (2 * m)) * (m : ZMod (2 * m)) = 0 := by
    have h := ZMod.natCast_self (2 * m)
    push_cast at h; linear_combination h
  simp only [endIdx, angJ, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  linear_combination (q : ZMod (2 * m)) * hzero

/-- **Local constancy of `J` off the seam** (off the principal cut).  Where `arg` is continuous
(`0 < ζ₀.re ∨ ζ₀.im ≠ 0`) and `(T−A)/2π` is not an integer at `ζ₀` (i.e. `ζ₀` is off the `T=A`
seam), the floor `angJ` is locally constant — hence `endIdx` is too. -/
lemma angJ_eventuallyEq {m : ℕ} {p ζ₀ : ℂ} (hcut : 0 < ζ₀.re ∨ ζ₀.im ≠ 0)
    (hns : ∀ k : ℤ, (angT p m ζ₀ - angA m ζ₀) / (2 * Real.pi) ≠ (k : ℝ)) :
    ∀ᶠ ζ in nhds ζ₀, angJ p m ζ = angJ p m ζ₀ := by
  set r : ℂ → ℝ := fun ζ => (angT p m ζ - angA m ζ) / (2 * Real.pi) with hr
  have hcont : ContinuousAt r ζ₀ := by
    have hA : ContinuousAt (fun ζ => angA m ζ) ζ₀ :=
      Real.continuous_arccos.continuousAt.comp
        (((continuous_norm.pow m).continuousAt).neg.div_const 2)
    have hT : ContinuousAt (fun ζ => angT p m ζ) ζ₀ :=
      ((Complex.continuousAt_arg hcut).const_mul (m : ℝ)).sub continuousAt_const
    exact (hT.sub hA).div_const _
  have hlt : ((⌊r ζ₀⌋ : ℤ) : ℝ) < r ζ₀ :=
    lt_of_le_of_ne (Int.floor_le _) (fun h => hns ⌊r ζ₀⌋ h.symm)
  have hub : r ζ₀ < (⌊r ζ₀⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hev : ∀ᶠ ζ in nhds ζ₀, ((⌊r ζ₀⌋ : ℤ) : ℝ) < r ζ ∧ r ζ < (⌊r ζ₀⌋ : ℝ) + 1 :=
    hcont.eventually (Ioo_mem_nhds hlt hub)
  filter_upwards [hev] with ζ hζ
  change ⌊r ζ⌋ = ⌊r ζ₀⌋
  rw [Int.floor_eq_iff.mpr ⟨le_of_lt hζ.1, hζ.2⟩]

/-- **Polar form of the chart radius.**  For `‖p‖=1`,
`‖endChart ζ‖² − 1 = ‖ζ‖^m·(2 cos T + ‖ζ‖^m)` with `T = angT p m ζ`.  Hence (on `ζ≠0`) the seam
`‖endChart ζ‖=1` is `cos T = −‖ζ‖^m/2 = cos (angA m ζ)`. -/
lemma endChart_normSq_sub_one_polar {p : ℂ} (hp : ‖p‖ = 1) (m : ℕ) (ζ : ℂ) :
    Complex.normSq (endChart p m ζ) - 1 = ‖ζ‖ ^ m * (2 * Real.cos (angT p m ζ) + ‖ζ‖ ^ m) := by
  have hns : Complex.normSq p = 1 := by
    have h := Complex.sq_norm p; rw [hp] at h; simpa using h.symm
  rw [endChart_normSq_sub_one hns m ζ, ← locusExpr, locusExpr_polar hp]
  rfl

/-- **`J` relative to a branch lift.**  Writing `H = T−A−2πN`,
the floor splits off the integer `N`: `angJ = N + ⌊H/2π⌋`.  With `−2π < H < 2π` this forces
`⌊H/2π⌋ ∈ {−1, 0}`, giving the three-case `J` values (`N−1` outside / `N` seam & inside). -/
lemma angJ_eq_floor_H (p : ℂ) (m : ℕ) (ζ : ℂ) (N : ℤ) :
    angJ p m ζ = ⌊(angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) / (2 * Real.pi)⌋ + N := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have key : (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) / (2 * Real.pi) + (N : ℝ)
      = (angT p m ζ - angA m ζ) / (2 * Real.pi) := by field_simp; ring
  rw [angJ, ← key, Int.floor_add_intCast]

/-- **Outside value of `J`** (`H<0`).  With `H = T−A−2πN` and `−2π ≤ H < 0`
(just outside the `a₂` seam `T=A+2πN`), `⌊H/2π⌋ = −1`, so `angJ = N − 1`. -/
lemma angJ_eq_sub_one_of_neg {p : ℂ} {m : ℕ} {ζ : ℂ} {N : ℤ}
    (hlo : -(2 * Real.pi) ≤ angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ))
    (hneg : angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ) < 0) :
    angJ p m ζ = N - 1 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfloor : ⌊(angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) / (2 * Real.pi)⌋ = -1 := by
    apply Int.floor_eq_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [Int.cast_neg, Int.cast_one, le_div_iff₀ hpi]; nlinarith [hlo]
    · rw [Int.cast_neg, Int.cast_one, div_lt_iff₀ hpi]; nlinarith [hneg]
  rw [angJ_eq_floor_H p m ζ N, hfloor]; ring

/-- **Seam and inside value of `J`** (`H≥0`).  With `H = T−A−2πN` and
`0 ≤ H < 2π`, `⌊H/2π⌋ = 0`, so `angJ = N`. -/
lemma angJ_eq_of_nonneg {p : ℂ} {m : ℕ} {ζ : ℂ} {N : ℤ}
    (hlo : 0 ≤ angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ))
    (hhi : angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ) < 2 * Real.pi) :
    angJ p m ζ = N := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfloor : ⌊(angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) / (2 * Real.pi)⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [Int.cast_zero, le_div_iff₀ hpi]; nlinarith [hlo]
    · rw [Int.cast_zero, zero_add, div_lt_iff₀ hpi]; nlinarith [hhi]
  rw [angJ_eq_floor_H p m ζ N, hfloor, zero_add]

/-! ### Seam classification from the sign of `H`

`H = T − A − 2πN`.  Near a branch `T = A + 2πN` (so `H ≈ 0`), with `A ∈ (0,π)` and `A+H ∈ (0,π)`,
strict decrease of `cos` on `(0,π)` turns the sign of `H` into the chart-image position:
`H > 0 ⇒ inside` (`‖endChart‖ < 1`), `H < 0 ⇒ outside`, `H = 0 ⇒ seam`. -/

/-- Periodicity fold: `cos T = cos (A + H)` with `H = T − A − 2πN`. -/
lemma cos_angT_eq_cos_angA_add_H (p : ℂ) (m : ℕ) (ζ : ℂ) (N : ℤ) :
    Real.cos (angT p m ζ)
      = Real.cos (angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ))) := by
  have h : angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ))
      = angT p m ζ + ((-N : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
  rw [h, Real.cos_add_int_mul_two_pi]

/-- The chart radius as a cosine gap: `‖endChart‖² − 1 = 2‖ζ‖^m·(cos T − cos A)` (using
`cos A = −‖ζ‖^m/2`). -/
lemma endChart_normSq_sub_one_cos {p : ℂ} (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ} (hb : ‖ζ‖ ^ m ≤ 2) :
    Complex.normSq (endChart p m ζ) - 1
      = 2 * ‖ζ‖ ^ m * (Real.cos (angT p m ζ) - Real.cos (angA m ζ)) := by
  have hnn : (0 : ℝ) ≤ ‖ζ‖ ^ m := pow_nonneg (norm_nonneg ζ) m
  have hcosA : Real.cos (angA m ζ) = -‖ζ‖ ^ m / 2 := by
    rw [angA]; exact Real.cos_arccos (by linarith) (by linarith)
  rw [endChart_normSq_sub_one_polar hp, hcosA]; ring

/-- **Inside** (`H > 0`): the chart image lands strictly inside the unit disk. -/
lemma norm_endChart_lt_one {p : ℂ} (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0)
    (hb : ‖ζ‖ ^ m ≤ 2) {N : ℤ}
    (hA0 : 0 ≤ angA m ζ)
    (hAH : angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi)
    (hHpos : 0 < angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) :
    ‖endChart p m ζ‖ < 1 := by
  have hρ : 0 < ‖ζ‖ ^ m := pow_pos (norm_pos_iff.mpr hζ) m
  have hcos : Real.cos (angT p m ζ) < Real.cos (angA m ζ) := by
    rw [cos_angT_eq_cos_angA_add_H p m ζ N]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hA0 hAH (by linarith)
  have hsub := endChart_normSq_sub_one_cos hp hb
  have hns : Complex.normSq (endChart p m ζ) < 1 := by nlinarith [hsub, hcos, hρ]
  nlinarith [norm_nonneg (endChart p m ζ), Complex.sq_norm (endChart p m ζ), hns]

/-- **Outside** (`H < 0`): the chart image lands strictly outside the unit disk. -/
lemma one_lt_norm_endChart {p : ℂ} (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0)
    (hb : ‖ζ‖ ^ m ≤ 2) {N : ℤ}
    (hAH0 : 0 ≤ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)))
    (hA : angA m ζ ≤ Real.pi)
    (hHneg : angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ) < 0) :
    1 < ‖endChart p m ζ‖ := by
  have hρ : 0 < ‖ζ‖ ^ m := pow_pos (norm_pos_iff.mpr hζ) m
  have hcos : Real.cos (angA m ζ) < Real.cos (angT p m ζ) := by
    rw [cos_angT_eq_cos_angA_add_H p m ζ N]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hAH0 hA (by linarith)
  have hsub := endChart_normSq_sub_one_cos hp hb
  have hns : 1 < Complex.normSq (endChart p m ζ) := by nlinarith [hsub, hcos, hρ]
  nlinarith [norm_nonneg (endChart p m ζ), Complex.sq_norm (endChart p m ζ), hns]

/-- **Seam** (`H = 0`): the chart image lands exactly on the unit circle. -/
lemma norm_endChart_eq_one {p : ℂ} (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ} {N : ℤ}
    (hb : ‖ζ‖ ^ m ≤ 2)
    (hH0 : angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ) = 0) :
    ‖endChart p m ζ‖ = 1 := by
  have hcos : Real.cos (angT p m ζ) = Real.cos (angA m ζ) := by
    rw [cos_angT_eq_cos_angA_add_H p m ζ N, hH0, add_zero]
  have hsub := endChart_normSq_sub_one_cos hp hb
  rw [hcos, sub_self, mul_zero] at hsub
  have h2 : ‖endChart p m ζ‖ ^ 2 = 1 := by rw [Complex.sq_norm]; linarith [hsub]
  rw [← Real.sqrt_sq (norm_nonneg (endChart p m ζ)), h2, Real.sqrt_one]

/-! ### Polar form of `conj(p)·ζ^m` (feeds the `q`-algebra of the `c`-parity pin)

`conj(p)·ζ^m = ‖ζ‖^m·exp(T·i)` (`T = angT`), the exp route of `locusExpr_polar` (no `arg(ζ^m)`
branch issue).  Hence `(conj p·ζ^m).re = ‖ζ‖^m cos T` and `.im = ‖ζ‖^m sin T`. -/
lemma conj_mul_pow_polar {p : ℂ} (hp : ‖p‖ = 1) (m : ℕ) (ζ : ℂ) :
    (starRingEnd ℂ) p * ζ ^ m
      = (↑(‖ζ‖ ^ m) : ℂ) * Complex.exp ((↑(angT p m ζ) : ℂ) * I) := by
  have hpc : (starRingEnd ℂ) p = Complex.exp (-(Complex.arg p : ℂ) * I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I p, hp, Complex.ofReal_one, one_mul]
    rw [← Complex.exp_conj]; congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have hζm : ζ ^ m = (↑(‖ζ‖ ^ m) : ℂ) * Complex.exp ((↑((m : ℝ) * Complex.arg ζ) : ℂ) * I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ζ]
    rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf
  rw [hpc, hζm, ← mul_assoc, mul_comm (Complex.exp _) (↑(‖ζ‖ ^ m) : ℂ), mul_assoc,
    ← Complex.exp_add]
  rw [show -(Complex.arg p : ℂ) * I + ↑((m : ℝ) * Complex.arg ζ) * I
        = (↑(angT p m ζ) : ℂ) * I from by rw [angT]; push_cast; ring]

/-- `(conj p·ζ^m).re = ‖ζ‖^m cos T`. -/
lemma conj_mul_pow_re {p : ℂ} (hp : ‖p‖ = 1) (m : ℕ) (ζ : ℂ) :
    ((starRingEnd ℂ) p * ζ ^ m).re = ‖ζ‖ ^ m * Real.cos (angT p m ζ) := by
  rw [conj_mul_pow_polar hp, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im]; ring

/-- `(conj p·ζ^m).im = ‖ζ‖^m sin T`. -/
lemma conj_mul_pow_im {p : ℂ} (hp : ‖p‖ = 1) (m : ℕ) (ζ : ℂ) :
    ((starRingEnd ℂ) p * ζ ^ m).im = ‖ζ‖ ^ m * Real.sin (angT p m ζ) := by
  rw [conj_mul_pow_polar hp, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im]; ring

/-! ### The algebraic `q³` sign bridge (parity selection without arguments)

For `q = conj(p)·w` with `w = p + ζ^m` on the unit circle, the arc family of `w` is read off
`Im(q³)` without any argument calculation: on the unit circle `Im(q³)=Im q·(4(Re q)²−1)`, whose
sign is that of `Im q` once `(Re q)² > 1/4`; and `Re(w³) = −Im(p³)·Im(q³)` (since `Re(p³)=0`,
`w = p·q`).  At the `T=A` seam `q.re = 1−ρ²/2 > 1/2` and `q.im > 0`; at `T=−A`, `q.im < 0`. -/

/-- `Im(q³) = Im q · (3(Re q)² − (Im q)²)`. -/
lemma im_cube (q : ℂ) : (q ^ 3).im = q.im * (3 * q.re ^ 2 - q.im ^ 2) := by
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_im, Complex.mul_re]
  ring

/-- On the unit circle, `Im(q³) = Im q · (4(Re q)² − 1)` — sign of `Im q` when `(Re q)² > 1/4`. -/
lemma im_cube_unit {q : ℂ} (hq : Complex.normSq q = 1) :
    (q ^ 3).im = q.im * (4 * q.re ^ 2 - 1) := by
  have hq' : q.re * q.re + q.im * q.im = 1 := by rw [← Complex.normSq_apply]; exact hq
  rw [im_cube]; linear_combination (-q.im) * hq'

/-- **The sign bridge**: `Re((p·q)³) = −Im(p³)·Im(q³)` when `Re(p³)=0`. -/
lemma re_cube_mul {p q : ℂ} (hp : (p ^ 3).re = 0) :
    ((p * q) ^ 3).re = -(p ^ 3).im * (q ^ 3).im := by
  have h : (p * q) ^ 3 = p ^ 3 * q ^ 3 := by ring
  rw [h, Complex.mul_re, hp]; ring

/-! ### The `q`-algebra of the `c`-parity pin: `q = conj(p)·endChart = 1 + conj(p)·ζ^m`

`endChart = p·q` and `q = 1 + conj(p)·ζ^m`, so `Re((endChart)³) = −Im(p³)·Im(q³)` (`re_cube_mul`,
`Re(p³)=0`).  At a seam (`‖endChart‖=1`) `|q|=1`, and with `ρ = ‖ζ‖^m < 1` and `cos T = −ρ/2`,
`q.re = 1−ρ²/2 > ½` and `q.im = ρ sin T`; so on the `a₂` family (`sin T > 0`), `Im(q³) > 0`. -/

/-- `q = conj(p)·endChart = 1 + conj(p)·ζ^m` (uses `conj p · p = ‖p‖² = 1`). -/
lemma conj_mul_endChart {p : ℂ} (hp : ‖p‖ = 1) (m : ℕ) (ζ : ℂ) :
    (starRingEnd ℂ) p * endChart p m ζ = 1 + (starRingEnd ℂ) p * ζ ^ m := by
  rw [endChart, mul_add]
  congr 1
  rw [RCLike.conj_mul, hp]; norm_num

/-- `endChart = p·q` with `q = conj(p)·endChart` (uses `p · conj p = ‖p‖² = 1`). -/
lemma endChart_eq_p_mul_conj {p : ℂ} (hp : ‖p‖ = 1) (m : ℕ) (ζ : ℂ) :
    p * ((starRingEnd ℂ) p * endChart p m ζ) = endChart p m ζ := by
  rw [← mul_assoc, RCLike.mul_conj, hp]; norm_num

/-- On the seam `‖endChart‖=1`, `q = conj(p)·endChart` lies on the unit circle. -/
lemma normSq_conj_mul_endChart {p : ℂ} (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ}
    (hseam : ‖endChart p m ζ‖ = 1) :
    Complex.normSq ((starRingEnd ℂ) p * endChart p m ζ) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_mul, RCLike.norm_conj, hp, hseam]; norm_num

/-- `Re((endChart)³) = −Im(p³)·Im(q³)`, the `re_cube_mul` bridge applied to `endChart = p·q`. -/
lemma reCube_endChart_eq {p : ℂ} (hpunc : p ∈ punctures 3) (hp : ‖p‖ = 1) (m : ℕ) (ζ : ℂ) :
    ((endChart p m ζ) ^ 3).re
      = -(p ^ 3).im * (((starRingEnd ℂ) p * endChart p m ζ) ^ 3).im := by
  have key := re_cube_mul (q := (starRingEnd ℂ) p * endChart p m ζ) (cube_re_im hpunc).1
  rwa [endChart_eq_p_mul_conj hp m ζ] at key

/-- **`Im(q³) > 0` on the `a₂` family** (`cos T = −ρ/2`, `sin T > 0`, `ρ < 1`): the positive
reflected-arc sign.  Combined with `reCube_endChart_eq`, `Re((endChart)³)` has the sign of
`−Im(p³)`, pinning the arc. -/
lemma q_imCube_pos {p : ℂ} (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0) (hρ1 : ‖ζ‖ ^ m < 1)
    (hcos : Real.cos (angT p m ζ) = -‖ζ‖ ^ m / 2) (hsin : 0 < Real.sin (angT p m ζ))
    (hseam : ‖endChart p m ζ‖ = 1) :
    0 < (((starRingEnd ℂ) p * endChart p m ζ) ^ 3).im := by
  have hρ : 0 < ‖ζ‖ ^ m := pow_pos (norm_pos_iff.mpr hζ) m
  have hqeq := conj_mul_endChart hp m ζ
  rw [im_cube_unit (normSq_conj_mul_endChart hp hseam)]
  have hqim : ((starRingEnd ℂ) p * endChart p m ζ).im = ‖ζ‖ ^ m * Real.sin (angT p m ζ) := by
    rw [hqeq, Complex.add_im, Complex.one_im, conj_mul_pow_im hp]; ring
  have hqre : ((starRingEnd ℂ) p * endChart p m ζ).re = 1 - ‖ζ‖ ^ m * ‖ζ‖ ^ m / 2 := by
    rw [hqeq, Complex.add_re, Complex.one_re, conj_mul_pow_re hp, hcos]; ring
  rw [hqim, hqre]
  have h1 : 0 < ‖ζ‖ ^ m * Real.sin (angT p m ζ) := mul_pos hρ hsin
  have ha : ‖ζ‖ ^ m * ‖ζ‖ ^ m < 1 := by nlinarith [hρ, hρ1]
  have h2 : 0 < 4 * (1 - ‖ζ‖ ^ m * ‖ζ‖ ^ m / 2) ^ 2 - 1 := by
    nlinarith [ha, sq_nonneg (1 - ‖ζ‖ ^ m * ‖ζ‖ ^ m)]
  exact mul_pos h1 h2

/-- **The `a₂` arc membership from the `c`-parity pin.**  At an `a₂` seam, once `c`'s parity is
chosen so that `(−1)^(parity(c+2N))·Im(p³) > 0`, the chart image lands in the reflected seam arc
`seamArc (c+2N−1) = arc 3 (parity(c+2N)).val`.  Since `Re((endChart)³) = −Im(p³)·Im(q³)` with
`Im(q³) > 0`, the arc sign `(−1)^(parity(c+2N))·Re((endChart)³) < 0` holds. -/
lemma arc_mem_a2 {p : ℂ} (hpunc : p ∈ punctures 3) (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ} {N : ℤ}
    {c : ZMod (2 * m)} (hζ : ζ ≠ 0) (hρ1 : ‖ζ‖ ^ m < 1)
    (hcos : Real.cos (angT p m ζ) = -‖ζ‖ ^ m / 2) (hsin : 0 < Real.sin (angT p m ζ))
    (hseam : ‖endChart p m ζ‖ = 1)
    (hpar : 0 < (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)))).val * (p ^ 3).im) :
    endChart p m ζ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1) := by
  have hQ : 0 < (((starRingEnd ℂ) p * endChart p m ζ) ^ 3).im :=
    q_imCube_pos hp hζ hρ1 hcos hsin hseam
  have hre := reCube_endChart_eq hpunc hp m ζ
  have hc : c + 2 * (N : ZMod (2 * m)) - 1 + 1 = c + 2 * (N : ZMod (2 * m)) := by ring
  simp only [seamArc, arc, Set.mem_ofPred_eq]
  rw [hc]
  refine ⟨hseam, ?_⟩
  rw [hre]
  nlinarith [hpar, hQ]

/-- **`Im(q³) < 0` on the `a₁` family** (`cos T = −ρ/2`, `sin T < 0`, `ρ < 1`): the opposite
reflected-arc sign — `q.im = ρ sin T < 0`, `q.re = 1−ρ²/2 > ½`. -/
lemma q_imCube_neg {p : ℂ} (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0) (hρ1 : ‖ζ‖ ^ m < 1)
    (hcos : Real.cos (angT p m ζ) = -‖ζ‖ ^ m / 2) (hsin : Real.sin (angT p m ζ) < 0)
    (hseam : ‖endChart p m ζ‖ = 1) :
    (((starRingEnd ℂ) p * endChart p m ζ) ^ 3).im < 0 := by
  have hρ : 0 < ‖ζ‖ ^ m := pow_pos (norm_pos_iff.mpr hζ) m
  have hqeq := conj_mul_endChart hp m ζ
  rw [im_cube_unit (normSq_conj_mul_endChart hp hseam)]
  have hqim : ((starRingEnd ℂ) p * endChart p m ζ).im = ‖ζ‖ ^ m * Real.sin (angT p m ζ) := by
    rw [hqeq, Complex.add_im, Complex.one_im, conj_mul_pow_im hp]; ring
  have hqre : ((starRingEnd ℂ) p * endChart p m ζ).re = 1 - ‖ζ‖ ^ m * ‖ζ‖ ^ m / 2 := by
    rw [hqeq, Complex.add_re, Complex.one_re, conj_mul_pow_re hp, hcos]; ring
  rw [hqim, hqre]
  have h1 : ‖ζ‖ ^ m * Real.sin (angT p m ζ) < 0 := mul_neg_of_pos_of_neg hρ hsin
  have ha : ‖ζ‖ ^ m * ‖ζ‖ ^ m < 1 := by nlinarith [hρ, hρ1]
  have h2 : 0 < 4 * (1 - ‖ζ‖ ^ m * ‖ζ‖ ^ m / 2) ^ 2 - 1 := by
    nlinarith [ha, sq_nonneg (1 - ‖ζ‖ ^ m * ‖ζ‖ ^ m)]
  exact mul_neg_of_neg_of_pos h1 h2

/-- **The `a₁` arc membership** (direct-germ family, `T = −A`).  For a target index `n` whose
parity is pinned by `(−1)^(parity(n+1))·Im(p³) < 0`, the chart image lands in `seamArc n`.  Here
`Re((endChart)³) = −Im(p³)·Im(q³)` with `Im(q³) < 0`, so the arc sign is `< 0`.  (The single bit of
`c` that satisfies this and the `a₂` pin simultaneously is reconciled in the witness assembly.) -/
lemma arc_mem_a1 {p : ℂ} (hpunc : p ∈ punctures 3) (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ}
    {n : ZMod (2 * m)} (hζ : ζ ≠ 0) (hρ1 : ‖ζ‖ ^ m < 1)
    (hcos : Real.cos (angT p m ζ) = -‖ζ‖ ^ m / 2) (hsin : Real.sin (angT p m ζ) < 0)
    (hseam : ‖endChart p m ζ‖ = 1)
    (hpar : (-1 : ℝ) ^ (parity m (n + 1)).val * (p ^ 3).im < 0) :
    endChart p m ζ ∈ seamArc 3 m n := by
  have hQ : (((starRingEnd ℂ) p * endChart p m ζ) ^ 3).im < 0 :=
    q_imCube_neg hp hζ hρ1 hcos hsin hseam
  have hre := reCube_endChart_eq hpunc hp m ζ
  simp only [seamArc, arc, Set.mem_ofPred_eq]
  refine ⟨hseam, ?_⟩
  rw [hre]
  nlinarith [hpar, hQ]

/-! ### Parity arithmetic — one bit of `c` serves both seam families

`parity` kills the even shift `2x`, and flips under `+1`; so the `a₂` pin
`0 < (−1)^(parity c)·Im(p³)` and the `a₁` pin `(−1)^(parity(c+1))·Im(p³) < 0` are the same parity condition. -/

/-- `parity` is blind to the even shift: `parity (c + 2x) = parity c`. -/
lemma parity_add_two_mul {m : ℕ} (c x : ZMod (2 * m)) : parity m (c + 2 * x) = parity m c := by
  have h2 : parity m (2 : ZMod (2 * m)) = 0 := by
    have : (2 : ZMod (2 * m)) = 1 + 1 := by norm_num
    rw [this, map_add, map_one]; decide
  rw [map_add, map_mul, h2, zero_mul, add_zero]

/-- The sign `(−1)^(parity ·)` flips under `+1`. -/
lemma neg_one_pow_parity_add_one (a : ZMod 2) :
    (-1 : ℝ) ^ (a + 1).val = -(-1 : ℝ) ^ a.val := by
  fin_cases a <;>
    first
      | (show (-1 : ℝ) ^ 1 = -(-1 : ℝ) ^ 0; norm_num)
      | (show (-1 : ℝ) ^ 0 = -(-1 : ℝ) ^ 1; norm_num)

/-! ### The reflected-germ `=ᶠ` matching, pointwise across the seam

Near an `a₂`-family seam point `ζ₀` (where `T = A + 2πN`, `H = 0`), the end field agrees with the
single reflected germ `glue u (c+2N−1) ∘ σ ∘ endChart`.  The three regions — outside (`J=N−1`),
inside (`J=N`), seam (`J=N`, `SeamVal`) — each reduce to it via `glueSigma_outside` /
`glueSigma_inside` / `SeamVal`, with matching index pair `(j'+1,j'−1) = (c+2N, c+2N−2)`. -/

/-- **Inside** (`J=N`, `‖endChart‖<1`): `endField` reads `glue u (c+2N−1) ∘ σ` via `glueSigma_inside`
(copy `c+2N` directly). -/
lemma endFieldWith_eq_reflected_inside {m : ℕ} (p : ℂ) (u : ZMod (2 * m) → ℂ → ℂ)
    (c : ZMod (2 * m)) {ζ : ℂ} {N : ℤ} (hJ : angJ p m ζ = N)
    (hne : endChart p m ζ ≠ 0) (hlt : ‖endChart p m ζ‖ < 1) :
    endFieldWith p u (endIdx m c p) ζ
      = Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) (Bracket.σ (endChart p m ζ)) := by
  have hidx : c + 2 * (N : ZMod (2 * m)) - 1 + 1 = c + 2 * (N : ZMod (2 * m)) := by ring
  rw [glueSigma_inside u (c + 2 * (N : ZMod (2 * m)) - 1) hne hlt, hidx,
      endFieldWith_inside p u (endIdx m c p) (le_of_lt hlt)]
  simp only [endIdx, hJ]

/-- **Outside** (`J=N−1`, `1<‖endChart‖`): `endField` reads `glue u (c+2N−1) ∘ σ` via
`glueSigma_outside` (copy `c+2N−1` reflected). -/
lemma endFieldWith_eq_reflected_outside {m : ℕ} (p : ℂ) (u : ZMod (2 * m) → ℂ → ℂ)
    (c : ZMod (2 * m)) {ζ : ℂ} {N : ℤ} (hJ : angJ p m ζ = N - 1)
    (hgt : 1 < ‖endChart p m ζ‖) :
    endFieldWith p u (endIdx m c p) ζ
      = Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) (Bracket.σ (endChart p m ζ)) := by
  have hidx : c + 2 * ((N - 1 : ℤ) : ZMod (2 * m)) + 1 = c + 2 * (N : ZMod (2 * m)) - 1 := by
    push_cast; ring
  rw [glueSigma_outside u (c + 2 * (N : ZMod (2 * m)) - 1) hgt,
      endFieldWith_outside p u (endIdx m c p) hgt]
  simp only [endIdx, hJ]
  rw [hidx]

/-- **Seam** (`J=N`, `‖endChart‖=1`): `σ` fixes the point, and `SeamVal` identifies copies
`c+2N` and `c+2N−1` on `seamArc (c+2N−1)`. -/
lemma endFieldWith_eq_reflected_seam {k m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hsv : SeamVal k u) (c : ZMod (2 * m)) {ζ : ℂ} {N : ℤ} (hJ : angJ p m ζ = N)
    (hmem : endChart p m ζ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1))
    (heq : ‖endChart p m ζ‖ = 1) :
    endFieldWith p u (endIdx m c p) ζ
      = Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) (Bracket.σ (endChart p m ζ)) := by
  have hLHS : endFieldWith p u (endIdx m c p) ζ
      = u (c + 2 * (N : ZMod (2 * m))) (endChart p m ζ) := by
    rw [endFieldWith_inside p u (endIdx m c p) (le_of_eq heq)]
    simp only [endIdx, hJ]
  have hidx : c + 2 * (N : ZMod (2 * m)) - 1 + 1 = c + 2 * (N : ZMod (2 * m)) := by ring
  have hsvseam := hsv (c + 2 * (N : ZMod (2 * m)) - 1) (endChart p m ζ) hmem
  rw [hidx] at hsvseam
  have hRHS : Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) (Bracket.σ (endChart p m ζ))
      = u (c + 2 * (N : ZMod (2 * m)) - 1) (endChart p m ζ) := by
    rw [Bracket.σ_self heq]
    simp only [Surface.glue, if_pos (le_of_eq heq)]
  rw [hLHS, hRHS]
  exact hsvseam

/-! ### Neighborhood equality with the reflected germ

Combining the three pointwise germ identities: on a neighborhood of an `a₂` seam point `ζ₀`
(`H(ζ₀)=0`), `lt_trichotomy (H ζ) 0` routes each `ζ` to inside/seam/outside, where the floor value
and the classification feed the matching germ identity.  The neighborhood conditions are explicit
`∀ᶠ` hypotheses here; `endField_contDiffAt_seam_offCut` derives them off the principal cut. -/
lemma endFieldWith_reflected_eventuallyEq {m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hp : ‖p‖ = 1) (hsv : SeamVal 3 u) (c : ZMod (2 * m)) {ζ₀ : ℂ} {N : ℤ}
    (hne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0)
    (hζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0)
    (hb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2)
    (hHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)
        ∧ angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ) < 2 * Real.pi)
    (hAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
        ∧ 0 ≤ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ))
        ∧ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi)
    (harc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
        endChart p m ζ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    endFieldWith p u (endIdx m c p)
      =ᶠ[nhds ζ₀] fun ζ => Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1)
        (Bracket.σ (endChart p m ζ)) := by
  filter_upwards [hne, hζ, hb, hHbd, hAint, harc] with ζ hne hζ hb hHbd hAint harc
  obtain ⟨hA0, hAle, hAH0, hAHle⟩ := hAint
  rcases lt_trichotomy (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) 0 with hlt | heq | hgt
  · -- outside: H < 0
    have hJ : angJ p m ζ = N - 1 := angJ_eq_sub_one_of_neg (le_of_lt hHbd.1) hlt
    have hout : 1 < ‖endChart p m ζ‖ := one_lt_norm_endChart hp hζ hb hAH0 hAle hlt
    exact endFieldWith_eq_reflected_outside p u c hJ hout
  · -- seam: H = 0
    have hJ : angJ p m ζ = N := angJ_eq_of_nonneg (le_of_eq heq.symm) hHbd.2
    have hseam : ‖endChart p m ζ‖ = 1 := norm_endChart_eq_one hp hb heq
    exact endFieldWith_eq_reflected_seam p hsv c hJ (harc hseam) hseam
  · -- inside: H > 0
    have hJ : angJ p m ζ = N := angJ_eq_of_nonneg (le_of_lt hgt) hHbd.2
    have hin : ‖endChart p m ζ‖ < 1 := norm_endChart_lt_one hp hζ hb hA0 hAHle hgt
    exact endFieldWith_eq_reflected_inside p u c hJ hne hin

/-! ### C² regularity of the end field at the seam

At an `a₂` seam point `ζ₀` (`H(ζ₀)=0`), the matching reflected germ `glue u (c+2N−1) ∘ σ ∘ endChart`
is `C²`: `glue u (c+2N−1)` is `C^∞` at `σ(endChart ζ₀) = endChart ζ₀ ∈ seamArc (c+2N−1)` (IsSmooth
seam clause), `σ` is `C²` away from `0`, `endChart` is smooth.  `endFieldWith_reflected_eventuallyEq` transfers this to
`endFieldWith` by `congr_of_eventuallyEq`. -/
lemma endField_contDiffAt_seam {m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hp : ‖p‖ = 1) (hu : IsSmooth 3 m u) (hsv : SeamVal 3 u) (c : ZMod (2 * m)) {ζ₀ : ℂ} {N : ℤ}
    (hbζ₀ : ‖ζ₀‖ ^ m ≤ 2)
    (hH0 : angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ) = 0)
    (hne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0)
    (hζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0)
    (hb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2)
    (hHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)
        ∧ angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ) < 2 * Real.pi)
    (hAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
        ∧ 0 ≤ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ))
        ∧ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi)
    (harc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
        endChart p m ζ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ₀ := by
  have hseam0 : ‖endChart p m ζ₀‖ = 1 := norm_endChart_eq_one hp hbζ₀ hH0
  have hmem0 : endChart p m ζ₀ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1) :=
    harc.self_of_nhds hseam0
  have hne0 : endChart p m ζ₀ ≠ 0 := norm_pos_iff.mp (by rw [hseam0]; norm_num)
  have hσ0 : Bracket.σ (endChart p m ζ₀) = endChart p m ζ₀ := Bracket.σ_self hseam0
  have hglueσ : ContDiffAt ℝ 2 (Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1))
      (Bracket.σ (endChart p m ζ₀)) := by
    rw [hσ0]
    exact (hu.2.1 (c + 2 * (N : ZMod (2 * m)) - 1) (endChart p m ζ₀) hmem0).of_le two_le_infty
  have hfσ : ContDiffAt ℝ 2 (fun ζ => Bracket.σ (endChart p m ζ)) ζ₀ :=
    ((Bracket.contDiffAt_σ hne0).of_le two_le_infty).comp ζ₀ (contDiffAt_endChart p m ζ₀)
  have hcomp : ContDiffAt ℝ 2
      (Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) ∘ fun ζ => Bracket.σ (endChart p m ζ)) ζ₀ :=
    hglueσ.comp ζ₀ hfσ
  exact hcomp.congr_of_eventuallyEq
    (endFieldWith_reflected_eventuallyEq p hp hsv c hne hζ hb hHbd hAint harc)

/-! ### C² regularity at a seam point off the principal cut

Off the principal cut (`0 < ζ₀.re ∨ ζ₀.im ≠ 0`), continuity at `ζ₀` of `angA`, `angT`, `endChart`
and the sign functional produces the `∀ᶠ` hypotheses of `endField_contDiffAt_seam`, from just: `ζ₀ ≠ 0`,
`‖ζ₀‖^m < 2`, `ζ₀` on the `a₂` seam (`H(ζ₀)=0`), and the arc membership `endChart ζ₀ ∈
seamArc (c+2N−1)` (the `c`-parity pin, supplied by the `q³` bridge). -/
lemma endField_contDiffAt_seam_offCut {m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hp : ‖p‖ = 1) (hu : IsSmooth 3 m u) (hsv : SeamVal 3 u) (c : ZMod (2 * m)) {ζ₀ : ℂ} {N : ℤ}
    (hζ₀ : ζ₀ ≠ 0) (hcut : 0 < ζ₀.re ∨ ζ₀.im ≠ 0) (hb0 : ‖ζ₀‖ ^ m < 2)
    (hH0 : angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ) = 0)
    (hmem0 : endChart p m ζ₀ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ₀ := by
  -- continuity pieces at ζ₀
  have hendcont : ContinuousAt (endChart p m) ζ₀ := (contDiffAt_endChart p m ζ₀).continuousAt
  have hA : ContinuousAt (fun ζ => angA m ζ) ζ₀ :=
    Real.continuous_arccos.continuousAt.comp
      (((continuous_norm.pow m).continuousAt).neg.div_const 2)
  have hT : ContinuousAt (fun ζ => angT p m ζ) ζ₀ :=
    ((Complex.continuousAt_arg hcut).const_mul (m : ℝ)).sub continuousAt_const
  have hH : ContinuousAt
      (fun ζ => angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ζ₀ :=
    (hT.sub hA).sub continuousAt_const
  -- values at ζ₀
  have hseam0 : ‖endChart p m ζ₀‖ = 1 := norm_endChart_eq_one hp hb0.le hH0
  have hne0 : endChart p m ζ₀ ≠ 0 := norm_pos_iff.mp (by rw [hseam0]; norm_num)
  have hAmem := angA_mem hζ₀ hb0
  have hA0 : angA m ζ₀ ∈ Set.Ioo 0 Real.pi := ⟨by linarith [Real.pi_pos, hAmem.1], hAmem.2⟩
  -- the ∀ᶠ facts
  have fne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0 := hendcont.eventually_ne hne0
  have fζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0 := isOpen_ne.mem_nhds hζ₀
  have fb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2 := by
    filter_upwards [(continuous_norm.pow m).continuousAt.eventually_lt continuousAt_const hb0]
      with ζ h using h.le
  have fHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)
      ∧ angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ) < 2 * Real.pi := by
    have hmem : Set.Ioo (-(2 * Real.pi)) (2 * Real.pi)
        ∈ nhds (angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ)) := by
      rw [hH0]; exact Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    filter_upwards [hH.eventually hmem] with ζ h using ⟨h.1, h.2⟩
  have fAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
      ∧ 0 ≤ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ))
      ∧ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi := by
    have hmemA : Set.Ioo 0 Real.pi ∈ nhds (angA m ζ₀) := Ioo_mem_nhds hA0.1 hA0.2
    have hmemAH : Set.Ioo 0 Real.pi
        ∈ nhds (angA m ζ₀ + (angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ))) := by
      have hval : angA m ζ₀ + (angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ)) = angA m ζ₀ := by
        rw [hH0]; ring
      rw [hval]; exact Ioo_mem_nhds hA0.1 hA0.2
    filter_upwards [hA.eventually hmemA, (hA.add hH).eventually hmemAH] with ζ hfa hfah
    exact ⟨hfa.1.le, hfa.2.le, hfah.1.le, hfah.2.le⟩
  have farc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
      endChart p m ζ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1) := by
    have hsign0 : (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ₀) ^ 3).re < 0 := by
      have h := hmem0; simp only [seamArc, arc, Set.mem_ofPred_eq] at h; exact h.2
    have hgcont : ContinuousAt (fun ζ => (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ) ^ 3).re) ζ₀ :=
      continuousAt_const.mul (Complex.continuous_re.continuousAt.comp (hendcont.pow 3))
    filter_upwards [hgcont.eventually_lt continuousAt_const hsign0] with ζ hg hnorm
    simp only [seamArc, arc, Set.mem_ofPred_eq]
    exact ⟨hnorm, hg⟩
  exact endField_contDiffAt_seam p hp hu hsv c hb0.le hH0 fne fζ fb fHbd fAint farc

/-! ### The `a₁` (direct-germ) seam — constant `idx` with locally constant index

At an `a₁` seam (`T = −A`, where `(T−A)/2π ∈ (−1,−½) ∉ ℤ`) the floor `J` is locally constant, so
`idx` does not jump: the end field agrees with the single direct germ `glue u (idx ζ₀) ∘ endChart`,
`C²` by the IsSmooth seam clause once `endChart ζ₀ ∈ seamArc (idx ζ₀)`.  No `σ`, no `SeamVal`. -/
lemma endField_contDiffAt_seam_direct {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : IsSmooth 3 m u) (p : ℂ) (idx : ℂ → ZMod (2 * m)) {ζ₀ : ℂ}
    (hidx : ∀ᶠ ζ in nhds ζ₀, idx ζ = idx ζ₀)
    (harc : endChart p m ζ₀ ∈ seamArc 3 m (idx ζ₀)) :
    ContDiffAt ℝ 2 (endFieldWith p u idx) ζ₀ := by
  have hgC2 : ContDiffAt ℝ 2 (Surface.glue u (idx ζ₀)) (endChart p m ζ₀) :=
    (hu.2.1 (idx ζ₀) (endChart p m ζ₀) harc).of_le two_le_infty
  have hcomp : ContDiffAt ℝ 2 (fun ζ => Surface.glue u (idx ζ₀) (endChart p m ζ)) ζ₀ :=
    hgC2.comp ζ₀ (contDiffAt_endChart p m ζ₀)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hidx] with ζ hζ
  simp only [endFieldWith, hζ]

/-! ### The off-cut stitch — `C²` at every nonzero `ζ` off the principal cut

Trichotomy on `‖endChart ζ‖` vs `1`: off the circle (inside/outside) `idx` is locally constant
(`angJ_eventuallyEq`, since off-seam ⇒ `cos T ≠ cos A` ⇒ `(T−A)/2π ∉ ℤ`); on the circle (seam),
`cos_eq_cos_iff` splits into the `a₂` (`T=A`, reflected capstone) and `a₁` (`T=−A`, direct) families,
with the arc membership supplied by the single `c`-parity bit. -/

/-- Off-seam, off-cut: `C²` via `endField_contDiffAt_offSeam`, `idx` locally constant. -/
lemma endField_contDiffAt_offSeam_offCut {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hsmu : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (p : ℂ) (hp : ‖p‖ = 1) (c : ZMod (2 * m)) {ζ : ℂ}
    (hcut : 0 < ζ.re ∨ ζ.im ≠ 0) (hρ2 : ‖ζ‖ ^ m ≤ 2)
    (hoff : ‖endChart p m ζ‖ < 1 ∨ 1 < ‖endChart p m ζ‖) :
    ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ := by
  have hne1 : ‖endChart p m ζ‖ ≠ 1 := by
    rcases hoff with h | h
    · exact ne_of_lt h
    · exact (ne_of_lt h).symm
  have hns : ∀ k : ℤ, (angT p m ζ - angA m ζ) / (2 * Real.pi) ≠ (k : ℝ) := by
    intro k hk
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    rw [div_eq_iff hpi] at hk
    have hTeq : angT p m ζ = angA m ζ + (k : ℝ) * (2 * Real.pi) := by linarith [hk]
    have hcos : Real.cos (angT p m ζ) = Real.cos (angA m ζ) := by
      rw [hTeq, Real.cos_add_int_mul_two_pi]
    have h := endChart_normSq_sub_one_cos hp hρ2
    rw [hcos, sub_self, mul_zero] at h
    have hsq : ‖endChart p m ζ‖ ^ 2 = 1 := by rw [Complex.sq_norm]; linarith
    exact hne1 (by rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one])
  have hidx : ∀ᶠ ζ' in nhds ζ, endIdx m c p ζ' = endIdx m c p ζ := by
    filter_upwards [angJ_eventuallyEq hcut hns] with ζ' h
    simp only [endIdx, h]
  exact endField_contDiffAt_offSeam hsmu p (endIdx m c p) hidx hoff

/-- **Per-point off-cut `C²`.**  For every nonzero `ζ` off the principal cut (with `‖ζ‖^m < 1`),
the end field is `C²`, given the single `c`-parity bit `0 < (−1)^(parity c)·Im(p³)`.  Trichotomy on
`‖endChart ζ‖`: off the circle use the off-seam helper; on the circle split by `cos_eq_cos_iff` into
the `a₂` (reflected capstone) and `a₁` (direct seam) families. -/
lemma endField_contDiffAt_pt_offCut {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (p : ℂ) (hp : ‖p‖ = 1) (hpunc : p ∈ punctures 3) (hu : IsSmooth 3 m u) (hsv : SeamVal 3 u)
    (c : ZMod (2 * m)) {ζ : ℂ}
    (hcut : 0 < ζ.re ∨ ζ.im ≠ 0) (hζ : ζ ≠ 0) (hρ1 : ‖ζ‖ ^ m < 1)
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ 3).im) :
    ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ := by
  have hρ2 : ‖ζ‖ ^ m < 2 := lt_trans hρ1 one_lt_two
  have hρpos : 0 < ‖ζ‖ ^ m := pow_pos (norm_pos_iff.mpr hζ) m
  rcases lt_trichotomy (‖endChart p m ζ‖) 1 with hlt | heq | hgt
  · exact endField_contDiffAt_offSeam_offCut hu.1 p hp c hcut hρ2.le (Or.inl hlt)
  · -- SEAM: cos T = cos A
    have hcosA : Real.cos (angA m ζ) = -‖ζ‖ ^ m / 2 := by
      rw [angA]; exact Real.cos_arccos (by linarith) (by linarith)
    have hcosT : Real.cos (angT p m ζ) = Real.cos (angA m ζ) := by
      have h := endChart_normSq_sub_one_cos hp hρ2.le
      have hns1 : Complex.normSq (endChart p m ζ) = 1 := by
        rw [Complex.normSq_eq_norm_sq, heq]; norm_num
      rw [hns1] at h
      have h0 : 2 * ‖ζ‖ ^ m * (Real.cos (angT p m ζ) - Real.cos (angA m ζ)) = 0 := by linarith [h]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' (by positivity)
      · linarith [h']
    have hAmem := angA_mem hζ hρ2
    rw [Real.cos_eq_cos_iff] at hcosT
    obtain ⟨k, hk | hk⟩ := hcosT
    · -- a₂: angA = 2kπ + angT ⟹ T = A − 2kπ (N = −k)
      have hT2 : angT p m ζ = angA m ζ + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast; linear_combination -hk
      have hH0 : angT p m ζ - angA m ζ - 2 * Real.pi * (((-k : ℤ)) : ℝ) = 0 := by
        rw [hT2]; ring
      have hcosTA : Real.cos (angT p m ζ) = -‖ζ‖ ^ m / 2 := by
        rw [hT2, Real.cos_add_int_mul_two_pi, hcosA]
      have hsinT : 0 < Real.sin (angT p m ζ) := by
        rw [hT2, Real.sin_add_int_mul_two_pi]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hAmem.1, Real.pi_pos]) hAmem.2
      have hmem0 : endChart p m ζ ∈ seamArc 3 m (c + 2 * (((-k : ℤ)) : ZMod (2 * m)) - 1) :=
        arc_mem_a2 hpunc hp hζ hρ1 hcosTA hsinT heq (by rw [parity_add_two_mul]; exact hbit)
      exact endField_contDiffAt_seam_offCut p hp hu hsv c hζ hcut hρ2 hH0 hmem0
    · -- a₁: angA = 2kπ − angT ⟹ T = −A + 2kπ
      have hT2 : angT p m ζ = -angA m ζ + ((k : ℤ) : ℝ) * (2 * Real.pi) := by
        linear_combination hk
      have hcosTA : Real.cos (angT p m ζ) = -‖ζ‖ ^ m / 2 := by
        rw [hT2, Real.cos_add_int_mul_two_pi, Real.cos_neg, hcosA]
      have hsinT : Real.sin (angT p m ζ) < 0 := by
        rw [hT2, Real.sin_add_int_mul_two_pi, Real.sin_neg]
        have := Real.sin_pos_of_pos_of_lt_pi (show 0 < angA m ζ by linarith [hAmem.1, Real.pi_pos])
          hAmem.2
        linarith
      have hns : ∀ j : ℤ, (angT p m ζ - angA m ζ) / (2 * Real.pi) ≠ (j : ℝ) := by
        intro j hj
        have hpi : (2 * Real.pi) ≠ 0 := by positivity
        rw [div_eq_iff hpi] at hj
        have hcomb : -angA m ζ + ((k : ℤ) : ℝ) * (2 * Real.pi) - angA m ζ = (j : ℝ) * (2 * Real.pi) := by
          rw [← hT2]; exact hj
        have hApi : angA m ζ = ((k : ℝ) - (j : ℝ)) * Real.pi := by linear_combination (-1 / 2 : ℝ) * hcomb
        rw [hApi] at hAmem
        have hlo : (1 : ℝ) / 2 < (k : ℝ) - (j : ℝ) := by nlinarith [hAmem.1, Real.pi_pos]
        have hhi : (k : ℝ) - (j : ℝ) < 1 := by nlinarith [hAmem.2, Real.pi_pos]
        have hlo' : (0 : ℤ) < k - j := by
          have : (0 : ℝ) < ((k - j : ℤ) : ℝ) := by push_cast; linarith [hlo]
          exact_mod_cast this
        have hhi' : (k - j : ℤ) < 1 := by
          have : ((k - j : ℤ) : ℝ) < 1 := by push_cast; linarith [hhi]
          exact_mod_cast this
        omega
      have hidx : ∀ᶠ ζ' in nhds ζ, endIdx m c p ζ' = endIdx m c p ζ := by
        filter_upwards [angJ_eventuallyEq hcut hns] with ζ' h; simp only [endIdx, h]
      have hpe : parity m (endIdx m c p ζ + 1) = parity m c + 1 := by
        simp only [endIdx]; rw [map_add, map_one, parity_add_two_mul]
      have hpar : (-1 : ℝ) ^ (parity m (endIdx m c p ζ + 1)).val * (p ^ 3).im < 0 := by
        rw [hpe, neg_one_pow_parity_add_one]; nlinarith [hbit]
      exact endField_contDiffAt_seam_direct hu p (endIdx m c p) hidx
        (arc_mem_a1 hpunc hp hζ hρ1 hcosTA hsinT heq hpar)
  · exact endField_contDiffAt_offSeam_offCut hu.1 p hp c hcut hρ2.le (Or.inr hgt)

/-! ### The principal-cut extension via a continuous local lift

At a negative-real `ζ₀` the principal `arg` is discontinuous, so the lift `θ(ζ) = arg(−ζ) + π`
(continuous there, since `−ζ₀` is positive-real) replaces it.  `θ ζ ≡ arg ζ (mod 2π)` pointwise, and
`endIdx_arg_invariant` applies at each point with a point-dependent `q`; no local constancy of `q` is needed.  The `cos`/`sin` classification and arc pins are lift-invariant (`m` integral),
so only index local constancy and the neighborhood continuity inputs switch to `θ`. -/

/-- The lift `arg(−ζ) + π` is continuous off the positive real axis (in particular near a cut point). -/
lemma argLift_continuousAt {ζ₀ : ℂ} (h : ζ₀.re < 0 ∨ ζ₀.im ≠ 0) :
    ContinuousAt (fun ζ => Complex.arg (-ζ) + Real.pi) ζ₀ := by
  have hslit : -ζ₀ ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    rcases h with h | h
    · left; simpa using by linarith
    · right; simpa using h
  exact ((Complex.continuousAt_arg hslit).comp continuous_neg.continuousAt).add continuousAt_const

/-- The lift is congruent to the principal `arg` modulo `2π`: `arg(−ζ)+π = arg ζ + 2πq` for some `q`. -/
lemma argLift_arg_eq {ζ : ℂ} (hζ : ζ ≠ 0) :
    ∃ q : ℤ, Complex.arg (-ζ) + Real.pi = Complex.arg ζ + 2 * Real.pi * (q : ℝ) := by
  have hangle : ((Complex.arg (-ζ) + Real.pi : ℝ) : Real.Angle) = (Complex.arg ζ : Real.Angle) := by
    rw [Real.Angle.coe_add, Complex.arg_neg_coe_angle hζ, add_assoc, ← Real.Angle.coe_add,
      ← two_mul, Real.Angle.coe_two_pi, add_zero]
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hangle
  obtain ⟨q, hq⟩ := hangle
  exact ⟨q, by linarith [hq]⟩

/-- **Lift-based local constancy of `endIdx`.  Where a continuous lift `θ` agrees with
`arg` mod `2π` (pointwise, each `ζ` its own `q`) and the lifted floor is off-integer at `ζ₀`,
`endIdx` is locally constant — even across the principal cut, since the `2m`-jump cancels. -/
lemma endIdx_eventuallyEq_of_lift {m : ℕ} {p ζ₀ : ℂ} {c : ZMod (2 * m)} (θ : ℂ → ℝ)
    (hθc : ContinuousAt θ ζ₀)
    (hθq : ∀ᶠ ζ in nhds ζ₀, ∃ q : ℤ, θ ζ = Complex.arg ζ + 2 * Real.pi * (q : ℝ))
    (hns : ∀ k : ℤ,
      ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (k : ℝ)) :
    ∀ᶠ ζ in nhds ζ₀, endIdx m c p ζ = endIdx m c p ζ₀ := by
  set r : ℂ → ℝ :=
    fun ζ => ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ) / (2 * Real.pi) with hrdef
  have hA : ContinuousAt (fun ζ => angA m ζ) ζ₀ :=
    Real.continuous_arccos.continuousAt.comp
      (((continuous_norm.pow m).continuousAt).neg.div_const 2)
  have hrc : ContinuousAt r ζ₀ := by
    rw [hrdef]
    exact (((hθc.const_mul (m : ℝ)).sub continuousAt_const).sub hA).div_const _
  have hlt : ((⌊r ζ₀⌋ : ℤ) : ℝ) < r ζ₀ := lt_of_le_of_ne (Int.floor_le _) (fun h => hns _ h.symm)
  have hub : r ζ₀ < (⌊r ζ₀⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hJL : ∀ᶠ ζ in nhds ζ₀, ⌊r ζ⌋ = ⌊r ζ₀⌋ := by
    filter_upwards [hrc.eventually (Ioo_mem_nhds hlt hub)] with ζ hζ
    exact Int.floor_eq_iff.mpr ⟨le_of_lt hζ.1, hζ.2⟩
  have hEq : ∀ᶠ ζ in nhds ζ₀, endIdx m c p ζ = c + 2 * ((⌊r ζ⌋ : ℤ) : ZMod (2 * m)) := by
    filter_upwards [hθq] with ζ hq
    obtain ⟨q, hq⟩ := hq
    have hrζ : r ζ = ((m : ℝ) * (Complex.arg ζ + 2 * Real.pi * (q : ℝ)) - Complex.arg p
        - angA m ζ) / (2 * Real.pi) := by simp only [hrdef, hq]
    rw [hrζ]
    exact (endIdx_arg_invariant c p ζ q).symm
  filter_upwards [hJL, hEq] with ζ hjl heq
  rw [heq, hjl]
  exact (hEq.self_of_nhds).symm

/-! ### Lift-agnostic reusable pieces for the `a₂`-at-cut case

Generic floor values (not tied to `angT`), `endIdx`-value germ identities (key on the `endIdx`
value, not on `angJ`, so they hold for the lifted branch), and `cos` lift-invariance. -/

/-- Generic floor value: `0 ≤ y − 2πN < 2π ⇒ ⌊y/2π⌋ = N`. -/
lemma floor_div_two_pi_eq {y : ℝ} {N : ℤ} (hlo : 0 ≤ y - 2 * Real.pi * (N : ℝ))
    (hhi : y - 2 * Real.pi * (N : ℝ) < 2 * Real.pi) : ⌊y / (2 * Real.pi)⌋ = N := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfl : ⌊(y - 2 * Real.pi * (N : ℝ)) / (2 * Real.pi)⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [Int.cast_zero, le_div_iff₀ hpi]; nlinarith [hlo]
    · rw [Int.cast_zero, zero_add, div_lt_iff₀ hpi]; nlinarith [hhi]
  have key : y / (2 * Real.pi) = (y - 2 * Real.pi * (N : ℝ)) / (2 * Real.pi) + (N : ℝ) := by
    field_simp; ring
  rw [key, Int.floor_add_intCast, hfl, zero_add]

/-- Generic floor value: `−2π ≤ y − 2πN < 0 ⇒ ⌊y/2π⌋ = N − 1`. -/
lemma floor_div_two_pi_eq_sub_one {y : ℝ} {N : ℤ} (hlo : -(2 * Real.pi) ≤ y - 2 * Real.pi * (N : ℝ))
    (hhi : y - 2 * Real.pi * (N : ℝ) < 0) : ⌊y / (2 * Real.pi)⌋ = N - 1 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfl : ⌊(y - 2 * Real.pi * (N : ℝ)) / (2 * Real.pi)⌋ = -1 := by
    apply Int.floor_eq_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [Int.cast_neg, Int.cast_one, le_div_iff₀ hpi]; nlinarith [hlo]
    · rw [Int.cast_neg, Int.cast_one, div_lt_iff₀ hpi]; nlinarith [hhi]
  have key : y / (2 * Real.pi) = (y - 2 * Real.pi * (N : ℝ)) / (2 * Real.pi) + (N : ℝ) := by
    field_simp; ring
  rw [key, Int.floor_add_intCast, hfl]; ring

/-- `cos` lift-invariance: for `θv = arg ζ + 2πq`, `cos(m·θv − argp) = cos(angT)`. -/
lemma cos_lift_eq {p : ℂ} {m : ℕ} {ζ : ℂ} {θv : ℝ} {q : ℤ}
    (hq : θv = Complex.arg ζ + 2 * Real.pi * (q : ℝ)) :
    Real.cos ((m : ℝ) * θv - Complex.arg p) = Real.cos (angT p m ζ) := by
  rw [hq, angT, show (m : ℝ) * (Complex.arg ζ + 2 * Real.pi * (q : ℝ)) - Complex.arg p
      = ((m : ℝ) * Complex.arg ζ - Complex.arg p) + ((m * q : ℤ) : ℝ) * (2 * Real.pi) from by
        push_cast; ring, Real.cos_add_int_mul_two_pi]

/-- `sin` lift-invariance: for `θv = arg ζ + 2πq`, `sin(m·θv − argp) = sin(angT)`. -/
lemma sin_lift_eq {p : ℂ} {m : ℕ} {ζ : ℂ} {θv : ℝ} {q : ℤ}
    (hq : θv = Complex.arg ζ + 2 * Real.pi * (q : ℝ)) :
    Real.sin ((m : ℝ) * θv - Complex.arg p) = Real.sin (angT p m ζ) := by
  rw [hq, angT, show (m : ℝ) * (Complex.arg ζ + 2 * Real.pi * (q : ℝ)) - Complex.arg p
      = ((m : ℝ) * Complex.arg ζ - Complex.arg p) + ((m * q : ℤ) : ℝ) * (2 * Real.pi) from by
        push_cast; ring, Real.sin_add_int_mul_two_pi]

/-- **`endIdx`-value inside germ identity** (lift-agnostic): keyed on `endIdx ζ = c+2N`. -/
lemma endFieldWith_eq_reflected_inside_val {m : ℕ} (p : ℂ) (u : ZMod (2 * m) → ℂ → ℂ)
    (c : ZMod (2 * m)) {ζ : ℂ} {N : ℤ} (hv : endIdx m c p ζ = c + 2 * (N : ZMod (2 * m)))
    (hne : endChart p m ζ ≠ 0) (hlt : ‖endChart p m ζ‖ < 1) :
    endFieldWith p u (endIdx m c p) ζ
      = Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) (Bracket.σ (endChart p m ζ)) := by
  have hidx : c + 2 * (N : ZMod (2 * m)) - 1 + 1 = c + 2 * (N : ZMod (2 * m)) := by ring
  rw [glueSigma_inside u (c + 2 * (N : ZMod (2 * m)) - 1) hne hlt, hidx,
    endFieldWith_inside p u (endIdx m c p) (le_of_lt hlt), hv]

/-- **`endIdx`-value outside germ identity** (lift-agnostic): keyed on `endIdx ζ = c+2(N−1)`. -/
lemma endFieldWith_eq_reflected_outside_val {m : ℕ} (p : ℂ) (u : ZMod (2 * m) → ℂ → ℂ)
    (c : ZMod (2 * m)) {ζ : ℂ} {N : ℤ} (hv : endIdx m c p ζ = c + 2 * ((N - 1 : ℤ) : ZMod (2 * m)))
    (hgt : 1 < ‖endChart p m ζ‖) :
    endFieldWith p u (endIdx m c p) ζ
      = Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) (Bracket.σ (endChart p m ζ)) := by
  have hidx : c + 2 * ((N - 1 : ℤ) : ZMod (2 * m)) + 1 = c + 2 * (N : ZMod (2 * m)) - 1 := by
    push_cast; ring
  rw [glueSigma_outside u (c + 2 * (N : ZMod (2 * m)) - 1) hgt,
    endFieldWith_outside p u (endIdx m c p) hgt, hv, hidx]

/-- **`endIdx`-value seam germ identity** (lift-agnostic): keyed on `endIdx ζ = c+2N`. -/
lemma endFieldWith_eq_reflected_seam_val {k m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hsv : SeamVal k u) (c : ZMod (2 * m)) {ζ : ℂ} {N : ℤ}
    (hv : endIdx m c p ζ = c + 2 * (N : ZMod (2 * m)))
    (hmem : endChart p m ζ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1))
    (heq : ‖endChart p m ζ‖ = 1) :
    endFieldWith p u (endIdx m c p) ζ
      = Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) (Bracket.σ (endChart p m ζ)) := by
  have hLHS : endFieldWith p u (endIdx m c p) ζ = u (c + 2 * (N : ZMod (2 * m))) (endChart p m ζ) := by
    rw [endFieldWith_inside p u (endIdx m c p) (le_of_eq heq), hv]
  have hidx : c + 2 * (N : ZMod (2 * m)) - 1 + 1 = c + 2 * (N : ZMod (2 * m)) := by ring
  have hsvseam := hsv (c + 2 * (N : ZMod (2 * m)) - 1) (endChart p m ζ) hmem
  rw [hidx] at hsvseam
  have hRHS : Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) (Bracket.σ (endChart p m ζ))
      = u (c + 2 * (N : ZMod (2 * m)) - 1) (endChart p m ζ) := by
    rw [Bracket.σ_self heq]; simp only [Surface.glue, if_pos (le_of_eq heq)]
  rw [hLHS, hRHS]; exact hsvseam

/-! ### Generic (lifted-angle) classification — keyed on `cos s = cos(angT)`

With `s` the lifted angle `m·θ ζ − argp` (`cos s = cos(angT)` by `cos_lift_eq`), the sign of the
lifted `H' = s − angA − 2πN` gives inside/outside/seam, reusing `endChart_normSq_sub_one_cos`. -/

/-- Inside, generic: lifted `H' > 0 ⇒ ‖endChart‖ < 1`. -/
lemma norm_endChart_lt_one_gen {p : ℂ} (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0)
    (hb : ‖ζ‖ ^ m ≤ 2) {s : ℝ} {N : ℤ} (hcs : Real.cos s = Real.cos (angT p m ζ))
    (hA0 : 0 ≤ angA m ζ) (hAH : angA m ζ + (s - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi)
    (hHpos : 0 < s - angA m ζ - 2 * Real.pi * (N : ℝ)) : ‖endChart p m ζ‖ < 1 := by
  have hρ : 0 < ‖ζ‖ ^ m := pow_pos (norm_pos_iff.mpr hζ) m
  have hcos : Real.cos (angT p m ζ) < Real.cos (angA m ζ) := by
    rw [← hcs, ← show Real.cos (angA m ζ + (s - angA m ζ - 2 * Real.pi * (N : ℝ))) = Real.cos s from by
      rw [show angA m ζ + (s - angA m ζ - 2 * Real.pi * (N : ℝ)) = s + ((-N : ℤ) : ℝ) * (2 * Real.pi)
        from by push_cast; ring, Real.cos_add_int_mul_two_pi]]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hA0 hAH (by linarith)
  have hsub := endChart_normSq_sub_one_cos hp hb
  have hns' : Complex.normSq (endChart p m ζ) < 1 := by nlinarith [hsub, hcos, hρ]
  nlinarith [norm_nonneg (endChart p m ζ), Complex.sq_norm (endChart p m ζ), hns']

/-- Outside, generic: lifted `H' < 0 ⇒ 1 < ‖endChart‖`. -/
lemma one_lt_norm_endChart_gen {p : ℂ} (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ} (hζ : ζ ≠ 0)
    (hb : ‖ζ‖ ^ m ≤ 2) {s : ℝ} {N : ℤ} (hcs : Real.cos s = Real.cos (angT p m ζ))
    (hAH0 : 0 ≤ angA m ζ + (s - angA m ζ - 2 * Real.pi * (N : ℝ))) (hA : angA m ζ ≤ Real.pi)
    (hHneg : s - angA m ζ - 2 * Real.pi * (N : ℝ) < 0) : 1 < ‖endChart p m ζ‖ := by
  have hρ : 0 < ‖ζ‖ ^ m := pow_pos (norm_pos_iff.mpr hζ) m
  have hcos : Real.cos (angA m ζ) < Real.cos (angT p m ζ) := by
    rw [← hcs, ← show Real.cos (angA m ζ + (s - angA m ζ - 2 * Real.pi * (N : ℝ))) = Real.cos s from by
      rw [show angA m ζ + (s - angA m ζ - 2 * Real.pi * (N : ℝ)) = s + ((-N : ℤ) : ℝ) * (2 * Real.pi)
        from by push_cast; ring, Real.cos_add_int_mul_two_pi]]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hAH0 hA (by linarith)
  have hsub := endChart_normSq_sub_one_cos hp hb
  have hns' : 1 < Complex.normSq (endChart p m ζ) := by nlinarith [hsub, hcos, hρ]
  nlinarith [norm_nonneg (endChart p m ζ), Complex.sq_norm (endChart p m ζ), hns']

/-- Seam, generic: lifted `H' = 0 ⇒ ‖endChart‖ = 1`. -/
lemma norm_endChart_eq_one_gen {p : ℂ} (hp : ‖p‖ = 1) {m : ℕ} {ζ : ℂ} (hb : ‖ζ‖ ^ m ≤ 2)
    {s : ℝ} {N : ℤ} (hcs : Real.cos s = Real.cos (angT p m ζ))
    (hH0 : s - angA m ζ - 2 * Real.pi * (N : ℝ) = 0) : ‖endChart p m ζ‖ = 1 := by
  have hcos : Real.cos (angT p m ζ) = Real.cos (angA m ζ) := by
    rw [← hcs, show s = angA m ζ + ((N : ℤ) : ℝ) * (2 * Real.pi) from by linear_combination hH0,
      Real.cos_add_int_mul_two_pi]
  have hsub := endChart_normSq_sub_one_cos hp hb
  rw [hcos, sub_self, mul_zero] at hsub
  have hsq : ‖endChart p m ζ‖ ^ 2 = 1 := by rw [Complex.sq_norm]; linarith
  rw [← Real.sqrt_sq (norm_nonneg (endChart p m ζ)), hsq, Real.sqrt_one]

/-- Reflected-germ matching through an angular lift, including at principal-cut
points. The lift agrees pointwise with `arg` modulo `2π`; the stated neighborhood
hypotheses supply the bounds and arc membership used in the trichotomy.
Continuity of the lift is not required by this lemma. The index is read from
the lifted floor using `endIdx_arg_invariant`, and the generic classification
identifies the inside, outside and seam cases. -/
lemma endFieldWith_reflected_eventuallyEq_lift {m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hp : ‖p‖ = 1) (hsv : SeamVal 3 u) (c : ZMod (2 * m)) {ζ₀ : ℂ} {N : ℤ} (θ : ℂ → ℝ)
    (hθq : ∀ᶠ ζ in nhds ζ₀, ∃ q : ℤ, θ ζ = Complex.arg ζ + 2 * Real.pi * (q : ℝ))
    (hne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0)
    (hζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0)
    (hb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2)
    (hHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < (m : ℝ) * θ ζ - Complex.arg p - angA m ζ
        - 2 * Real.pi * (N : ℝ) ∧ (m : ℝ) * θ ζ - Complex.arg p - angA m ζ
        - 2 * Real.pi * (N : ℝ) < 2 * Real.pi)
    (hAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
        ∧ 0 ≤ angA m ζ + ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ))
        ∧ angA m ζ + ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi)
    (harc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
        endChart p m ζ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    endFieldWith p u (endIdx m c p)
      =ᶠ[nhds ζ₀] fun ζ => Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1)
        (Bracket.σ (endChart p m ζ)) := by
  filter_upwards [hθq, hne, hζ, hb, hHbd, hAint, harc] with ζ hq hne hζ hb hHbd hAint harc
  obtain ⟨q, hq⟩ := hq
  obtain ⟨hA0, hAle, hAH0, hAHle⟩ := hAint
  have hcs : Real.cos ((m : ℝ) * θ ζ - Complex.arg p) = Real.cos (angT p m ζ) := cos_lift_eq hq
  have hendIdx : endIdx m c p ζ = c + 2 *
      ((⌊((m : ℝ) * θ ζ - Complex.arg p - angA m ζ) / (2 * Real.pi)⌋ : ℤ) : ZMod (2 * m)) := by
    rw [show ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ)
        = ((m : ℝ) * (Complex.arg ζ + 2 * Real.pi * (q : ℝ)) - Complex.arg p - angA m ζ)
        from by rw [hq]]
    exact (endIdx_arg_invariant c p ζ q).symm
  rcases lt_trichotomy ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ)) 0
    with hlt | heq | hgt
  · have hfl : ⌊((m : ℝ) * θ ζ - Complex.arg p - angA m ζ) / (2 * Real.pi)⌋ = N - 1 :=
      floor_div_two_pi_eq_sub_one (le_of_lt hHbd.1) hlt
    have hv : endIdx m c p ζ = c + 2 * ((N - 1 : ℤ) : ZMod (2 * m)) := by rw [hendIdx, hfl]
    exact endFieldWith_eq_reflected_outside_val p u c hv
      (one_lt_norm_endChart_gen hp hζ hb hcs hAH0 hAle hlt)
  · have hfl : ⌊((m : ℝ) * θ ζ - Complex.arg p - angA m ζ) / (2 * Real.pi)⌋ = N :=
      floor_div_two_pi_eq (le_of_eq heq.symm) hHbd.2
    have hv : endIdx m c p ζ = c + 2 * (N : ZMod (2 * m)) := by rw [hendIdx, hfl]
    have hseam : ‖endChart p m ζ‖ = 1 := norm_endChart_eq_one_gen hp hb hcs heq
    exact endFieldWith_eq_reflected_seam_val p hsv c hv (harc hseam) hseam
  · have hfl : ⌊((m : ℝ) * θ ζ - Complex.arg p - angA m ζ) / (2 * Real.pi)⌋ = N :=
      floor_div_two_pi_eq (le_of_lt hgt) hHbd.2
    have hv : endIdx m c p ζ = c + 2 * (N : ZMod (2 * m)) := by rw [hendIdx, hfl]
    exact endFieldWith_eq_reflected_inside_val p u c hv hne
      (norm_endChart_lt_one_gen hp hζ hb hcs hA0 hAHle hgt)

/-- **`a₂`-at-cut seam capstone** (lift-based).  From θ-continuity it builds the
`∀ᶠ` hypotheses of `endFieldWith_reflected_eventuallyEq_lift` for the lifted `H'`, matches the reflected germ,
and composes with the germ `C²` (IsSmooth seam clause + σ + endChart). -/
lemma endField_contDiffAt_seam_lift {m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hp : ‖p‖ = 1) (hu : IsSmooth 3 m u) (hsv : SeamVal 3 u) (c : ZMod (2 * m)) {ζ₀ : ℂ} {N : ℤ}
    (θ : ℂ → ℝ) (hθc : ContinuousAt θ ζ₀)
    (hθq : ∀ᶠ ζ in nhds ζ₀, ∃ q : ℤ, θ ζ = Complex.arg ζ + 2 * Real.pi * (q : ℝ))
    (hζ₀ : ζ₀ ≠ 0) (hb0 : ‖ζ₀‖ ^ m < 2)
    (hH0 : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (N : ℝ) = 0)
    (hmem0 : endChart p m ζ₀ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ₀ := by
  obtain ⟨q0, hq0⟩ := hθq.self_of_nhds
  have hcs0 : Real.cos ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.cos (angT p m ζ₀) := cos_lift_eq hq0
  have hseam0 : ‖endChart p m ζ₀‖ = 1 := norm_endChart_eq_one_gen hp hb0.le hcs0 hH0
  have hne0 : endChart p m ζ₀ ≠ 0 := norm_pos_iff.mp (by rw [hseam0]; norm_num)
  have hendcont : ContinuousAt (endChart p m) ζ₀ := (contDiffAt_endChart p m ζ₀).continuousAt
  have hA : ContinuousAt (fun ζ => angA m ζ) ζ₀ :=
    Real.continuous_arccos.continuousAt.comp
      (((continuous_norm.pow m).continuousAt).neg.div_const 2)
  have hH : ContinuousAt
      (fun ζ => (m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ)) ζ₀ :=
    (((hθc.const_mul (m : ℝ)).sub continuousAt_const).sub hA).sub continuousAt_const
  have hAmem := angA_mem hζ₀ hb0
  have hA0 : angA m ζ₀ ∈ Set.Ioo 0 Real.pi := ⟨by linarith [Real.pi_pos, hAmem.1], hAmem.2⟩
  have fne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0 := hendcont.eventually_ne hne0
  have fζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0 := isOpen_ne.mem_nhds hζ₀
  have hb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2 := by
    filter_upwards [(continuous_norm.pow m).continuousAt.eventually_lt continuousAt_const hb0]
      with ζ h using h.le
  have fHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < (m : ℝ) * θ ζ - Complex.arg p - angA m ζ
      - 2 * Real.pi * (N : ℝ) ∧ (m : ℝ) * θ ζ - Complex.arg p - angA m ζ
      - 2 * Real.pi * (N : ℝ) < 2 * Real.pi := by
    have hmem : Set.Ioo (-(2 * Real.pi)) (2 * Real.pi)
        ∈ nhds ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (N : ℝ)) := by
      rw [hH0]; exact Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    filter_upwards [hH.eventually hmem] with ζ h using ⟨h.1, h.2⟩
  have fAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
      ∧ 0 ≤ angA m ζ + ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ))
      ∧ angA m ζ + ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi := by
    have hmemA : Set.Ioo 0 Real.pi ∈ nhds (angA m ζ₀) := Ioo_mem_nhds hA0.1 hA0.2
    have hmemAH : Set.Ioo 0 Real.pi ∈ nhds (angA m ζ₀ + ((m : ℝ) * θ ζ₀ - Complex.arg p
        - angA m ζ₀ - 2 * Real.pi * (N : ℝ))) := by
      have hval : angA m ζ₀ + ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (N : ℝ))
          = angA m ζ₀ := by rw [hH0]; ring
      rw [hval]; exact Ioo_mem_nhds hA0.1 hA0.2
    filter_upwards [hA.eventually hmemA, (hA.add hH).eventually hmemAH] with ζ hfa hfah
    exact ⟨hfa.1.le, hfa.2.le, hfah.1.le, hfah.2.le⟩
  have farc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
      endChart p m ζ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1) := by
    have hsign0 : (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ₀) ^ 3).re < 0 := by
      have h := hmem0; simp only [seamArc, arc, Set.mem_ofPred_eq] at h; exact h.2
    have hgcont : ContinuousAt (fun ζ => (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ) ^ 3).re) ζ₀ :=
      continuousAt_const.mul (Complex.continuous_re.continuousAt.comp (hendcont.pow 3))
    filter_upwards [hgcont.eventually_lt continuousAt_const hsign0] with ζ hg hnorm
    simp only [seamArc, arc, Set.mem_ofPred_eq]
    exact ⟨hnorm, hg⟩
  have hmatch := endFieldWith_reflected_eventuallyEq_lift p hp hsv c θ hθq fne fζ hb fHbd fAint farc
  have hσ0 : Bracket.σ (endChart p m ζ₀) = endChart p m ζ₀ := Bracket.σ_self hseam0
  have hglueσ : ContDiffAt ℝ 2 (Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1))
      (Bracket.σ (endChart p m ζ₀)) := by
    rw [hσ0]
    exact (hu.2.1 (c + 2 * (N : ZMod (2 * m)) - 1) (endChart p m ζ₀) hmem0).of_le two_le_infty
  have hfσ : ContDiffAt ℝ 2 (fun ζ => Bracket.σ (endChart p m ζ)) ζ₀ :=
    ((Bracket.contDiffAt_σ hne0).of_le two_le_infty).comp ζ₀ (contDiffAt_endChart p m ζ₀)
  have hcomp : ContDiffAt ℝ 2
      (Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) ∘ fun ζ => Bracket.σ (endChart p m ζ)) ζ₀ :=
    hglueσ.comp ζ₀ hfσ
  exact hcomp.congr_of_eventuallyEq hmatch

/-- **Per-point `C²` on the principal cut.**  For a negative-real `ζ₀`, the lift `θ=arg(−ζ)+π`
(continuous there) drives the same trichotomy: off-seam and `a₁` use lift-based index local
constancy; `a₂` uses the lift-based seam capstone.  The single `c`-parity bit discharges both arc
memberships (the `cos`/`sin` of `angT` at `ζ₀` are pointwise, hence usable despite the cut). -/
lemma endField_contDiffAt_pt_cut {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (p : ℂ) (hp : ‖p‖ = 1) (hpunc : p ∈ punctures 3) (hu : IsSmooth 3 m u) (hsv : SeamVal 3 u)
    (c : ZMod (2 * m)) {ζ₀ : ℂ} (hcre : ζ₀.re < 0) (hρ1 : ‖ζ₀‖ ^ m < 1)
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ 3).im) :
    ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ₀ := by
  have hζ₀ : ζ₀ ≠ 0 := fun h => by simp [h] at hcre
  have hρ2 : ‖ζ₀‖ ^ m < 2 := lt_trans hρ1 one_lt_two
  have hρpos : 0 < ‖ζ₀‖ ^ m := pow_pos (norm_pos_iff.mpr hζ₀) m
  set θ : ℂ → ℝ := fun ζ => Complex.arg (-ζ) + Real.pi with hθdef
  have hθc : ContinuousAt θ ζ₀ := argLift_continuousAt (Or.inl hcre)
  have hθq : ∀ᶠ ζ in nhds ζ₀, ∃ q : ℤ, θ ζ = Complex.arg ζ + 2 * Real.pi * (q : ℝ) := by
    filter_upwards [isOpen_ne.mem_nhds hζ₀] with ζ hζ using argLift_arg_eq hζ
  obtain ⟨q0, hq0⟩ := hθq.self_of_nhds
  have hcs0 : Real.cos ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.cos (angT p m ζ₀) := cos_lift_eq hq0
  have hsn0 : Real.sin ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.sin (angT p m ζ₀) := sin_lift_eq hq0
  rcases lt_trichotomy (‖endChart p m ζ₀‖) 1 with hlt | heq | hgt
  · have hns : ∀ k : ℤ, ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (k : ℝ) := by
      intro k hk
      rw [div_eq_iff (by positivity)] at hk
      have hH0k : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (k : ℝ) = 0 := by
        linear_combination hk
      rw [norm_endChart_eq_one_gen hp hρ2.le hcs0 hH0k] at hlt; exact lt_irrefl 1 hlt
    exact endField_contDiffAt_offSeam hu.1 p (endIdx m c p)
      (endIdx_eventuallyEq_of_lift θ hθc hθq hns) (Or.inl hlt)
  · have hcosA : Real.cos (angA m ζ₀) = -‖ζ₀‖ ^ m / 2 := by
      rw [angA]; exact Real.cos_arccos (by linarith) (by linarith)
    have hcosT : Real.cos (angT p m ζ₀) = Real.cos (angA m ζ₀) := by
      have h := endChart_normSq_sub_one_cos hp hρ2.le
      have hns1 : Complex.normSq (endChart p m ζ₀) = 1 := by
        rw [Complex.normSq_eq_norm_sq, heq]; norm_num
      rw [hns1] at h
      have h0 : 2 * ‖ζ₀‖ ^ m * (Real.cos (angT p m ζ₀) - Real.cos (angA m ζ₀)) = 0 := by linarith [h]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' (by positivity)
      · linarith [h']
    have hAmem := angA_mem hζ₀ hρ2
    have hcosTA : Real.cos (angT p m ζ₀) = -‖ζ₀‖ ^ m / 2 := by rw [hcosT, hcosA]
    have hcosS : Real.cos ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.cos (angA m ζ₀) := by rw [hcs0, hcosT]
    rw [Real.cos_eq_cos_iff] at hcosS
    obtain ⟨k, hk | hk⟩ := hcosS
    · have hH0 : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (((-k : ℤ)) : ℝ) = 0 := by
        push_cast; linear_combination -hk
      have hsinT : 0 < Real.sin (angT p m ζ₀) := by
        rw [← hsn0, show (m : ℝ) * θ ζ₀ - Complex.arg p
            = angA m ζ₀ + ((-k : ℤ) : ℝ) * (2 * Real.pi) from by push_cast; linear_combination -hk,
          Real.sin_add_int_mul_two_pi]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hAmem.1, Real.pi_pos]) hAmem.2
      have hmem0 : endChart p m ζ₀ ∈ seamArc 3 m (c + 2 * (((-k : ℤ)) : ZMod (2 * m)) - 1) :=
        arc_mem_a2 hpunc hp hζ₀ hρ1 hcosTA hsinT heq (by rw [parity_add_two_mul]; exact hbit)
      exact endField_contDiffAt_seam_lift p hp hu hsv c θ hθc hθq hζ₀ hρ2 hH0 hmem0
    · have hsS : (m : ℝ) * θ ζ₀ - Complex.arg p = -angA m ζ₀ + ((k : ℤ) : ℝ) * (2 * Real.pi) := by
        linear_combination hk
      have hsinT : Real.sin (angT p m ζ₀) < 0 := by
        rw [← hsn0, hsS, Real.sin_add_int_mul_two_pi, Real.sin_neg]
        have := Real.sin_pos_of_pos_of_lt_pi (show 0 < angA m ζ₀ by linarith [hAmem.1, Real.pi_pos])
          hAmem.2
        linarith
      have hns : ∀ j : ℤ, ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (j : ℝ) := by
        intro j hj
        rw [div_eq_iff (by positivity)] at hj
        rw [hsS] at hj
        have hApi : angA m ζ₀ = ((k : ℝ) - (j : ℝ)) * Real.pi := by linear_combination (-1 / 2 : ℝ) * hj
        rw [hApi] at hAmem
        have hlo : (1 : ℝ) / 2 < (k : ℝ) - (j : ℝ) := by nlinarith [hAmem.1, Real.pi_pos]
        have hhi : (k : ℝ) - (j : ℝ) < 1 := by nlinarith [hAmem.2, Real.pi_pos]
        have hlo' : (0 : ℤ) < k - j := by
          have hh : (0 : ℝ) < ((k - j : ℤ) : ℝ) := by push_cast; linarith [hlo]
          exact_mod_cast hh
        have hhi' : (k - j : ℤ) < 1 := by
          have hh : ((k - j : ℤ) : ℝ) < 1 := by push_cast; linarith [hhi]
          exact_mod_cast hh
        omega
      have hpe : parity m (endIdx m c p ζ₀ + 1) = parity m c + 1 := by
        simp only [endIdx]; rw [map_add, map_one, parity_add_two_mul]
      have hpar : (-1 : ℝ) ^ (parity m (endIdx m c p ζ₀ + 1)).val * (p ^ 3).im < 0 := by
        rw [hpe, neg_one_pow_parity_add_one]; nlinarith [hbit]
      exact endField_contDiffAt_seam_direct hu p (endIdx m c p)
        (endIdx_eventuallyEq_of_lift θ hθc hθq hns)
        (arc_mem_a1 hpunc hp hζ₀ hρ1 hcosTA hsinT heq hpar)
  · have hns : ∀ k : ℤ, ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (k : ℝ) := by
      intro k hk
      rw [div_eq_iff (by positivity)] at hk
      have hH0k : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (k : ℝ) = 0 := by
        linear_combination hk
      rw [norm_endChart_eq_one_gen hp hρ2.le hcs0 hH0k] at hgt; exact lt_irrefl 1 hgt
    exact endField_contDiffAt_offSeam hu.1 p (endIdx m c p)
      (endIdx_eventuallyEq_of_lift θ hθc hθq hns) (Or.inr hgt)

/-- **Regularity on the punctured chart.**  The end field `endFieldWith p u (endIdx m c p)` is `C²` at every nonzero
`ζ` with `‖ζ‖^m < 1`, given the single `c`-parity bit.  Off the principal cut use
`endField_contDiffAt_pt_offCut`; on it (`ζ` negative-real) use `endField_contDiffAt_pt_cut`. -/
theorem endField_contDiffAt_punctured {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ) (hp : ‖p‖ = 1)
    (hpunc : p ∈ punctures 3) (hu : IsSmooth 3 m u) (hsv : SeamVal 3 u) (c : ZMod (2 * m))
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ 3).im) :
    ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ ^ m < 1 → ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ := by
  intro ζ hζ hρ1
  by_cases hcut : 0 < ζ.re ∨ ζ.im ≠ 0
  · exact endField_contDiffAt_pt_offCut p hp hpunc hu hsv c hcut hζ hρ1 hbit
  · rw [not_or, not_lt, not_ne_iff] at hcut
    have hcre : ζ.re < 0 := lt_of_le_of_ne hcut.1
      (fun h => hζ (Complex.ext (by rw [Complex.zero_re]; exact h)
        (by rw [Complex.zero_im]; exact hcut.2)))
    exact endField_contDiffAt_pt_cut p hp hpunc hu hsv c hcre hρ1 hbit

/-! ### The complex PDE `Δ F + endPotential·F = 0` (feeds `hre`/`him`)

For the removability PDE, the end field satisfies the pulled-back Jacobi equation at nonzero
`ζ` with `‖ζ‖^m < 1`, under the smoothness, Jacobi, seam-normalization and parity hypotheses.  The regularity proof supplies the same germs: off-seam the direct germ `glue u n`, at the `a₂` seam the
reflected germ `(glue u j')∘σ`.  Both are `C²` and solve `ΔH + potV 3 · H = 0` at `endChart ζ`
(the glue equation lemmas and `comp_sigma_flat`), so `endComp_of_flat` + `laplacian_congr_of_eventuallyEq` transfer the equation. -/

/-- The reflected germ `(glue u j)∘σ` is `C²` at a seam point `w₀ ∈ seamArc j`. -/
lemma reflectedGerm_contDiffAt {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : IsSmooth 3 m u)
    (j : ZMod (2 * m)) {w₀ : ℂ} (hmem : w₀ ∈ seamArc 3 m j) (heq : ‖w₀‖ = 1) :
    ContDiffAt ℝ 2 (Surface.glue u j ∘ Bracket.σ) w₀ := by
  have hw0 : w₀ ≠ 0 := norm_pos_iff.mp (by rw [heq]; norm_num)
  have hg : ContDiffAt ℝ 2 (Surface.glue u j) (Bracket.σ w₀) := by
    rw [Bracket.σ_self heq]; exact (hu.2.1 j w₀ hmem).of_le two_le_infty
  exact hg.comp w₀ ((Bracket.contDiffAt_σ hw0).of_le two_le_infty)

/-- The reflected germ `(glue u j)∘σ` solves the flat-coordinate Jacobi equation at a seam point `w₀ ∈ seamArc j` (via
`comp_sigma_flat`, since `σ` fixes `w₀`). -/
lemma reflectedGerm_flat {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : IsSmooth 3 m u)
    (hjac : IsJacobiField 3 m u) (j : ZMod (2 * m)) {w₀ : ℂ} (hmem : w₀ ∈ seamArc 3 m j)
    (heq : ‖w₀‖ = 1) :
    laplacian (Surface.glue u j ∘ Bracket.σ) w₀
      + (potV 3 w₀ : ℂ) * (Surface.glue u j ∘ Bracket.σ) w₀ = 0 := by
  have hw0 : w₀ ≠ 0 := norm_pos_iff.mp (by rw [heq]; norm_num)
  refine comp_sigma_flat hw0 ?_ ?_
  · rw [Bracket.σ_self heq]; exact (hu.2.1 j w₀ hmem).of_le two_le_infty
  · rw [Bracket.σ_self heq]; exact glue_flat_jacobi hu hjac j hmem

/-- **PDE transfer.**  If the end field agrees near `ζ` with `H ∘ endChart` for a `w`-germ `H` that
is `C²` and solves the flat-coordinate Jacobi equation at `endChart ζ`, then the end field solves the pulled-back equation
`Δ F + endPotential·F = 0` at `ζ` (`endComp_of_flat` + `laplacian_congr_of_eventuallyEq`). -/
lemma endField_laplacian_of_germ {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ) (c : ZMod (2 * m))
    {ζ : ℂ} (H : ℂ → ℂ)
    (hEq : endFieldWith p u (endIdx m c p) =ᶠ[nhds ζ] fun z => H (endChart p m z))
    (hC2 : ContDiffAt ℝ 2 H (endChart p m ζ))
    (hflat : laplacian H (endChart p m ζ)
      + (potV 3 (endChart p m ζ) : ℂ) * H (endChart p m ζ) = 0) :
    laplacian (endFieldWith p u (endIdx m c p)) ζ
      + (endPotential p m ζ : ℂ) * endFieldWith p u (endIdx m c p) ζ = 0 := by
  have hF : endFieldWith p u (endIdx m c p) ζ = H (endChart p m ζ) := hEq.self_of_nhds
  rw [laplacian_congr_of_eventuallyEq hEq, hF]
  exact endComp_of_flat p hC2 hflat

/-- **`a₂` off-cut germ representation.**  Mirrors `endField_contDiffAt_seam_offCut`'s `∀ᶠ`
derivation but returns the reflected germ `(glue u (c+2N−1))∘σ` together with its `=ᶠ` match, `C²`,
and the flat-coordinate Jacobi equation at `endChart ζ₀` — the input to `endField_laplacian_of_germ`. -/
lemma endField_germ_rep_seam_offCut {m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ} (hp : ‖p‖ = 1)
    (hu : IsSmooth 3 m u) (hjac : IsJacobiField 3 m u) (hsv : SeamVal 3 u) (c : ZMod (2 * m))
    {ζ₀ : ℂ} {N : ℤ} (hζ₀ : ζ₀ ≠ 0) (hcut : 0 < ζ₀.re ∨ ζ₀.im ≠ 0) (hb0 : ‖ζ₀‖ ^ m < 2)
    (hH0 : angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ) = 0)
    (hmem0 : endChart p m ζ₀ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    ∃ H : ℂ → ℂ, (endFieldWith p u (endIdx m c p) =ᶠ[nhds ζ₀] fun z => H (endChart p m z))
      ∧ ContDiffAt ℝ 2 H (endChart p m ζ₀)
      ∧ laplacian H (endChart p m ζ₀) + (potV 3 (endChart p m ζ₀) : ℂ) * H (endChart p m ζ₀) = 0 := by
  have hendcont : ContinuousAt (endChart p m) ζ₀ := (contDiffAt_endChart p m ζ₀).continuousAt
  have hA : ContinuousAt (fun ζ => angA m ζ) ζ₀ :=
    Real.continuous_arccos.continuousAt.comp
      (((continuous_norm.pow m).continuousAt).neg.div_const 2)
  have hT : ContinuousAt (fun ζ => angT p m ζ) ζ₀ :=
    ((Complex.continuousAt_arg hcut).const_mul (m : ℝ)).sub continuousAt_const
  have hH : ContinuousAt (fun ζ => angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ζ₀ :=
    (hT.sub hA).sub continuousAt_const
  have hseam0 : ‖endChart p m ζ₀‖ = 1 := norm_endChart_eq_one hp hb0.le hH0
  have hne0 : endChart p m ζ₀ ≠ 0 := norm_pos_iff.mp (by rw [hseam0]; norm_num)
  have hAmem := angA_mem hζ₀ hb0
  have hA0 : angA m ζ₀ ∈ Set.Ioo 0 Real.pi := ⟨by linarith [Real.pi_pos, hAmem.1], hAmem.2⟩
  have fne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0 := hendcont.eventually_ne hne0
  have fζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0 := isOpen_ne.mem_nhds hζ₀
  have fb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2 := by
    filter_upwards [(continuous_norm.pow m).continuousAt.eventually_lt continuousAt_const hb0]
      with ζ h using h.le
  have fHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)
      ∧ angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ) < 2 * Real.pi := by
    have hmem : Set.Ioo (-(2 * Real.pi)) (2 * Real.pi)
        ∈ nhds (angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ)) := by
      rw [hH0]; exact Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    filter_upwards [hH.eventually hmem] with ζ h using ⟨h.1, h.2⟩
  have fAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
      ∧ 0 ≤ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ))
      ∧ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi := by
    have hmemA : Set.Ioo 0 Real.pi ∈ nhds (angA m ζ₀) := Ioo_mem_nhds hA0.1 hA0.2
    have hmemAH : Set.Ioo 0 Real.pi
        ∈ nhds (angA m ζ₀ + (angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ))) := by
      have hval : angA m ζ₀ + (angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ)) = angA m ζ₀ := by
        rw [hH0]; ring
      rw [hval]; exact Ioo_mem_nhds hA0.1 hA0.2
    filter_upwards [hA.eventually hmemA, (hA.add hH).eventually hmemAH] with ζ hfa hfah
    exact ⟨hfa.1.le, hfa.2.le, hfah.1.le, hfah.2.le⟩
  have farc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
      endChart p m ζ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1) := by
    have hsign0 : (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ₀) ^ 3).re < 0 := by
      have h := hmem0; simp only [seamArc, arc, Set.mem_ofPred_eq] at h; exact h.2
    have hgcont : ContinuousAt (fun ζ => (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ) ^ 3).re) ζ₀ :=
      continuousAt_const.mul (Complex.continuous_re.continuousAt.comp (hendcont.pow 3))
    filter_upwards [hgcont.eventually_lt continuousAt_const hsign0] with ζ hg hnorm
    simp only [seamArc, arc, Set.mem_ofPred_eq]
    exact ⟨hnorm, hg⟩
  exact ⟨Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) ∘ Bracket.σ,
    endFieldWith_reflected_eventuallyEq p hp hsv c fne fζ fb fHbd fAint farc,
    reflectedGerm_contDiffAt hu (c + 2 * (N : ZMod (2 * m)) - 1) hmem0 hseam0,
    reflectedGerm_flat hu hjac (c + 2 * (N : ZMod (2 * m)) - 1) hmem0 hseam0⟩

/-- **Direct germ representation** (off-seam / `a₁`): with `idx` locally constant and `glue u (idx ζ)`
`C²` and satisfies the Jacobi equation at `endChart ζ`, the field agrees with `glue u (idx ζ) ∘ endChart`. -/
lemma endField_germ_rep_direct {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ) (c : ZMod (2 * m)) {ζ : ℂ}
    (hidx : ∀ᶠ ζ' in nhds ζ, endIdx m c p ζ' = endIdx m c p ζ)
    (hC2 : ContDiffAt ℝ 2 (Surface.glue u (endIdx m c p ζ)) (endChart p m ζ))
    (hflat : laplacian (Surface.glue u (endIdx m c p ζ)) (endChart p m ζ)
      + (potV 3 (endChart p m ζ) : ℂ) * Surface.glue u (endIdx m c p ζ) (endChart p m ζ) = 0) :
    ∃ H : ℂ → ℂ, (endFieldWith p u (endIdx m c p) =ᶠ[nhds ζ] fun z => H (endChart p m z))
      ∧ ContDiffAt ℝ 2 H (endChart p m ζ)
      ∧ laplacian H (endChart p m ζ) + (potV 3 (endChart p m ζ) : ℂ) * H (endChart p m ζ) = 0 := by
  refine ⟨Surface.glue u (endIdx m c p ζ), ?_, hC2, hflat⟩
  filter_upwards [hidx] with z hz
  simp only [endFieldWith, hz]

/-- **`a₂` cut germ representation.**  The lift-based counterpart of `endField_germ_rep_seam_offCut`
for a seam point on the principal cut (mirrors `endField_contDiffAt_seam_lift`'s `∀ᶠ` derivation). -/
lemma endField_germ_rep_seam_lift {m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ} (hp : ‖p‖ = 1)
    (hu : IsSmooth 3 m u) (hjac : IsJacobiField 3 m u) (hsv : SeamVal 3 u) (c : ZMod (2 * m))
    {ζ₀ : ℂ} {N : ℤ} (θ : ℂ → ℝ) (hθc : ContinuousAt θ ζ₀)
    (hθq : ∀ᶠ ζ in nhds ζ₀, ∃ q : ℤ, θ ζ = Complex.arg ζ + 2 * Real.pi * (q : ℝ))
    (hζ₀ : ζ₀ ≠ 0) (hb0 : ‖ζ₀‖ ^ m < 2)
    (hH0 : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (N : ℝ) = 0)
    (hmem0 : endChart p m ζ₀ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    ∃ H : ℂ → ℂ, (endFieldWith p u (endIdx m c p) =ᶠ[nhds ζ₀] fun z => H (endChart p m z))
      ∧ ContDiffAt ℝ 2 H (endChart p m ζ₀)
      ∧ laplacian H (endChart p m ζ₀) + (potV 3 (endChart p m ζ₀) : ℂ) * H (endChart p m ζ₀) = 0 := by
  obtain ⟨q0, hq0⟩ := hθq.self_of_nhds
  have hcs0 : Real.cos ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.cos (angT p m ζ₀) := cos_lift_eq hq0
  have hseam0 : ‖endChart p m ζ₀‖ = 1 := norm_endChart_eq_one_gen hp hb0.le hcs0 hH0
  have hne0 : endChart p m ζ₀ ≠ 0 := norm_pos_iff.mp (by rw [hseam0]; norm_num)
  have hendcont : ContinuousAt (endChart p m) ζ₀ := (contDiffAt_endChart p m ζ₀).continuousAt
  have hA : ContinuousAt (fun ζ => angA m ζ) ζ₀ :=
    Real.continuous_arccos.continuousAt.comp
      (((continuous_norm.pow m).continuousAt).neg.div_const 2)
  have hH : ContinuousAt
      (fun ζ => (m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ)) ζ₀ :=
    (((hθc.const_mul (m : ℝ)).sub continuousAt_const).sub hA).sub continuousAt_const
  have hAmem := angA_mem hζ₀ hb0
  have hA0 : angA m ζ₀ ∈ Set.Ioo 0 Real.pi := ⟨by linarith [Real.pi_pos, hAmem.1], hAmem.2⟩
  have fne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0 := hendcont.eventually_ne hne0
  have fζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0 := isOpen_ne.mem_nhds hζ₀
  have hb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2 := by
    filter_upwards [(continuous_norm.pow m).continuousAt.eventually_lt continuousAt_const hb0]
      with ζ h using h.le
  have fHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < (m : ℝ) * θ ζ - Complex.arg p - angA m ζ
      - 2 * Real.pi * (N : ℝ) ∧ (m : ℝ) * θ ζ - Complex.arg p - angA m ζ
      - 2 * Real.pi * (N : ℝ) < 2 * Real.pi := by
    have hmem : Set.Ioo (-(2 * Real.pi)) (2 * Real.pi)
        ∈ nhds ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (N : ℝ)) := by
      rw [hH0]; exact Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    filter_upwards [hH.eventually hmem] with ζ h using ⟨h.1, h.2⟩
  have fAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
      ∧ 0 ≤ angA m ζ + ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ))
      ∧ angA m ζ + ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi := by
    have hmemA : Set.Ioo 0 Real.pi ∈ nhds (angA m ζ₀) := Ioo_mem_nhds hA0.1 hA0.2
    have hmemAH : Set.Ioo 0 Real.pi ∈ nhds (angA m ζ₀ + ((m : ℝ) * θ ζ₀ - Complex.arg p
        - angA m ζ₀ - 2 * Real.pi * (N : ℝ))) := by
      have hval : angA m ζ₀ + ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (N : ℝ))
          = angA m ζ₀ := by rw [hH0]; ring
      rw [hval]; exact Ioo_mem_nhds hA0.1 hA0.2
    filter_upwards [hA.eventually hmemA, (hA.add hH).eventually hmemAH] with ζ hfa hfah
    exact ⟨hfa.1.le, hfa.2.le, hfah.1.le, hfah.2.le⟩
  have farc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
      endChart p m ζ ∈ seamArc 3 m (c + 2 * (N : ZMod (2 * m)) - 1) := by
    have hsign0 : (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ₀) ^ 3).re < 0 := by
      have h := hmem0; simp only [seamArc, arc, Set.mem_ofPred_eq] at h; exact h.2
    have hgcont : ContinuousAt (fun ζ => (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ) ^ 3).re) ζ₀ :=
      continuousAt_const.mul (Complex.continuous_re.continuousAt.comp (hendcont.pow 3))
    filter_upwards [hgcont.eventually_lt continuousAt_const hsign0] with ζ hg hnorm
    simp only [seamArc, arc, Set.mem_ofPred_eq]
    exact ⟨hnorm, hg⟩
  exact ⟨Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) ∘ Bracket.σ,
    endFieldWith_reflected_eventuallyEq_lift p hp hsv c θ hθq fne fζ hb fHbd fAint farc,
    reflectedGerm_contDiffAt hu (c + 2 * (N : ZMod (2 * m)) - 1) hmem0 hseam0,
    reflectedGerm_flat hu hjac (c + 2 * (N : ZMod (2 * m)) - 1) hmem0 hseam0⟩

/-- **Off-cut complex PDE.**  `Δ F + endPotential·F = 0` at a nonzero `ζ` off the principal cut,
by the regularity proof's trichotomy routed through `endField_laplacian_of_germ`. -/
lemma endField_laplacian_offCut {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ) (hp : ‖p‖ = 1)
    (hpunc : p ∈ punctures 3) (hu : IsSmooth 3 m u) (hjac : IsJacobiField 3 m u) (hsv : SeamVal 3 u)
    (c : ZMod (2 * m)) {ζ : ℂ} (hcut : 0 < ζ.re ∨ ζ.im ≠ 0) (hζ : ζ ≠ 0) (hρ1 : ‖ζ‖ ^ m < 1)
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ 3).im) :
    laplacian (endFieldWith p u (endIdx m c p)) ζ
      + (endPotential p m ζ : ℂ) * endFieldWith p u (endIdx m c p) ζ = 0 := by
  have hρ2 : ‖ζ‖ ^ m < 2 := lt_trans hρ1 one_lt_two
  have hρpos : 0 < ‖ζ‖ ^ m := pow_pos (norm_pos_iff.mpr hζ) m
  have hnsOff : ‖endChart p m ζ‖ ≠ 1 →
      ∀ᶠ ζ' in nhds ζ, endIdx m c p ζ' = endIdx m c p ζ := by
    intro hne1
    have hns : ∀ k : ℤ, (angT p m ζ - angA m ζ) / (2 * Real.pi) ≠ (k : ℝ) := by
      intro k hk
      rw [div_eq_iff (by positivity)] at hk
      have hcos : Real.cos (angT p m ζ) = Real.cos (angA m ζ) := by
        rw [show angT p m ζ = angA m ζ + (k : ℝ) * (2 * Real.pi) from by linarith [hk],
          Real.cos_add_int_mul_two_pi]
      have h := endChart_normSq_sub_one_cos hp hρ2.le
      rw [hcos, sub_self, mul_zero] at h
      have hsq : ‖endChart p m ζ‖ ^ 2 = 1 := by rw [Complex.sq_norm]; linarith
      exact hne1 (by rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one])
    filter_upwards [angJ_eventuallyEq hcut hns] with ζ' h; simp only [endIdx, h]
  rcases lt_trichotomy (‖endChart p m ζ‖) 1 with hlt | heq | hgt
  · obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_direct p c (hnsOff (ne_of_lt hlt))
      (glue_contDiffAt_disk hu.1 (endIdx m c p ζ) hlt) (glue_flat_disk hjac (endIdx m c p ζ) hlt)
    exact endField_laplacian_of_germ p c H hEq hC2 hflat
  · have hcosA : Real.cos (angA m ζ) = -‖ζ‖ ^ m / 2 := by
      rw [angA]; exact Real.cos_arccos (by linarith) (by linarith)
    have hcosT : Real.cos (angT p m ζ) = Real.cos (angA m ζ) := by
      have h := endChart_normSq_sub_one_cos hp hρ2.le
      have hns1 : Complex.normSq (endChart p m ζ) = 1 := by
        rw [Complex.normSq_eq_norm_sq, heq]; norm_num
      rw [hns1] at h
      have h0 : 2 * ‖ζ‖ ^ m * (Real.cos (angT p m ζ) - Real.cos (angA m ζ)) = 0 := by linarith [h]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' (by positivity)
      · linarith [h']
    have hAmem := angA_mem hζ hρ2
    rw [Real.cos_eq_cos_iff] at hcosT
    obtain ⟨k, hk | hk⟩ := hcosT
    · have hT2 : angT p m ζ = angA m ζ + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast; linear_combination -hk
      have hH0 : angT p m ζ - angA m ζ - 2 * Real.pi * (((-k : ℤ)) : ℝ) = 0 := by rw [hT2]; ring
      have hcosTA : Real.cos (angT p m ζ) = -‖ζ‖ ^ m / 2 := by
        rw [hT2, Real.cos_add_int_mul_two_pi, hcosA]
      have hsinT : 0 < Real.sin (angT p m ζ) := by
        rw [hT2, Real.sin_add_int_mul_two_pi]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hAmem.1, Real.pi_pos]) hAmem.2
      obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_seam_offCut p hp hu hjac hsv c hζ hcut hρ2 hH0
        (arc_mem_a2 hpunc hp hζ hρ1 hcosTA hsinT heq (by rw [parity_add_two_mul]; exact hbit))
      exact endField_laplacian_of_germ p c H hEq hC2 hflat
    · have hT2 : angT p m ζ = -angA m ζ + ((k : ℤ) : ℝ) * (2 * Real.pi) := by
        linear_combination hk
      have hcosTA : Real.cos (angT p m ζ) = -‖ζ‖ ^ m / 2 := by
        rw [hT2, Real.cos_add_int_mul_two_pi, Real.cos_neg, hcosA]
      have hsinT : Real.sin (angT p m ζ) < 0 := by
        rw [hT2, Real.sin_add_int_mul_two_pi, Real.sin_neg]
        have := Real.sin_pos_of_pos_of_lt_pi (show 0 < angA m ζ by linarith [hAmem.1, Real.pi_pos])
          hAmem.2
        linarith
      have hns : ∀ j : ℤ, (angT p m ζ - angA m ζ) / (2 * Real.pi) ≠ (j : ℝ) := by
        intro j hj
        rw [div_eq_iff (by positivity)] at hj
        rw [hT2] at hj
        have hApi : angA m ζ = ((k : ℝ) - (j : ℝ)) * Real.pi := by linear_combination (-1 / 2 : ℝ) * hj
        rw [hApi] at hAmem
        have hlo : (1 : ℝ) / 2 < (k : ℝ) - (j : ℝ) := by nlinarith [hAmem.1, Real.pi_pos]
        have hhi : (k : ℝ) - (j : ℝ) < 1 := by nlinarith [hAmem.2, Real.pi_pos]
        have hlo' : (0 : ℤ) < k - j := by
          have hh : (0 : ℝ) < ((k - j : ℤ) : ℝ) := by push_cast; linarith [hlo]
          exact_mod_cast hh
        have hhi' : (k - j : ℤ) < 1 := by
          have hh : ((k - j : ℤ) : ℝ) < 1 := by push_cast; linarith [hhi]
          exact_mod_cast hh
        omega
      have hidx : ∀ᶠ ζ' in nhds ζ, endIdx m c p ζ' = endIdx m c p ζ := by
        filter_upwards [angJ_eventuallyEq hcut hns] with ζ' h; simp only [endIdx, h]
      have hpe : parity m (endIdx m c p ζ + 1) = parity m c + 1 := by
        simp only [endIdx]; rw [map_add, map_one, parity_add_two_mul]
      have hpar : (-1 : ℝ) ^ (parity m (endIdx m c p ζ + 1)).val * (p ^ 3).im < 0 := by
        rw [hpe, neg_one_pow_parity_add_one]; nlinarith [hbit]
      have harc := arc_mem_a1 hpunc hp hζ hρ1 hcosTA hsinT heq hpar
      obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_direct p c hidx
        ((hu.2.1 (endIdx m c p ζ) (endChart p m ζ) harc).of_le two_le_infty)
        (glue_flat_jacobi hu hjac (endIdx m c p ζ) harc)
      exact endField_laplacian_of_germ p c H hEq hC2 hflat
  · obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_direct p c (hnsOff (ne_of_gt hgt))
      (glue_contDiffAt_exterior hu.1 (endIdx m c p ζ) hgt) (glue_flat_exterior hu.1 hjac (endIdx m c p ζ) hgt)
    exact endField_laplacian_of_germ p c H hEq hC2 hflat

/-- **Cut complex PDE.**  `Δ F + endPotential·F = 0` at a negative-real `ζ₀`, via the lift `θ`
(same trichotomy as `pt_cut`, routed through the lift-based germ representations). -/
lemma endField_laplacian_cut {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ) (hp : ‖p‖ = 1)
    (hpunc : p ∈ punctures 3) (hu : IsSmooth 3 m u) (hjac : IsJacobiField 3 m u) (hsv : SeamVal 3 u)
    (c : ZMod (2 * m)) {ζ₀ : ℂ} (hcre : ζ₀.re < 0) (hρ1 : ‖ζ₀‖ ^ m < 1)
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ 3).im) :
    laplacian (endFieldWith p u (endIdx m c p)) ζ₀
      + (endPotential p m ζ₀ : ℂ) * endFieldWith p u (endIdx m c p) ζ₀ = 0 := by
  have hζ₀ : ζ₀ ≠ 0 := fun h => by simp [h] at hcre
  have hρ2 : ‖ζ₀‖ ^ m < 2 := lt_trans hρ1 one_lt_two
  have hρpos : 0 < ‖ζ₀‖ ^ m := pow_pos (norm_pos_iff.mpr hζ₀) m
  set θ : ℂ → ℝ := fun ζ => Complex.arg (-ζ) + Real.pi with hθdef
  have hθc : ContinuousAt θ ζ₀ := argLift_continuousAt (Or.inl hcre)
  have hθq : ∀ᶠ ζ in nhds ζ₀, ∃ q : ℤ, θ ζ = Complex.arg ζ + 2 * Real.pi * (q : ℝ) := by
    filter_upwards [isOpen_ne.mem_nhds hζ₀] with ζ hζ using argLift_arg_eq hζ
  obtain ⟨q0, hq0⟩ := hθq.self_of_nhds
  have hcs0 : Real.cos ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.cos (angT p m ζ₀) := cos_lift_eq hq0
  have hsn0 : Real.sin ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.sin (angT p m ζ₀) := sin_lift_eq hq0
  rcases lt_trichotomy (‖endChart p m ζ₀‖) 1 with hlt | heq | hgt
  · have hns : ∀ k : ℤ, ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (k : ℝ) := by
      intro k hk
      rw [div_eq_iff (by positivity)] at hk
      have hH0k : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (k : ℝ) = 0 := by
        linear_combination hk
      rw [norm_endChart_eq_one_gen hp hρ2.le hcs0 hH0k] at hlt; exact lt_irrefl 1 hlt
    obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_direct p c
      (endIdx_eventuallyEq_of_lift θ hθc hθq hns)
      (glue_contDiffAt_disk hu.1 (endIdx m c p ζ₀) hlt) (glue_flat_disk hjac (endIdx m c p ζ₀) hlt)
    exact endField_laplacian_of_germ p c H hEq hC2 hflat
  · have hcosA : Real.cos (angA m ζ₀) = -‖ζ₀‖ ^ m / 2 := by
      rw [angA]; exact Real.cos_arccos (by linarith) (by linarith)
    have hcosT : Real.cos (angT p m ζ₀) = Real.cos (angA m ζ₀) := by
      have h := endChart_normSq_sub_one_cos hp hρ2.le
      have hns1 : Complex.normSq (endChart p m ζ₀) = 1 := by
        rw [Complex.normSq_eq_norm_sq, heq]; norm_num
      rw [hns1] at h
      have h0 : 2 * ‖ζ₀‖ ^ m * (Real.cos (angT p m ζ₀) - Real.cos (angA m ζ₀)) = 0 := by linarith [h]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' (by positivity)
      · linarith [h']
    have hAmem := angA_mem hζ₀ hρ2
    have hcosTA : Real.cos (angT p m ζ₀) = -‖ζ₀‖ ^ m / 2 := by rw [hcosT, hcosA]
    have hcosS : Real.cos ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.cos (angA m ζ₀) := by rw [hcs0, hcosT]
    rw [Real.cos_eq_cos_iff] at hcosS
    obtain ⟨k, hk | hk⟩ := hcosS
    · have hH0 : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (((-k : ℤ)) : ℝ) = 0 := by
        push_cast; linear_combination -hk
      have hsinT : 0 < Real.sin (angT p m ζ₀) := by
        rw [← hsn0, show (m : ℝ) * θ ζ₀ - Complex.arg p
            = angA m ζ₀ + ((-k : ℤ) : ℝ) * (2 * Real.pi) from by push_cast; linear_combination -hk,
          Real.sin_add_int_mul_two_pi]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hAmem.1, Real.pi_pos]) hAmem.2
      have hmem0 : endChart p m ζ₀ ∈ seamArc 3 m (c + 2 * (((-k : ℤ)) : ZMod (2 * m)) - 1) :=
        arc_mem_a2 hpunc hp hζ₀ hρ1 hcosTA hsinT heq (by rw [parity_add_two_mul]; exact hbit)
      obtain ⟨H, hEq, hC2, hflat⟩ :=
        endField_germ_rep_seam_lift p hp hu hjac hsv c θ hθc hθq hζ₀ hρ2 hH0 hmem0
      exact endField_laplacian_of_germ p c H hEq hC2 hflat
    · have hsS : (m : ℝ) * θ ζ₀ - Complex.arg p = -angA m ζ₀ + ((k : ℤ) : ℝ) * (2 * Real.pi) := by
        linear_combination hk
      have hsinT : Real.sin (angT p m ζ₀) < 0 := by
        rw [← hsn0, hsS, Real.sin_add_int_mul_two_pi, Real.sin_neg]
        have := Real.sin_pos_of_pos_of_lt_pi (show 0 < angA m ζ₀ by linarith [hAmem.1, Real.pi_pos])
          hAmem.2
        linarith
      have hns : ∀ j : ℤ, ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (j : ℝ) := by
        intro j hj
        rw [div_eq_iff (by positivity)] at hj
        rw [hsS] at hj
        have hApi : angA m ζ₀ = ((k : ℝ) - (j : ℝ)) * Real.pi := by linear_combination (-1 / 2 : ℝ) * hj
        rw [hApi] at hAmem
        have hlo : (1 : ℝ) / 2 < (k : ℝ) - (j : ℝ) := by nlinarith [hAmem.1, Real.pi_pos]
        have hhi : (k : ℝ) - (j : ℝ) < 1 := by nlinarith [hAmem.2, Real.pi_pos]
        have hlo' : (0 : ℤ) < k - j := by
          have hh : (0 : ℝ) < ((k - j : ℤ) : ℝ) := by push_cast; linarith [hlo]
          exact_mod_cast hh
        have hhi' : (k - j : ℤ) < 1 := by
          have hh : ((k - j : ℤ) : ℝ) < 1 := by push_cast; linarith [hhi]
          exact_mod_cast hh
        omega
      have hpe : parity m (endIdx m c p ζ₀ + 1) = parity m c + 1 := by
        simp only [endIdx]; rw [map_add, map_one, parity_add_two_mul]
      have hpar : (-1 : ℝ) ^ (parity m (endIdx m c p ζ₀ + 1)).val * (p ^ 3).im < 0 := by
        rw [hpe, neg_one_pow_parity_add_one]; nlinarith [hbit]
      have harc := arc_mem_a1 hpunc hp hζ₀ hρ1 hcosTA hsinT heq hpar
      obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_direct p c
        (endIdx_eventuallyEq_of_lift θ hθc hθq hns)
        ((hu.2.1 (endIdx m c p ζ₀) (endChart p m ζ₀) harc).of_le two_le_infty)
        (glue_flat_jacobi hu hjac (endIdx m c p ζ₀) harc)
      exact endField_laplacian_of_germ p c H hEq hC2 hflat
  · have hns : ∀ k : ℤ, ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (k : ℝ) := by
      intro k hk
      rw [div_eq_iff (by positivity)] at hk
      have hH0k : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (k : ℝ) = 0 := by
        linear_combination hk
      rw [norm_endChart_eq_one_gen hp hρ2.le hcs0 hH0k] at hgt; exact lt_irrefl 1 hgt
    obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_direct p c
      (endIdx_eventuallyEq_of_lift θ hθc hθq hns)
      (glue_contDiffAt_exterior hu.1 (endIdx m c p ζ₀) hgt)
      (glue_flat_exterior hu.1 hjac (endIdx m c p ζ₀) hgt)
    exact endField_laplacian_of_germ p c H hEq hC2 hflat

/-- **The complex PDE on the punctured ball.**  `Δ F + endPotential·F = 0` at every nonzero `ζ`
with `‖ζ‖^m < 1` (off-cut ∪ cut). -/
theorem endField_laplacian_punctured {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ) (hp : ‖p‖ = 1)
    (hpunc : p ∈ punctures 3) (hu : IsSmooth 3 m u) (hjac : IsJacobiField 3 m u) (hsv : SeamVal 3 u)
    (c : ZMod (2 * m)) (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ 3).im) :
    ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ ^ m < 1 → laplacian (endFieldWith p u (endIdx m c p)) ζ
      + (endPotential p m ζ : ℂ) * endFieldWith p u (endIdx m c p) ζ = 0 := by
  intro ζ hζ hρ1
  by_cases hcut : 0 < ζ.re ∨ ζ.im ≠ 0
  · exact endField_laplacian_offCut p hp hpunc hu hjac hsv c hcut hζ hρ1 hbit
  · rw [not_or, not_lt, not_ne_iff] at hcut
    have hcre : ζ.re < 0 := lt_of_le_of_ne hcut.1
      (fun h => hζ (Complex.ext (by rw [Complex.zero_re]; exact h)
        (by rw [Complex.zero_im]; exact hcut.2)))
    exact endField_laplacian_cut p hp hpunc hu hjac hsv c hcre hρ1 hbit

/-- Neighborhood `C²` of the end field, for passage to the `lapReal` equation. -/
lemma endField_eventually_contDiffAt {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ) (hp : ‖p‖ = 1)
    (hpunc : p ∈ punctures 3) (hu : IsSmooth 3 m u) (hsv : SeamVal 3 u) (c : ZMod (2 * m))
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ 3).im) {ζ : ℂ} (hζ : ζ ≠ 0) (hρ1 : ‖ζ‖ ^ m < 1) :
    ∀ᶠ y in nhds ζ, ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) y := by
  have hρball : ∀ᶠ y in nhds ζ, ‖y‖ ^ m < 1 := by
    filter_upwards [(continuous_norm.pow m).continuousAt.eventually_lt continuousAt_const hρ1]
      with y h using h
  filter_upwards [isOpen_ne.mem_nhds hζ, hρball] with y hy hyρ
  exact endField_contDiffAt_punctured p hp hpunc hu hsv c hbit y hy hyρ

/-- The real part solves the `lapReal` equation for nonzero `ζ` with `‖ζ‖^m < 1`. -/
theorem endField_hre {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ) (hp : ‖p‖ = 1)
    (hpunc : p ∈ punctures 3) (hu : IsSmooth 3 m u) (hjac : IsJacobiField 3 m u) (hsv : SeamVal 3 u)
    (c : ZMod (2 * m)) (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ 3).im) :
    ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ ^ m < 1 →
      lapReal (fun z => (endFieldWith p u (endIdx m c p) z).re) ζ
        + endPotential p m ζ * (endFieldWith p u (endIdx m c p) ζ).re = 0 := by
  intro ζ hζ hρ1
  rw [lapReal_re (endField_eventually_contDiffAt p hp hpunc hu hsv c hbit hζ hρ1)]
  have hlap : laplacian (endFieldWith p u (endIdx m c p)) ζ
      = -(endPotential p m ζ : ℂ) * endFieldWith p u (endIdx m c p) ζ := by
    linear_combination endField_laplacian_punctured p hp hpunc hu hjac hsv c hbit ζ hζ hρ1
  rw [hlap]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The imaginary part solves the `lapReal` equation for nonzero `ζ` with `‖ζ‖^m < 1`. -/
theorem endField_him {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ) (hp : ‖p‖ = 1)
    (hpunc : p ∈ punctures 3) (hu : IsSmooth 3 m u) (hjac : IsJacobiField 3 m u) (hsv : SeamVal 3 u)
    (c : ZMod (2 * m)) (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ 3).im) :
    ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ ^ m < 1 →
      lapReal (fun z => (endFieldWith p u (endIdx m c p) z).im) ζ
        + endPotential p m ζ * (endFieldWith p u (endIdx m c p) ζ).im = 0 := by
  intro ζ hζ hρ1
  rw [lapReal_im (endField_eventually_contDiffAt p hp hpunc hu hsv c hbit hζ hρ1)]
  have hlap : laplacian (endFieldWith p u (endIdx m c p)) ζ
      = -(endPotential p m ζ : ℂ) * endFieldWith p u (endIdx m c p) ζ := by
    linear_combination endField_laplacian_punctured p hp hpunc hu hjac hsv c hbit ζ hζ hρ1
  rw [hlap]
  simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ### Evaluation identities for coverage

For the shrinking all-copy coverage: a `ζ` whose chart image is `w` (interior) reads copy `endIdx ζ`
directly; a `ζ` whose chart image is `σ w` (exterior) reads copy `endIdx ζ + 1` after reflection. -/

/-- **Direct evaluation.**  If `endChart ζ = w` with `‖w‖ ≤ 1`, then `endField ζ = u (endIdx ζ) w`. -/
lemma endField_direct_eval {m : ℕ} (p : ℂ) (u : ZMod (2 * m) → ℂ → ℂ) (c : ZMod (2 * m)) {ζ w : ℂ}
    (hw : endChart p m ζ = w) (h1 : ‖w‖ ≤ 1) :
    endFieldWith p u (endIdx m c p) ζ = u (endIdx m c p ζ) w := by
  rw [endFieldWith_inside p u (endIdx m c p) (by rw [hw]; exact h1), hw]

/-- **Reflected evaluation.**  If `endChart ζ = σ w` with `0 < ‖w‖ < 1`, then
`endField ζ = u (endIdx ζ + 1) w`. -/
lemma endField_reflected_eval {m : ℕ} (p : ℂ) (u : ZMod (2 * m) → ℂ → ℂ) (c : ZMod (2 * m))
    {ζ w : ℂ} (hw : endChart p m ζ = Bracket.σ w) (hw0 : w ≠ 0) (hlt : ‖w‖ < 1) :
    endFieldWith p u (endIdx m c p) ζ = u (endIdx m c p ζ + 1) w := by
  have hgt : 1 < ‖endChart p m ζ‖ := by
    rw [hw, Bracket.norm_σ]; exact (one_lt_inv₀ (norm_pos_iff.mpr hw0)).mpr hlt
  rw [endFieldWith_outside p u (endIdx m c p) hgt, hw, Bracket.σ_σ]

/-- **m-th root existence with norm control.**  For `z ≠ 0` and `m > 0` there is a nonzero
`ζ` with `ζ^m = z` and `‖ζ‖^m = ‖z‖` (ℂ algebraically closed; the norm relation is free from
`norm_pow`).  So `‖z‖` small forces `‖ζ‖` small. -/
lemma exists_mpow_root {m : ℕ} (hm : 0 < m) {z : ℂ} (hz : z ≠ 0) :
    ∃ ζ : ℂ, ζ ^ m = z ∧ ‖ζ‖ ^ m = ‖z‖ ∧ ζ ≠ 0 := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq z hm
  refine ⟨ζ, hζ, by rw [← norm_pow, hζ], fun h => hz ?_⟩
  rw [h, zero_pow hm.ne'] at hζ; exact hζ.symm

/-- The angle `θ` is a `2π`-lift of `arg (exp(θ·i))` (`toIocMod` differs by an integer multiple). -/
lemma arg_exp_lift (θ : ℝ) :
    ∃ q : ℤ, θ = Complex.arg (Complex.exp ((θ : ℂ) * Complex.I)) + 2 * Real.pi * (q : ℝ) := by
  refine ⟨toIocDiv Real.two_pi_pos (-Real.pi) θ, ?_⟩
  rw [Complex.arg_exp_mul_I]
  have h := self_sub_toIocMod Real.two_pi_pos (-Real.pi) θ
  rw [zsmul_eq_mul] at h
  linear_combination h

/-- **Root with prescribed copy index.**  For `z ≠ 0` and target residue index `J`, there is a
nonzero `ζ` with `ζ^m = z`, `‖ζ‖^m = ‖z‖`, and `endIdx ζ = c + 2J` exactly.  The angle `θ` is tuned
so the floor lands on `J`; the construction hits the residue directly (no rotation orbit needed). -/
lemma exists_root_endIdx {m : ℕ} (hm : 0 < m) (c : ZMod (2 * m)) (p : ℂ) {z : ℂ} (hz : z ≠ 0)
    (J : ℤ) :
    ∃ ζ : ℂ, ζ ^ m = z ∧ ‖ζ‖ ^ m = ‖z‖ ∧ endIdx m c p ζ = c + 2 * (J : ZMod (2 * m)) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  set s : ℝ := ‖z‖ ^ ((1 : ℝ) / m) with hs
  have hspos : 0 < s := Real.rpow_pos_of_pos hzpos _
  have hsm_pow : s ^ m = ‖z‖ := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hzpos.le, one_div,
      inv_mul_cancel₀ hmR, Real.rpow_one]
  set A : ℝ := Real.arccos (-‖z‖ / 2) with hA
  set base : ℝ := (Complex.arg z - Complex.arg p - A) / (2 * Real.pi) with hbase
  set θ : ℝ := (Complex.arg z + 2 * Real.pi * ((J - ⌊base⌋ : ℤ) : ℝ)) / m with hθ
  have hmθR : (m : ℝ) * θ = Complex.arg z + 2 * Real.pi * ((J - ⌊base⌋ : ℤ) : ℝ) := by
    rw [hθ]; field_simp
  refine ⟨(↑s : ℂ) * Complex.exp ((↑θ : ℂ) * Complex.I), ?_, ?_, ?_⟩
  · -- ζ ^ m = z
    rw [mul_pow, ← Complex.ofReal_pow, hsm_pow, ← Complex.exp_nat_mul,
      show (↑m : ℂ) * ((↑θ : ℂ) * Complex.I) = (↑((m : ℝ) * θ) : ℂ) * Complex.I from by
        push_cast; ring, hmθR,
      show (↑(Complex.arg z + 2 * Real.pi * ((J - ⌊base⌋ : ℤ) : ℝ)) : ℂ) * Complex.I
          = (↑(Complex.arg z) : ℂ) * Complex.I
            + (↑((J - ⌊base⌋ : ℤ)) : ℂ) * (2 * ↑Real.pi * Complex.I) from by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    exact Complex.norm_mul_exp_arg_mul_I z
  · -- ‖ζ‖ ^ m = ‖z‖
    rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_of_nonneg hspos.le, hsm_pow]
  · -- endIdx = c + 2 J
    set ζ : ℂ := (↑s : ℂ) * Complex.exp ((↑θ : ℂ) * Complex.I) with hζ
    have hnζ : ‖ζ‖ = s := by
      rw [hζ, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
        Real.norm_of_nonneg hspos.le]
    have hargζ : Complex.arg ζ = Complex.arg (Complex.exp ((↑θ : ℂ) * Complex.I)) := by
      rw [hζ, Complex.arg_real_mul _ hspos]
    obtain ⟨q, hq'⟩ := arg_exp_lift θ
    have hq : θ = Complex.arg ζ + 2 * Real.pi * (q : ℝ) := by rw [hargζ]; exact hq'
    have hAζ : angA m ζ = A := by
      rw [angA, hA]; congr 1; rw [hnζ, hsm_pow]
    rw [← endIdx_arg_invariant c p ζ q]
    have hfloor : ⌊((m : ℝ) * (Complex.arg ζ + 2 * Real.pi * (q : ℝ)) - Complex.arg p
        - angA m ζ) / (2 * Real.pi)⌋ = J := by
      rw [hAζ, show (m : ℝ) * (Complex.arg ζ + 2 * Real.pi * (q : ℝ))
          = Complex.arg z + 2 * Real.pi * ((J - ⌊base⌋ : ℤ) : ℝ) from by
        rw [← hq]; exact hmθR,
        show (Complex.arg z + 2 * Real.pi * ((J - ⌊base⌋ : ℤ) : ℝ) - Complex.arg p - A)
            / (2 * Real.pi) = base + ((J - ⌊base⌋ : ℤ) : ℝ) from by rw [hbase]; field_simp; ring,
        Int.floor_add_intCast]
      omega
    rw [hfloor]

/-- Every `ZMod (2m)` element is `2J` or `2J + 1` for some integer `J` (parity split). -/
lemma exists_two_mul_or {m : ℕ} (y : ZMod (2 * m)) :
    ∃ J : ℤ, y = 2 * (J : ZMod (2 * m)) ∨ y = 2 * (J : ZMod (2 * m)) + 1 := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨k / 2, ?_⟩
  rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · left; rw [show k / 2 = j from by omega, hj]; push_cast; ring
  · right; rw [show k / 2 = j from by omega, hj]; push_cast; ring

/-- **Reflected displacement identity.**  `‖σ w − p‖ = ‖w − p‖ / ‖w‖` for
`‖p‖ = 1`, `w ≠ 0`.  Since `1/w̄ → p` as `w → p`, the reflected preimage `ζ^m = σ w − p` is small
when `w` is near `p`. -/
lemma norm_sigma_sub {p w : ℂ} (hp : ‖p‖ = 1) (hw0 : w ≠ 0) :
    ‖Bracket.σ w - p‖ = ‖w - p‖ / ‖w‖ := by
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hwc : (starRingEnd ℂ) w ≠ 0 := by simpa using hw0
  rw [eq_div_iff hwn, ← RCLike.norm_conj w, ← norm_mul,
    show (Bracket.σ w - p) * (starRingEnd ℂ) w = 1 - p * (starRingEnd ℂ) w from by
      rw [Bracket.σ_apply]; field_simp]
  have hp1 : Complex.normSq p = 1 := by rw [Complex.normSq_eq_norm_sq, hp]; norm_num
  have hp2 : p.re * p.re + p.im * p.im = 1 := by rw [← Complex.normSq_apply]; exact hp1
  have hsq : Complex.normSq (1 - p * (starRingEnd ℂ) w) = Complex.normSq (w - p) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
    linear_combination (w.re * w.re + w.im * w.im - 1) * hp2
  have h2 : ‖1 - p * (starRingEnd ℂ) w‖ ^ 2 = ‖w - p‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hsq]
  rw [← Real.sqrt_sq (norm_nonneg (1 - p * (starRingEnd ℂ) w)), h2,
    Real.sqrt_sq (norm_nonneg (w - p))]

/-- On the unit circle, `Re(w³) = 0` forces `w` to be a puncture (`w⁶ = −1`). -/
lemma mem_punctures_of_reCube_zero {w : ℂ} (hw : ‖w‖ = 1) (hre0 : (w ^ 3).re = 0) :
    w ∈ punctures 3 := by
  have hz : Complex.normSq (w ^ 3) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, hw]; norm_num
  have him : (w ^ 3).im * (w ^ 3).im = 1 := by
    rw [Complex.normSq_apply, hre0] at hz; linarith
  have hsq2 : (w ^ 3) ^ 2 = -1 := by
    rw [sq]; apply Complex.ext
    · simp only [Complex.mul_re, Complex.neg_re, Complex.one_re, hre0]; linarith
    · simp only [Complex.mul_im, Complex.neg_im, Complex.one_im, hre0]; ring
  show w ^ (2 * 3) = -1
  rw [show (2 * 3 : ℕ) = 3 * 2 from rfl, pow_mul, hsq2]

/-- **Coverage of every copy near the puncture.** For every copy `n` and point `w ≠ p` in the closed disk near
`p`, there is a small `ζ` with `endFieldWith p u (endIdx m c p) ζ = u n w`: direct preimage for one
parity, reflected for the other (interior), and on the circle `SeamVal` (non-puncture) or
`PunctureZero` (puncture) closes the opposite parity. -/
lemma endField_coverage {m : ℕ} (hm : 0 < m) {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ) (hp : ‖p‖ = 1)
    (hu : u ∈ EnergySmooth 3 m) (c : ZMod (2 * m)) :
    ∀ r : ℝ, 0 < r → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ZMod (2 * m)) (w : ℂ),
      ‖w - p‖ < δ → ‖w‖ ≤ 1 → w ≠ p →
        ∃ ζ : ℂ, 0 < ‖ζ‖ ∧ ‖ζ‖ < r ∧ endFieldWith p u (endIdx m c p) ζ = u n w := by
  have hsv : SeamVal 3 u := hu.2.2.2.2
  have hpz : PunctureZero 3 u := hu.2.2.2.1
  intro r hr
  have hrm : 0 < r ^ m := pow_pos hr m
  refine ⟨min (r ^ m / 2) (1 / 2), lt_min (by positivity) (by norm_num), ?_⟩
  intro n w hwδ hw1 hwp
  have hδ1 : min (r ^ m / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hδr : min (r ^ m / 2) (1 / 2) ≤ r ^ m / 2 := min_le_left _ _
  have hwhalf : 1 / 2 < ‖w‖ := by
    have h1 := norm_sub_norm_le p w; rw [norm_sub_rev] at h1; nlinarith [h1, hwδ, hδ1, hp]
  have hw0 : w ≠ 0 := by rw [← norm_pos_iff]; linarith [hwhalf]
  have hwpz : w - p ≠ 0 := sub_ne_zero.mpr hwp
  -- the chart-radius bound ‖ζ‖ < r from ‖ζ‖^m = ‖w-p‖
  have hζrad : ∀ ζ : ℂ, ‖ζ‖ ^ m = ‖w - p‖ → ‖ζ‖ < r := fun ζ hζ => by
    apply lt_of_pow_lt_pow_left₀ m hr.le; rw [hζ]; nlinarith [hwδ, hδr, hrm]
  have hζpos : ∀ ζ : ℂ, ζ ^ m = w - p → 0 < ‖ζ‖ := fun ζ hζ => by
    rw [norm_pos_iff]; intro h; rw [h, zero_pow hm.ne'] at hζ; exact hwpz hζ.symm
  obtain ⟨J, hJ | hJ⟩ := exists_two_mul_or (n - c)
  · -- direct leg: n = c + 2J
    have hnc : n = c + 2 * (J : ZMod (2 * m)) := by linear_combination hJ
    obtain ⟨ζ, hζm, hζnorm, hζidx⟩ := exists_root_endIdx hm c p hwpz J
    have hew : endChart p m ζ = w := by rw [endChart, hζm]; ring
    exact ⟨ζ, hζpos ζ hζm, hζrad ζ hζnorm, by rw [endField_direct_eval p u c hew hw1, hζidx, ← hnc]⟩
  · -- parity c+1: n = c + 2J + 1
    have hnc : n = c + 2 * (J : ZMod (2 * m)) + 1 := by linear_combination hJ
    rcases lt_or_eq_of_le hw1 with hwlt | hweq
    · -- interior reflected
      have hσpz : Bracket.σ w - p ≠ 0 := by
        intro hh
        exact hwp (by rw [← Bracket.σ_σ w, sub_eq_zero.mp hh, Bracket.σ_self hp])
      obtain ⟨ζ, hζm, hζnorm, hζidx⟩ := exists_root_endIdx hm c p hσpz J
      have hew : endChart p m ζ = Bracket.σ w := by rw [endChart, hζm]; ring
      have hζn' : ‖ζ‖ ^ m = ‖w - p‖ / ‖w‖ := by rw [hζnorm, norm_sigma_sub hp hw0]
      have hwpos : (0 : ℝ) < ‖w‖ := by linarith [hwhalf]
      refine ⟨ζ, ?_, ?_, ?_⟩
      · rw [norm_pos_iff]; rintro rfl; rw [zero_pow hm.ne'] at hζm; exact hσpz hζm.symm
      · apply lt_of_pow_lt_pow_left₀ m hr.le
        rw [hζn', div_lt_iff₀ hwpos]; nlinarith [hwδ, hδr, hwhalf, hrm]
      · rw [endField_reflected_eval p u c hew hw0 hwlt, hζidx,
          show c + 2 * (J : ZMod (2 * m)) + 1 = n from hnc.symm]
    · -- circle boundary
      have hwnorm : ‖w‖ = 1 := hweq
      by_cases hre0 : (w ^ 3).re = 0
      · -- w is a puncture: PunctureZero
        have hwpunc : w ∈ punctures 3 := mem_punctures_of_reCube_zero hwnorm hre0
        obtain ⟨ζ, hζm, hζnorm, _⟩ := exists_mpow_root hm hwpz
        have hew : endChart p m ζ = w := by rw [endChart, hζm]; ring
        exact ⟨ζ, hζpos ζ hζm, hζrad ζ hζnorm,
          by rw [endField_direct_eval p u c hew hw1, hpz _ w hwpunc, hpz n w hwpunc]⟩
      · -- non-puncture: SeamVal on the incident arc
        have hsign : (-1 : ℝ) ^ (parity m n).val * (w ^ 3).re ≠ 0 :=
          mul_ne_zero (pow_ne_zero _ (by norm_num)) hre0
        rcases lt_or_gt_of_ne hsign with hlt | hgt
        · -- w ∈ seamArc (n-1); root endIdx = n-1
          have hmem : w ∈ seamArc 3 m (n - 1) := by
            simp only [seamArc, arc, Set.mem_ofPred_eq]
            exact ⟨hwnorm, by rw [show (n - 1) + 1 = n from by ring]; exact hlt⟩
          obtain ⟨ζ, hζm, hζnorm, hζidx⟩ := exists_root_endIdx hm c p hwpz J
          have hew : endChart p m ζ = w := by rw [endChart, hζm]; ring
          refine ⟨ζ, hζpos ζ hζm, hζrad ζ hζnorm, ?_⟩
          rw [endField_direct_eval p u c hew hw1, hζidx,
            show c + 2 * (J : ZMod (2 * m)) = n - 1 from by rw [hnc]; ring]
          have hsvn := hsv (n - 1) w hmem
          rw [show (n - 1) + 1 = n from by ring] at hsvn
          exact hsvn.symm
        · -- w ∈ seamArc n; root endIdx = n+1
          have hmem : w ∈ seamArc 3 m n := by
            simp only [seamArc, arc, Set.mem_ofPred_eq]
            refine ⟨hwnorm, ?_⟩
            rw [show parity m (n + 1) = parity m n + 1 from by rw [map_add, map_one],
              neg_one_pow_parity_add_one]
            nlinarith [hgt]
          obtain ⟨ζ, hζm, hζnorm, hζidx⟩ := exists_root_endIdx hm c p hwpz (J + 1)
          have hew : endChart p m ζ = w := by rw [endChart, hζm]; ring
          refine ⟨ζ, hζpos ζ hζm, hζrad ζ hζnorm, ?_⟩
          rw [endField_direct_eval p u c hew hw1, hζidx,
            show c + 2 * ((J + 1 : ℤ) : ZMod (2 * m)) = n + 1 from by rw [hnc]; push_cast; ring]
          exact hsv n w hmem

/-- **The `c`-parity pin exists.**  Since `Im(p³) = ±1 ≠ 0` at a puncture, some `c` satisfies the
condition `0 < (−1)^(parity c)·Im(p³)` used in the regularity and PDE results. -/
lemma exists_parity_pin {m : ℕ} {p : ℂ} (hpunc : p ∈ punctures 3) :
    ∃ c : ZMod (2 * m), 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ 3).im := by
  rcases lt_or_gt_of_ne (cube_im_ne hpunc) with hlt | hgt
  · refine ⟨1, ?_⟩
    rw [show (parity m (1 : ZMod (2 * m))).val = 1 from by rw [map_one]; rfl, pow_one]
    linarith [hlt]
  · refine ⟨0, ?_⟩
    rw [show (parity m (0 : ZMod (2 * m))).val = 0 from by rw [map_zero]; rfl, pow_zero]
    linarith [hgt]

/-- `‖p‖ = 1` at a puncture of `Ξ₃` (`p⁶ = −1`). -/
lemma norm_eq_one_of_mem_punctures {p : ℂ} (hp : p ∈ punctures 3) : ‖p‖ = 1 := by
  have h6 : ‖p‖ ^ 6 = 1 := by
    have hh : p ^ (2 * 3) = -1 := hp
    calc ‖p‖ ^ 6 = ‖p ^ 6‖ := (norm_pow p 6).symm
      _ = ‖p ^ (2 * 3)‖ := by norm_num
      _ = ‖(-1 : ℂ)‖ := by rw [hh]
      _ = 1 := by simp
  calc ‖p‖ = (‖p‖ ^ (6 : ℕ)) ^ ((1 : ℝ) / 6) := by
        rw [← Real.rpow_natCast ‖p‖ 6, ← Real.rpow_mul (norm_nonneg p)]; norm_num
    _ = (1 : ℝ) ^ ((1 : ℝ) / 6) := by rw [h6]
    _ = 1 := Real.one_rpow _

end KsIndex.EndField
