module

/-
KsIndexLean — Periodic arc field and cosine collar cutoff.

`hAmp θ = sqrt (max (cos θ) 0)` is the nonnegative amplitude, bounded by `1`.
The representative `per θ` lies in `(-π,π]`, and
`vF θ = hAmp θ * exp (-i * per θ / 2)` is continuous and `2π`-periodic.
At the representative's discontinuities the amplitude vanishes on a
neighborhood, so the field remains continuous. Its norm is exactly `hAmp`.

The collar factor `wCol η θ = smoothTransition ((cos θ - η)/η)` takes values
in `[0,1]`, is even and periodic, and has the exported `C²` regularity for
every real `η`. For `η > 0`, it is zero where `cos θ ≤ η` and one where
`2η ≤ cos θ`.

The cut field `psiF η = vF * wCol η` and junction part
`fJ η = vF * (1-wCol η)` are continuous and periodic and sum to `vF`.
For positive `η`, the cut field vanishes where `cos θ ≤ η`; the junction
part can be nonzero only where `0 < cos θ < 2η`. The pointwise envelope
`‖fJ η θ‖ ≤ hAmp θ` holds for every real `η`. Fourier identification,
weighted-energy estimates, and negativity of a suitably chosen cut field
are established separately.
-/
public import Mathlib

@[expose] public section


noncomputable section

open Real Set Filter Topology

namespace KsIndex.ArcField

/-! ### The amplitude -/

/-- The arc amplitude `√((cos θ)⁺)`. -/
def hAmp (θ : ℝ) : ℝ := Real.sqrt (max (Real.cos θ) 0)

lemma hAmp_nonneg (θ : ℝ) : 0 ≤ hAmp θ := Real.sqrt_nonneg _

lemma hAmp_le_one (θ : ℝ) : hAmp θ ≤ 1 := by
  have h : max (Real.cos θ) 0 ≤ 1 := max_le (Real.cos_le_one θ) zero_le_one
  exact (Real.sqrt_le_sqrt h).trans_eq Real.sqrt_one

lemma hAmp_eq_zero_of_nonpos {θ : ℝ} (h : Real.cos θ ≤ 0) : hAmp θ = 0 := by
  simp only [hAmp, max_eq_right h, Real.sqrt_zero]

lemma hAmp_eq_sqrt {θ : ℝ} (h : 0 ≤ Real.cos θ) : hAmp θ = Real.sqrt (Real.cos θ) := by
  simp only [hAmp, max_eq_left h]

lemma hAmp_sq {θ : ℝ} (h : 0 ≤ Real.cos θ) : hAmp θ ^ 2 = Real.cos θ := by
  rw [hAmp_eq_sqrt h]
  exact Real.sq_sqrt h

lemma continuous_hAmp : Continuous hAmp :=
  Real.continuous_sqrt.comp (Real.continuous_cos.max continuous_const)

lemma hAmp_periodic : Function.Periodic hAmp (2 * π) := by
  intro θ
  simp only [hAmp, Real.cos_add_two_pi]

lemma hAmp_even (θ : ℝ) : hAmp (-θ) = hAmp θ := by
  simp only [hAmp, Real.cos_neg]

/-! ### The principal representative and the periodized field -/

/-- The principal representative of `θ` in `(−π, π]`. -/
def per (θ : ℝ) : ℝ := toIocMod Real.two_pi_pos (-π) θ

lemma per_periodic : Function.Periodic per (2 * π) := fun θ =>
  toIocMod_add_right Real.two_pi_pos (-π) θ

lemma per_mem (θ : ℝ) : per θ ∈ Set.Ioc (-π) π := by
  have h := toIocMod_mem_Ioc Real.two_pi_pos (-π) θ
  rwa [show -π + 2 * π = π by ring] at h

lemma per_eq_self {θ : ℝ} (h : θ ∈ Set.Ioc (-π) π) : per θ = θ := by
  rw [show per θ = toIocMod Real.two_pi_pos (-π) θ from rfl, toIocMod_eq_self]
  rwa [show -π + 2 * π = π by ring]

/-- The periodized half-angle test field `vF = √cos⁺ · e^{−i·per/2}`. -/
def vF (θ : ℝ) : ℂ := (hAmp θ : ℂ) * Complex.exp (-Complex.I * ((per θ : ℝ) : ℂ) / 2)

lemma vF_periodic : Function.Periodic vF (2 * π) := by
  intro θ
  simp only [vF, hAmp_periodic θ, per_periodic θ]

lemma vF_eq_zero_of_nonpos {θ : ℝ} (h : Real.cos θ ≤ 0) : vF θ = 0 := by
  simp only [vF, hAmp_eq_zero_of_nonpos h, Complex.ofReal_zero, zero_mul]

/-- On the principal window the phase is the half-angle. -/
lemma vF_eq_of_mem {θ : ℝ} (h : θ ∈ Set.Ioc (-π) π) :
    vF θ = (hAmp θ : ℂ) * Complex.exp (-Complex.I * (θ : ℂ) / 2) := by
  simp only [vF, per_eq_self h]

lemma norm_vF (θ : ℝ) : ‖vF θ‖ = hAmp θ := by
  have harg : -Complex.I * ((per θ : ℝ) : ℂ) / 2 = ((-(per θ) / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  simp only [vF]
  rw [norm_mul, harg, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (hAmp_nonneg θ)]

/-- `vF` is continuous: away from the seam `θ ≡ −π (mod 2π)` because `per` is, and at the
seam because `cos = −1 < 0` there makes `vF` vanish on a neighborhood. -/
lemma continuous_vF : Continuous vF := by
  rw [continuous_iff_continuousAt]
  intro θ
  by_cases hmod : θ ≡ -π [PMOD (2 * π)]
  · -- the seam: `cos θ = −1`, `vF ≡ 0` near `θ`
    obtain ⟨z, hz⟩ := AddCommGroup.modEq_iff_zsmul'.mp hmod
    rw [zsmul_eq_mul] at hz
    have hθ : θ = -π + ((-z : ℤ) : ℝ) * (2 * π) := by
      push_cast
      linarith
    have hcos : Real.cos θ = -1 := by
      rw [hθ, Real.cos_add_int_mul_two_pi, Real.cos_neg, Real.cos_pi]
    have hnb : {t : ℝ | Real.cos t < 0} ∈ nhds θ :=
      (isOpen_lt Real.continuous_cos continuous_const).mem_nhds
        (by simp only [Set.mem_ofPred_eq, hcos]; norm_num)
    have hev : (fun _ : ℝ => (0 : ℂ)) =ᶠ[nhds θ] vF := by
      filter_upwards [hnb] with t ht
      exact (vF_eq_zero_of_nonpos (le_of_lt ht)).symm
    exact continuousAt_const.congr hev
  · -- off the seam: `per` is continuous at `θ`
    have hper : ContinuousAt per θ := continuousAt_toIocMod Real.two_pi_pos (-π) hmod
    have hpc : ContinuousAt (fun t : ℝ => ((per t : ℝ) : ℂ)) θ :=
      Complex.continuous_ofReal.continuousAt.comp hper
    have hin : ContinuousAt (fun t : ℝ => -Complex.I * ((per t : ℝ) : ℂ) / 2) θ :=
      (continuousAt_const.mul hpc).div_const 2
    have hexp : ContinuousAt
        (fun t : ℝ => Complex.exp (-Complex.I * ((per t : ℝ) : ℂ) / 2)) θ :=
      Complex.continuous_exp.continuousAt.comp hin
    have hamp : ContinuousAt (fun t : ℝ => ((hAmp t : ℝ) : ℂ)) θ :=
      Complex.continuous_ofReal.continuousAt.comp continuous_hAmp.continuousAt
    exact hamp.mul hexp

/-! ### The cos-collar cut -/

/-- The collar factor: `smoothTransition((cos θ − η)/η)` — `0` where `cos ≤ η`, `1` where
`cos ≥ 2η`, for `η > 0`. -/
def wCol (η θ : ℝ) : ℝ := Real.smoothTransition ((Real.cos θ - η) / η)

lemma wCol_mem (η θ : ℝ) : wCol η θ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma wCol_eq_zero {η θ : ℝ} (hη : 0 < η) (h : Real.cos θ ≤ η) : wCol η θ = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  rw [div_le_iff₀ hη]
  linarith

lemma wCol_eq_one {η θ : ℝ} (hη : 0 < η) (h : 2 * η ≤ Real.cos θ) : wCol η θ = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ hη]
  linarith

lemma wCol_periodic (η : ℝ) : Function.Periodic (wCol η) (2 * π) := by
  intro θ
  simp only [wCol, Real.cos_add_two_pi]

lemma wCol_even (η θ : ℝ) : wCol η (-θ) = wCol η θ := by
  simp only [wCol, Real.cos_neg]

lemma contDiff_wCol (η : ℝ) : ContDiff ℝ 2 (wCol η) :=
  Real.smoothTransition.contDiff.comp
    ((Real.contDiff_cos.sub contDiff_const).div_const η)

lemma continuous_wCol (η : ℝ) : Continuous (wCol η) := (contDiff_wCol η).continuous

/-! ### The cut field and the junction part -/

/-- The arc test field with the junction collar removed: `ψ_η = vF·wCol η`. -/
def psiF (η θ : ℝ) : ℂ := vF θ * ((wCol η θ : ℝ) : ℂ)

/-- The junction part `f = vF·(1 − wCol η)`. -/
def fJ (η θ : ℝ) : ℂ := vF θ * (1 - ((wCol η θ : ℝ) : ℂ))

lemma psiF_add_fJ (η θ : ℝ) : psiF η θ + fJ η θ = vF θ := by
  simp only [psiF, fJ]
  ring

/-- `ψ_η` vanishes wherever `cos ≤ η` — in particular on the whole closed dark side and in
the `η`-collar of both junctions, providing a positive support margin. -/
lemma psiF_eq_zero {η θ : ℝ} (hη : 0 < η) (h : Real.cos θ ≤ η) : psiF η θ = 0 := by
  simp only [psiF, wCol_eq_zero hη h, Complex.ofReal_zero, mul_zero]

/-- The junction part vanishes where the collar factor saturates (`cos ≥ 2η`). -/
lemma fJ_eq_zero_of_ge {η θ : ℝ} (hη : 0 < η) (h : 2 * η ≤ Real.cos θ) : fJ η θ = 0 := by
  simp only [fJ, wCol_eq_one hη h, Complex.ofReal_one, sub_self, mul_zero]

/-- The junction part vanishes off the open arc (through `vF`). -/
lemma fJ_eq_zero_of_nonpos {η θ : ℝ} (h : Real.cos θ ≤ 0) : fJ η θ = 0 := by
  simp only [fJ, vF_eq_zero_of_nonpos h, zero_mul]

/-- The L¹ envelope of the junction part: `‖fJ‖ ≤ hAmp` pointwise. -/
lemma norm_fJ_le (η θ : ℝ) : ‖fJ η θ‖ ≤ hAmp θ := by
  simp only [fJ, norm_mul]
  have h1 : ‖1 - ((wCol η θ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [show (1 : ℂ) - ((wCol η θ : ℝ) : ℂ) = ((1 - wCol η θ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [(wCol_mem η θ).2])]
    linarith [(wCol_mem η θ).1]
  calc ‖vF θ‖ * ‖1 - ((wCol η θ : ℝ) : ℂ)‖ ≤ hAmp θ * 1 :=
        mul_le_mul (le_of_eq (norm_vF θ)) h1 (norm_nonneg _) (hAmp_nonneg θ)
    _ = hAmp θ := mul_one _

lemma psiF_periodic (η : ℝ) : Function.Periodic (psiF η) (2 * π) := by
  intro θ
  simp only [psiF, vF_periodic θ, wCol_periodic η θ]

lemma fJ_periodic (η : ℝ) : Function.Periodic (fJ η) (2 * π) := by
  intro θ
  simp only [fJ, vF_periodic θ, wCol_periodic η θ]

lemma continuous_psiF (η : ℝ) : Continuous (psiF η) :=
  continuous_vF.mul (Complex.continuous_ofReal.comp (continuous_wCol η))

lemma continuous_fJ (η : ℝ) : Continuous (fJ η) :=
  continuous_vF.mul
    (continuous_const.sub (Complex.continuous_ofReal.comp (continuous_wCol η)))

end KsIndex.ArcField
