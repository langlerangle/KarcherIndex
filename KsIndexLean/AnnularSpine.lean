module

public import KsIndexLean.CircleMeasure
public import KsIndexLean.Surface
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

@[expose] public section


/-! # Boundary values controlled by annular energy

For a complex-valued function `u` that is `C¹` on an open neighborhood of
`A = {w | 1/2 ≤ ‖w‖ ≤ 1}`, `annular_spine_estimate` proves
`∫_S ‖u‖² dσ ≤ 8 ∫_A ‖u‖² + 2 ∫_A ‖radialDeriv u‖²`.
The derivative is the Fréchet derivative evaluated in the unit radial
direction. `annular_spine_gradSq` bounds the circle integral by eight
times the sum of the annular squared-value integral and the
`Surface.gradSq` integral.

The proof first applies the fundamental theorem of calculus along each
radius, inserts the polar radial weight and then integrates over the
angle. Both conclusions concern the assigned boundary values of a `C¹`
function; no weak function class or trace operator is used here.
-/

open MeasureTheory Set Complex intervalIntegral
open scoped Real

noncomputable section

namespace KsIndex.Trace

/-- The closed annulus `½ ≤ ‖w‖ ≤ 1`. -/
def annulus : Set ℂ := {w : ℂ | 1 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 1}

lemma mem_annulus {w : ℂ} : w ∈ annulus ↔ 1 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 1 := Iff.rfl

/-- The unit direction at angle `θ`. -/
abbrev dir (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

@[simp] lemma norm_dir (θ : ℝ) : ‖dir θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

lemma ray_mem_annulus {r θ : ℝ} (h1 : 1 / 2 ≤ r) (h2 : r ≤ 1) :
    (r : ℂ) * dir θ ∈ annulus := by
  have : ‖(r : ℂ) * dir θ‖ = r := by
    rw [norm_mul, norm_dir, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  exact ⟨by rw [this]; exact h1, by rw [this]; exact h2⟩

section Estimate

variable {u : ℂ → ℂ} {U : Set ℂ}

/-- The radial derivative along the ray at angle `θ`. -/
lemma hasDerivAt_ray (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U)
    {r θ : ℝ} (hmem : (r : ℂ) * dir θ ∈ U) :
    HasDerivAt (fun s : ℝ => u ((s : ℂ) * dir θ))
      (fderiv ℝ u ((r : ℂ) * dir θ) (dir θ)) r := by
  have hcurve : HasDerivAt (fun s : ℝ => (s : ℂ) * dir θ) (dir θ) r := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (dir θ)
  have hdiff : DifferentiableAt ℝ u ((r : ℂ) * dir θ) :=
    (hu.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hmem)
  exact (hdiff.hasFDerivAt.comp_hasDerivAt r hcurve)

/-- Continuity of the radial-derivative integrand in the radius. -/
lemma continuousOn_rayDeriv (hU : IsOpen U) (hAU : annulus ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) (θ : ℝ) :
    ContinuousOn (fun s : ℝ => fderiv ℝ u ((s : ℂ) * dir θ) (dir θ)) (Icc (1 / 2) 1) := by
  have hf : ContinuousOn (fderiv ℝ u) U :=
    hu.continuousOn_fderiv_of_isOpen hU le_rfl
  have hcurve : Continuous (fun s : ℝ => (s : ℂ) * dir θ) :=
    Complex.continuous_ofReal.mul continuous_const
  have hmem : ∀ s ∈ Icc (1 / 2 : ℝ) 1, (s : ℂ) * dir θ ∈ U := fun s hs =>
    hAU (ray_mem_annulus hs.1 hs.2)
  exact ((hf.comp hcurve.continuousOn hmem).clm_apply continuousOn_const)

/-- Value continuity along the ray. -/
lemma continuousOn_rayValue (_hU : IsOpen U) (hAU : annulus ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) (θ : ℝ) :
    ContinuousOn (fun s : ℝ => u ((s : ℂ) * dir θ)) (Icc (1 / 2) 1) := by
  have hcurve : Continuous (fun s : ℝ => (s : ℂ) * dir θ) :=
    Complex.continuous_ofReal.mul continuous_const
  exact hu.continuousOn.comp hcurve.continuousOn
    (fun s hs => hAU (ray_mem_annulus hs.1 hs.2))

/-- Continuity of the scalar integrand `‖φ‖² + ‖D‖²` along a ray. -/
lemma continuousOn_raySq (hU : IsOpen U) (hAU : annulus ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) (θ : ℝ) :
    ContinuousOn (fun t : ℝ => ‖u ((t : ℂ) * dir θ)‖ ^ 2 +
      ‖fderiv ℝ u ((t : ℂ) * dir θ) (dir θ)‖ ^ 2) (Icc (1 / 2) 1) :=
  (((continuousOn_rayValue hU hAU hu θ).norm.pow 2).add
    (((continuousOn_rayDeriv hU hAU hu θ).norm.pow 2)))

lemma half_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num
lemma uIcc_half : uIcc (1 / 2 : ℝ) 1 = Icc (1 / 2 : ℝ) 1 := uIcc_of_le half_le_one

/-- The per-angle bound, obtained by applying the fundamental theorem of
calculus to the squared norm along each radius. -/
lemma ray_sq_bound (hU : IsOpen U) (hAU : annulus ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) (θ : ℝ) :
    ‖u (dir θ)‖ ^ 2 ≤ 4 * (∫ t in (1 / 2 : ℝ)..1, ‖u ((t : ℂ) * dir θ)‖ ^ 2)
      + ∫ t in (1 / 2 : ℝ)..1, ‖fderiv ℝ u ((t : ℂ) * dir θ) (dir θ)‖ ^ 2 := by
  set φ : ℝ → ℂ := fun t => u ((t : ℂ) * dir θ) with hφ
  set D : ℝ → ℂ := fun t => fderiv ℝ u ((t : ℂ) * dir θ) (dir θ) with hD
  have hmem : ∀ t ∈ Icc (1 / 2 : ℝ) 1, (t : ℂ) * dir θ ∈ U := fun t ht =>
    hAU (ray_mem_annulus ht.1 ht.2)
  have hφc : ContinuousOn φ (Icc (1 / 2) 1) := continuousOn_rayValue hU hAU hu θ
  have hDc : ContinuousOn D (Icc (1 / 2) 1) := continuousOn_rayDeriv hU hAU hu θ
  have hKint : IntervalIntegrable (fun t => ‖φ t‖ ^ 2 + ‖D t‖ ^ 2) volume (1 / 2) 1 :=
    ((continuousOn_raySq hU hAU hu θ).mono uIcc_half.le).intervalIntegrable
  have hφint : IntervalIntegrable (fun t => ‖φ t‖ ^ 2) volume (1 / 2) 1 :=
    ((hφc.norm.pow 2).mono uIcc_half.le).intervalIntegrable
  have hDint : IntervalIntegrable (fun t => ‖D t‖ ^ 2) volume (1 / 2) 1 :=
    ((hDc.norm.pow 2).mono uIcc_half.le).intervalIntegrable
  set K : ℝ := ∫ t in (1 / 2 : ℝ)..1, (‖φ t‖ ^ 2 + ‖D t‖ ^ 2) with hK
  -- FTC on `[r, 1]` for `‖φ‖²`, then the elementary inner-product bound
  have key : ∀ r ∈ Icc (1 / 2 : ℝ) 1, ‖φ 1‖ ^ 2 ≤ ‖φ r‖ ^ 2 + K := by
    intro r hr
    have hinner : ContinuousOn (fun t => 2 * (inner ℝ (φ t) (D t) : ℝ)) (Icc r 1) :=
      continuousOn_const.mul ((hφc.mono (Icc_subset_Icc hr.1 le_rfl)).inner
        (hDc.mono (Icc_subset_Icc hr.1 le_rfl)))
    have hftc : (∫ t in r..1, 2 * (inner ℝ (φ t) (D t) : ℝ)) =
        ‖φ 1‖ ^ 2 - ‖φ r‖ ^ 2 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => ‖φ t‖ ^ 2)
      · intro t ht
        rw [uIcc_of_le hr.2] at ht
        exact (hasDerivAt_ray hU hu (hmem t ⟨le_trans hr.1 ht.1, ht.2⟩)).norm_sq
      · exact (hinner.mono (uIcc_of_le hr.2).le).intervalIntegrable
    have hpt : ∀ t ∈ Icc r 1, 2 * (inner ℝ (φ t) (D t) : ℝ) ≤ ‖φ t‖ ^ 2 + ‖D t‖ ^ 2 := by
      intro t _
      have hle := real_inner_le_norm (φ t) (D t)
      nlinarith [sq_nonneg (‖φ t‖ - ‖D t‖)]
    have hmono : (∫ t in r..1, 2 * (inner ℝ (φ t) (D t) : ℝ)) ≤
        ∫ t in r..1, (‖φ t‖ ^ 2 + ‖D t‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on hr.2
        ((hinner.mono (uIcc_of_le hr.2).le).intervalIntegrable)
        (hKint.mono_set (by rw [uIcc_half, uIcc_of_le hr.2]
                            exact Icc_subset_Icc hr.1 le_rfl)) hpt
    have htail : (∫ t in r..1, (‖φ t‖ ^ 2 + ‖D t‖ ^ 2)) ≤ K := by
      apply intervalIntegral.integral_mono_interval hr.1 hr.2 le_rfl
      · filter_upwards with t
        positivity
      · exact hKint
    linarith [hftc, hmono, htail]
  -- integrate the per-radius bound over `r ∈ [1 / 2, 1]`
  have hconst : (∫ r in (1 / 2 : ℝ)..1, ‖φ 1‖ ^ 2) = (1 / 2) * ‖φ 1‖ ^ 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  have hrint : (∫ r in (1 / 2 : ℝ)..1, (‖φ r‖ ^ 2 + K)) =
      (∫ r in (1 / 2 : ℝ)..1, ‖φ r‖ ^ 2) + (1 / 2) * K := by
    rw [intervalIntegral.integral_add hφint intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  have hint2 : (∫ r in (1 / 2 : ℝ)..1, ‖φ 1‖ ^ 2) ≤
      ∫ r in (1 / 2 : ℝ)..1, (‖φ r‖ ^ 2 + K) := by
    apply intervalIntegral.integral_mono_on half_le_one intervalIntegrable_const
      (hφint.add intervalIntegrable_const)
    intro r hr
    exact key r hr
  have hKsplit : K = (∫ t in (1 / 2 : ℝ)..1, ‖φ t‖ ^ 2) +
      ∫ t in (1 / 2 : ℝ)..1, ‖D t‖ ^ 2 := by
    rw [hK, intervalIntegral.integral_add hφint hDint]
  have hφnonneg : 0 ≤ ∫ t in (1 / 2 : ℝ)..1, ‖φ t‖ ^ 2 := by
    apply intervalIntegral.integral_nonneg half_le_one
    intro t _
    positivity
  have hval1 : φ 1 = u (dir θ) := by
    rw [hφ]
    norm_num
  rw [← hval1]
  rw [hconst, hrint] at hint2
  linarith [hint2, hKsplit, hφnonneg]

/-- Doubling under the radial weight: `1 ≤ 2t` on the window. -/
lemma weight_double {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (1 / 2) 1)
    (hft : IntervalIntegrable (fun t => t * f t) volume (1 / 2) 1)
    (h0 : ∀ t ∈ Icc (1 / 2 : ℝ) 1, 0 ≤ f t) :
    (∫ t in (1 / 2 : ℝ)..1, f t) ≤ 2 * ∫ t in (1 / 2 : ℝ)..1, t * f t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on half_le_one hf (hft.const_mul 2)
  intro t ht
  nlinarith [h0 t ht, ht.1]

/-- Clamp the radius into the annular window. -/
def clampT (t : ℝ) : ℝ := max (1 / 2) (min t 1)

lemma continuous_clampT : Continuous clampT :=
  continuous_const.max (continuous_id.min continuous_const)

lemma clampT_mem (t : ℝ) : clampT t ∈ Icc (1 / 2 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · apply max_le (by norm_num)
    exact min_le_right _ _

lemma clampT_eq {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) : clampT t = t := by
  rw [clampT, min_eq_left ht.2, max_eq_right ht.1]

section Global

variable {u : ℂ → ℂ} {U : Set ℂ}

/-- The clamped ray map, globally continuous into the annulus. -/
lemma continuous_clampRay :
    Continuous (fun p : ℝ × ℝ => ((clampT p.2 : ℝ) : ℂ) * dir p.1) := by
  apply Continuous.mul
  · exact Complex.continuous_ofReal.comp (continuous_clampT.comp continuous_snd)
  · exact (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const))

lemma clampRay_mem_annulus (p : ℝ × ℝ) :
    ((clampT p.2 : ℝ) : ℂ) * dir p.1 ∈ annulus :=
  ray_mem_annulus (clampT_mem p.2).1 (clampT_mem p.2).2

/-- Global continuity of the clamped value integrand. -/
lemma continuous_valIntegrand (_hU : IsOpen U) (hAU : annulus ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) :
    Continuous (fun p : ℝ × ℝ => p.2 * ‖u (((clampT p.2 : ℝ) : ℂ) * dir p.1)‖ ^ 2) := by
  apply continuous_snd.mul
  apply Continuous.pow
  apply Continuous.norm
  exact hu.continuousOn.comp_continuous continuous_clampRay
    (fun p => hAU (clampRay_mem_annulus p))

/-- Global continuity of the clamped derivative integrand. -/
lemma continuous_derIntegrand (hU : IsOpen U) (hAU : annulus ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) :
    Continuous (fun p : ℝ × ℝ =>
      p.2 * ‖fderiv ℝ u (((clampT p.2 : ℝ) : ℂ) * dir p.1) (dir p.1)‖ ^ 2) := by
  apply continuous_snd.mul
  apply Continuous.pow
  apply Continuous.norm
  have hf : Continuous (fun p : ℝ × ℝ =>
      fderiv ℝ u (((clampT p.2 : ℝ) : ℂ) * dir p.1)) :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).comp_continuous continuous_clampRay
      (fun p => hAU (clampRay_mem_annulus p))
  have hdir : Continuous (fun p : ℝ × ℝ => dir p.1) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
  exact isBoundedBilinearMap_apply.continuous.comp (hf.prodMk hdir)

/-- The weighted per-angle inner integrals, as continuous functions of the angle. -/
def valSlice (u : ℂ → ℂ) (θ : ℝ) : ℝ :=
  ∫ t in (1 / 2 : ℝ)..1, t * ‖u ((t : ℂ) * dir θ)‖ ^ 2
def derSlice (u : ℂ → ℂ) (θ : ℝ) : ℝ :=
  ∫ t in (1 / 2 : ℝ)..1, t * ‖fderiv ℝ u ((t : ℂ) * dir θ) (dir θ)‖ ^ 2

lemma valSlice_eq_clamped (θ : ℝ) : valSlice u θ =
    ∫ t in (1 / 2 : ℝ)..1, t * ‖u (((clampT t : ℝ) : ℂ) * dir θ)‖ ^ 2 := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_half] at ht
  change t * ‖u ((t : ℂ) * dir θ)‖ ^ 2 = t * ‖u (((clampT t : ℝ) : ℂ) * dir θ)‖ ^ 2
  rw [clampT_eq ht]
lemma derSlice_eq_clamped (θ : ℝ) : derSlice u θ =
    ∫ t in (1 / 2 : ℝ)..1, t * ‖fderiv ℝ u (((clampT t : ℝ) : ℂ) * dir θ) (dir θ)‖ ^ 2 := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_half] at ht
  change t * ‖fderiv ℝ u ((t : ℂ) * dir θ) (dir θ)‖ ^ 2 =
    t * ‖fderiv ℝ u (((clampT t : ℝ) : ℂ) * dir θ) (dir θ)‖ ^ 2
  rw [clampT_eq ht]

lemma continuous_valSlice (hU : IsOpen U) (hAU : annulus ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) : Continuous (valSlice u) := by
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun θ t => t * ‖u (((clampT t : ℝ) : ℂ) * dir θ)‖ ^ 2)
    (continuous_valIntegrand hU hAU hu) (1 / 2) 1
  simpa only [← valSlice_eq_clamped] using h

lemma continuous_derSlice (hU : IsOpen U) (hAU : annulus ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) : Continuous (derSlice u) := by
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun θ t => t * ‖fderiv ℝ u (((clampT t : ℝ) : ℂ) * dir θ) (dir θ)‖ ^ 2)
    (continuous_derIntegrand hU hAU hu) (1 / 2) 1
  simpa only [← derSlice_eq_clamped] using h

/-- The per-angle estimate with radial weight and constants `8` and `2`. -/
lemma ray_sq_bound_weighted (hU : IsOpen U) (hAU : annulus ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) (θ : ℝ) :
    ‖u (dir θ)‖ ^ 2 ≤ 8 * valSlice u θ + 2 * derSlice u θ := by
  have hb := ray_sq_bound hU hAU hu θ
  have hφc := continuousOn_rayValue hU hAU hu θ
  have hDc := continuousOn_rayDeriv hU hAU hu θ
  have hφint : IntervalIntegrable (fun t => ‖u ((t : ℂ) * dir θ)‖ ^ 2) volume (1 / 2) 1 :=
    ((hφc.norm.pow 2).mono uIcc_half.le).intervalIntegrable
  have hDint : IntervalIntegrable
      (fun t => ‖fderiv ℝ u ((t : ℂ) * dir θ) (dir θ)‖ ^ 2) volume (1 / 2) 1 :=
    ((hDc.norm.pow 2).mono uIcc_half.le).intervalIntegrable
  have hφt : IntervalIntegrable (fun t => t * ‖u ((t : ℂ) * dir θ)‖ ^ 2) volume (1 / 2) 1 :=
    (((continuousOn_id.mul (hφc.norm.pow 2))).mono uIcc_half.le).intervalIntegrable
  have hDt : IntervalIntegrable
      (fun t => t * ‖fderiv ℝ u ((t : ℂ) * dir θ) (dir θ)‖ ^ 2) volume (1 / 2) 1 :=
    (((continuousOn_id.mul (hDc.norm.pow 2))).mono uIcc_half.le).intervalIntegrable
  have h1 := weight_double hφint hφt (fun t _ => by positivity)
  have h2 := weight_double hDint hDt (fun t _ => by positivity)
  unfold valSlice derSlice
  linarith [hb, h1, h2]

end Global

end Estimate

section PolarBridge

lemma measurableSet_annulus : MeasurableSet annulus := by
  have : annulus = (fun w : ℂ => ‖w‖) ⁻¹' Icc (1 / 2) 1 := by
    ext w
    simp [mem_annulus, Set.mem_preimage]
  rw [this]
  exact (isClosed_Icc.preimage continuous_norm).measurableSet

lemma polarSymm_eq_dir (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * dir p.2 := by
  rw [Complex.polarCoord_symm_apply]
  unfold dir
  rw [Complex.exp_mul_I]
  push_cast
  ring

/-- The polar change of variables for the annulus, iterated with the angle outside. -/
lemma setIntegral_annulus_polar {F : ℂ → ℝ} (hF : ContinuousOn F annulus) :
    ∫ w in annulus, F w =
      ∫ θ in Ico (-π) π, (∫ t in (1 / 2 : ℝ)..1, t * F ((t : ℂ) * dir θ)) := by
  classical
  set R : Set (ℝ × ℝ) := Icc (1 / 2 : ℝ) 1 ×ˢ Ioo (-π) π with hR
  set g : ℝ × ℝ → ℝ := fun q => q.1 * F (((clampT q.1 : ℝ) : ℂ) * dir q.2) with hg
  have hgc : Continuous g := by
    apply continuous_fst.mul
    apply hF.comp_continuous
    · exact Continuous.mul
        (Complex.continuous_ofReal.comp (continuous_clampT.comp continuous_fst))
        (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
    · intro q
      exact ray_mem_annulus (clampT_mem q.1).1 (clampT_mem q.1).2
  -- step 1: whole-plane integral of the indicator, then polar CoV
  rw [← MeasureTheory.integral_indicator measurableSet_annulus,
    ← Complex.integral_comp_polarCoord_symm (annulus.indicator F)]
  -- step 2: on the target, the integrand is the product-set indicator of g
  have hcong : ∀ q ∈ polarCoord.target,
      q.1 • annulus.indicator F (Complex.polarCoord.symm q) = R.indicator g q := by
    intro q hq
    rw [polarCoord_target] at hq
    obtain ⟨r, θ⟩ := q
    obtain ⟨hr, hθ⟩ := hq
    have hrpos : (0 : ℝ) < r := hr
    have hnorm : ‖(r : ℂ) * dir θ‖ = r := by
      rw [norm_mul, norm_dir, mul_one, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
    rw [polarSymm_eq_dir]
    by_cases hmem : r ∈ Icc (1 / 2 : ℝ) 1
    · have hA : ((r : ℂ) * dir θ) ∈ annulus := by
        rw [mem_annulus, hnorm]
        exact ⟨hmem.1, hmem.2⟩
      have hRq : ((r, θ) : ℝ × ℝ) ∈ R := ⟨hmem, hθ⟩
      rw [Set.indicator_of_mem hA, Set.indicator_of_mem hRq, smul_eq_mul]
      change r * F ((r : ℂ) * dir θ) = r * F (((clampT r : ℝ) : ℂ) * dir θ)
      rw [clampT_eq hmem]
    · have hA : ((r : ℂ) * dir θ) ∉ annulus := by
        rw [mem_annulus, hnorm]
        exact hmem
      have hRq : ((r, θ) : ℝ × ℝ) ∉ R := fun hc => hmem hc.1
      rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hRq, smul_zero]
  rw [MeasureTheory.setIntegral_congr_fun polarCoord.open_target.measurableSet hcong]
  -- step 3: absorb the indicator into the (smaller) product domain
  have hRsub : R ⊆ polarCoord.target := by
    rw [polarCoord_target]
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    exact ⟨lt_of_lt_of_le (by norm_num) hr.1, hθ⟩
  rw [MeasureTheory.setIntegral_indicator (measurableSet_Icc.prod measurableSet_Ioo),
    Set.inter_eq_self_of_subset_right hRsub]
  -- step 4: product set to iterated integrals, angle outside
  have hint : IntegrableOn g R volume := by
    apply ((hgc.continuousOn).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
    exact Set.prod_mono le_rfl Ioo_subset_Icc_self
  rw [IntegrableOn, Measure.volume_eq_prod ℝ ℝ, hR, ← Measure.prod_restrict] at hint
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from
      Measure.volume_eq_prod ℝ ℝ]
  rw [hR, ← Measure.prod_restrict]
  rw [MeasureTheory.integral_prod _ hint]
  rw [MeasureTheory.integral_integral_swap (by exact hint)]
  -- inner: `Icc` set integral to the interval integral (endpoints null); de-clamp
  have hinner : ∀ θ : ℝ, (∫ r in Icc (1 / 2 : ℝ) 1, g (r, θ)) =
      ∫ t in (1 / 2 : ℝ)..1, t * F ((t : ℂ) * dir θ) := by
    intro θ
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le half_le_one]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_half] at ht
    change t * F (((clampT t : ℝ) : ℂ) * dir θ) = t * F ((t : ℂ) * dir θ)
    rw [clampT_eq ht]
  -- outer: `Ioo` to `Ico` (endpoint null)
  rw [MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ico.symm]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro θ _
  exact hinner θ

end PolarBridge



section Main

variable {u : ℂ → ℂ} {U : Set ℂ}

lemma annulus_subset_closedBall : annulus ⊆ Metric.closedBall (0 : ℂ) 1 := by
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hw.2

lemma isCompact_annulus : IsCompact annulus :=
  (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
    (isClosed_Icc.preimage continuous_norm) annulus_subset_closedBall

lemma integrableOn_Ico_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    MeasureTheory.IntegrableOn f (Ico (-π) π) volume :=
  ((hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self)

/-- The radial directional derivative, bound to the actual `fderiv`. -/
def radialDeriv (u : ℂ → ℂ) (w : ℂ) : ℂ := fderiv ℝ u w (((‖w‖ : ℝ) : ℂ)⁻¹ * w)

lemma radialDeriv_ray {t θ : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    radialDeriv u ((t : ℂ) * dir θ) = fderiv ℝ u ((t : ℂ) * dir θ) (dir θ) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
  have hnorm : ‖(t : ℂ) * dir θ‖ = t := by
    rw [norm_mul, norm_dir, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le]
  rw [radialDeriv, hnorm]
  congr 1
  have htne : ((t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ht0.ne'
  field_simp

lemma continuousOn_normSq_annulus (hAU : annulus ⊆ U) (hu : ContDiffOn ℝ 1 u U) :
    ContinuousOn (fun w => ‖u w‖ ^ 2) annulus :=
  (((hu.continuousOn).mono hAU).norm.pow 2)

lemma continuousOn_radialDerivSq_annulus (hU : IsOpen U) (hAU : annulus ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) :
    ContinuousOn (fun w => ‖radialDeriv u w‖ ^ 2) annulus := by
  apply ContinuousOn.pow
  apply ContinuousOn.norm
  have hfd : ContinuousOn (fderiv ℝ u) annulus :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).mono hAU
  have hvec : ContinuousOn (fun w : ℂ => (((‖w‖ : ℝ) : ℂ))⁻¹ * w) annulus := by
    apply ContinuousOn.mul _ continuousOn_id
    apply ContinuousOn.inv₀
    · exact Complex.continuous_ofReal.comp_continuousOn continuous_norm.continuousOn
    · intro w hw
      have : (1 / 2 : ℝ) ≤ ‖w‖ := hw.1
      simp only [ne_eq, Complex.ofReal_eq_zero]
      intro h
      rw [h] at this
      norm_num at this
  exact (isBoundedBilinearMap_apply.continuous.comp_continuousOn (hfd.prodMk hvec))

/-- The circle squared-value integral is bounded by annular value and radial
derivative integrals, for a function that is `C¹` near the closed annulus. -/
theorem annular_spine_estimate (hU : IsOpen U) (hAU : annulus ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) :
    (∫ w : Circle₁, ‖u (w : ℂ)‖ ^ 2 ∂circleMeasure) ≤
      8 * (∫ w in annulus, ‖u w‖ ^ 2) + 2 * ∫ w in annulus, ‖radialDeriv u w‖ ^ 2 := by
  -- the boundary side, over the polar-compatible window
  have hbc : Continuous (fun w : Circle₁ => ‖u (w : ℂ)‖ ^ 2) := by
    apply Continuous.pow
    apply Continuous.norm
    apply hu.continuousOn.comp_continuous continuous_subtype_val
    intro w
    apply hAU
    rw [mem_annulus, mem_sphere_zero_iff_norm.mp w.property]
    norm_num
  have hwin : (∫ w : Circle₁, ‖u (w : ℂ)‖ ^ 2 ∂circleMeasure) =
      ∫ θ in Ico (-π) π, ‖u (dir θ)‖ ^ 2 := by
    have h := integral_circleMeasure_window (-π)
      (f := fun w : Circle₁ => ‖u (w : ℂ)‖ ^ 2) hbc.aestronglyMeasurable
    rw [show -π + 2 * π = π by ring] at h
    rw [h]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ico
    intro θ _
    change ‖u ((circleParam θ : ℂ))‖ ^ 2 = ‖u (dir θ)‖ ^ 2
    rw [circleParam_coe]
  -- the per-angle bound, integrated over the window
  have hval := continuous_valSlice hU hAU hu
  have hder := continuous_derSlice hU hAU hu
  have hmono : (∫ θ in Ico (-π) π, ‖u (dir θ)‖ ^ 2) ≤
      ∫ θ in Ico (-π) π, (8 * valSlice u θ + 2 * derSlice u θ) := by
    apply MeasureTheory.setIntegral_mono_on
    · apply integrableOn_Ico_of_continuous
      apply Continuous.pow
      apply Continuous.norm
      apply hu.continuousOn.comp_continuous
      · exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
      · intro θ
        apply hAU
        rw [mem_annulus]
        rw [show ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 from Complex.norm_exp_ofReal_mul_I θ]
        norm_num
    · exact integrableOn_Ico_of_continuous ((hval.const_mul 8).add (hder.const_mul 2))
    · exact measurableSet_Ico
    · intro θ _
      exact ray_sq_bound_weighted hU hAU hu θ
  -- split, and convert each slice integral by the polar bridge
  have hsplit : (∫ θ in Ico (-π) π, (8 * valSlice u θ + 2 * derSlice u θ)) =
      8 * (∫ θ in Ico (-π) π, valSlice u θ) + 2 * ∫ θ in Ico (-π) π, derSlice u θ := by
    rw [MeasureTheory.integral_add (integrableOn_Ico_of_continuous (hval.const_mul 8))
        (integrableOn_Ico_of_continuous (hder.const_mul 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hbridge_val : (∫ θ in Ico (-π) π, valSlice u θ) = ∫ w in annulus, ‖u w‖ ^ 2 := by
    rw [setIntegral_annulus_polar (continuousOn_normSq_annulus hAU hu)]
    rfl
  have hbridge_der : (∫ θ in Ico (-π) π, derSlice u θ) =
      ∫ w in annulus, ‖radialDeriv u w‖ ^ 2 := by
    rw [setIntegral_annulus_polar (continuousOn_radialDerivSq_annulus hU hAU hu)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ico
    intro θ _
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_half] at ht
    change t * ‖fderiv ℝ u ((t : ℂ) * dir θ) (dir θ)‖ ^ 2 =
      t * ‖radialDeriv u ((t : ℂ) * dir θ)‖ ^ 2
    rw [radialDeriv_ray ht]
  rw [hwin]
  rw [← hbridge_val, ← hbridge_der]
  linarith [hmono, hsplit.symm.le, hsplit.le]

/-- The annular estimate with the radial derivative controlled by
`Surface.gradSq`. -/
theorem annular_spine_gradSq (hU : IsOpen U) (hAU : annulus ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) :
    (∫ w : Circle₁, ‖u (w : ℂ)‖ ^ 2 ∂circleMeasure) ≤
      8 * ((∫ w in annulus, ‖u w‖ ^ 2) + ∫ w in annulus, Surface.gradSq u w) := by
  have h1 := annular_spine_estimate hU hAU hu
  -- pointwise: the radial directional derivative is controlled by `gradSq`
  have hpt : ∀ w ∈ annulus, ‖radialDeriv u w‖ ^ 2 ≤ Surface.gradSq u w := by
    intro w hw
    set L := fderiv ℝ u w with hL
    have hwnorm : (1 / 2 : ℝ) ≤ ‖w‖ := hw.1
    set a : ℝ := ((((‖w‖ : ℝ) : ℂ))⁻¹ * w).re with ha
    set b : ℝ := ((((‖w‖ : ℝ) : ℂ))⁻¹ * w).im with hb
    have hab : a ^ 2 + b ^ 2 = 1 := by
      have hne : ‖w‖ ≠ 0 := by positivity
      have : ‖((‖w‖ : ℝ) : ℂ)⁻¹ * w‖ = 1 := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg w)]
        field_simp
      calc a ^ 2 + b ^ 2 = ‖((‖w‖ : ℝ) : ℂ)⁻¹ * w‖ ^ 2 := by
            rw [ha, hb, Complex.sq_norm, Complex.normSq_apply]
            ring
      _ = 1 := by rw [this]; norm_num
    have hdecomp : (((‖w‖ : ℝ) : ℂ))⁻¹ * w = (a : ℂ) * 1 + (b : ℂ) * Complex.I := by
      rw [ha, hb]
      apply Complex.ext <;> simp
    have hbound : ‖radialDeriv u w‖ ≤ |a| * ‖L 1‖ + |b| * ‖L Complex.I‖ := by
      rw [radialDeriv, ← hL, hdecomp, map_add]
      calc ‖L ((a : ℂ) * 1) + L ((b : ℂ) * Complex.I)‖
          ≤ ‖L ((a : ℂ) * 1)‖ + ‖L ((b : ℂ) * Complex.I)‖ := norm_add_le _ _
      _ = |a| * ‖L 1‖ + |b| * ‖L Complex.I‖ := by
          rw [show ((a : ℂ) * 1) = (a : ℝ) • (1 : ℂ) by simp [Complex.real_smul],
            show ((b : ℂ) * Complex.I) = (b : ℝ) • Complex.I by simp [Complex.real_smul],
            map_smul, map_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have := Surface.gradSq u w
    rw [Surface.gradSq, ← hL]
    nlinarith [hbound, norm_nonneg (radialDeriv u w), norm_nonneg (L 1),
      norm_nonneg (L Complex.I), sq_nonneg (|a| * ‖L Complex.I‖ - |b| * ‖L 1‖),
      sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b]
  have hint : (∫ w in annulus, ‖radialDeriv u w‖ ^ 2) ≤
      ∫ w in annulus, Surface.gradSq u w := by
    apply MeasureTheory.setIntegral_mono_on
    · exact (continuousOn_radialDerivSq_annulus hU hAU hu).integrableOn_compact
        (isCompact_annulus)
    · apply ContinuousOn.integrableOn_compact isCompact_annulus
      apply ContinuousOn.add
      · apply ContinuousOn.pow
        apply ContinuousOn.norm
        exact (isBoundedBilinearMap_apply.continuous.comp_continuousOn
          (((hu.continuousOn_fderiv_of_isOpen hU le_rfl).mono hAU).prodMk
            continuousOn_const))
      · apply ContinuousOn.pow
        apply ContinuousOn.norm
        exact (isBoundedBilinearMap_apply.continuous.comp_continuousOn
          (((hu.continuousOn_fderiv_of_isOpen hU le_rfl).mono hAU).prodMk
            continuousOn_const))
    · exact measurableSet_annulus
    · exact hpt
  have hnn : 0 ≤ ∫ w in annulus, ‖radialDeriv u w‖ ^ 2 := by
    apply MeasureTheory.setIntegral_nonneg measurableSet_annulus
    intro w _
    positivity
  linarith [h1, hint, hnn]

end Main

end KsIndex.Trace
