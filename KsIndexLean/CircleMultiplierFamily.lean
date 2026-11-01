module

public import KsIndexLean.CircleMultiplier
public import Mathlib.Topology.CompactOpen

@[expose] public section

/-! # Continuous families of circle multiplication operators

The multiplier-to-operator map is real linear and bounded in the uniform norm.
Its evaluation is jointly continuous in the multiplier and the L² input.
Restricting a continuous planar function to circles of varying real radius
provides a continuous family of real multipliers.
-/
open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace

lemma circleMul_left_add (η θ : C(Circle₁, ℝ)) (F : Lp ℂ 2 circleMeasure) :
    circleMul (η + θ) F = circleMul η F + circleMul θ F := by
  apply Lp.ext
  filter_upwards [circleMul_coe (η + θ) F, circleMul_coe η F, circleMul_coe θ F,
    Lp.coeFn_add (circleMul η F) (circleMul θ F)] with w hs hη hθ ha
  rw [hs, ha]
  change (η w + θ w) • F w = circleMul η F w + circleMul θ F w
  rw [hη, hθ, add_smul]

lemma circleMul_left_smul (c : ℝ) (η : C(Circle₁, ℝ)) (F : Lp ℂ 2 circleMeasure) :
    circleMul (c • η) F = c • circleMul η F := by
  apply Lp.ext
  filter_upwards [circleMul_coe (c • η) F, circleMul_coe η F,
    Lp.coeFn_smul c (circleMul η F)] with w hs hη hc
  rw [hs, hc]
  change (c * η w) • F w = c • circleMul η F w
  rw [hη, mul_smul]

/-- The real multiplier varies continuously in the uniform norm. -/
def circleMultiplierFamily : C(Circle₁, ℝ) →L[ℝ]
    (Lp ℂ 2 circleMeasure →L[ℂ] Lp ℂ 2 circleMeasure) :=
  LinearMap.mkContinuous
    { toFun := circleMulCLM
      map_add' := by
        intro η θ
        apply ContinuousLinearMap.ext
        intro F
        exact circleMul_left_add η θ F
      map_smul' := by
        intro c η
        apply ContinuousLinearMap.ext
        intro F
        exact circleMul_left_smul c η F }
    1 (fun η => by
      change ‖circleMulCLM η‖ ≤ 1 * ‖η‖
      rw [one_mul]
      exact (circleMulCLM η).opNorm_le_bound (norm_nonneg η) (norm_circleMul_le η))

lemma continuous_circleMul : Continuous (fun p : C(Circle₁, ℝ) × Lp ℂ 2 circleMeasure =>
    circleMul p.1 p.2) :=
  (circleMultiplierFamily.continuous.comp continuous_fst).clm_apply continuous_snd

def radialCircleMultiplier (χ : ℂ → ℝ) (hχ : Continuous χ) (r : ℝ) : C(Circle₁, ℝ) :=
  ⟨fun w => χ (r • (w : ℂ)), hχ.comp ((continuous_const (y := r)).smul
    (continuous_subtype_val : Continuous (fun w : Circle₁ => (w : ℂ))))⟩

lemma continuous_radialCircleMultiplier (χ : ℂ → ℝ) (hχ : Continuous χ) :
    Continuous (radialCircleMultiplier χ hχ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × Circle₁ => χ (p.1 • (p.2 : ℂ)))
  exact hχ.comp (continuous_fst.smul
    ((continuous_subtype_val : Continuous (fun w : Circle₁ => (w : ℂ))).comp continuous_snd))

end KsIndex.Trace
