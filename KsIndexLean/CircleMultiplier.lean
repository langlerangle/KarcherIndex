module

public import KsIndexLean.AngularCoordinateTests
public import KsIndexLean.ArcRadialGluing

@[expose] public section

/-! # Continuous real multipliers on circle L²

Multiplication by a continuous real circle function defines a bounded complex
linear operator with norm at most the multiplier's uniform norm. The operator
is symmetric for the L² inner product and commutes with weak interval
derivatives of L²-valued functions when the multiplier is fixed.
-/
open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

lemma memLp_circle_mul (η : C(Circle₁, ℝ)) (F : Lp ℂ 2 circleMeasure) :
    MemLp (fun w => η w • F w) 2 circleMeasure := by
  apply (Lp.memLp F).of_le_mul (c := ‖η‖)
    (η.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable F))
  exact Filter.Eventually.of_forall fun w => by
    change ‖η w • F w‖ ≤ ‖η‖ * ‖F w‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (η.norm_coe_le_norm w) (norm_nonneg _)

def circleMul (η : C(Circle₁, ℝ)) (F : Lp ℂ 2 circleMeasure) : Lp ℂ 2 circleMeasure :=
  (memLp_circle_mul η F).toLp (fun w => η w • F w)

lemma circleMul_coe (η : C(Circle₁, ℝ)) (F : Lp ℂ 2 circleMeasure) :
    circleMul η F =ᵐ[circleMeasure] fun w => η w • F w :=
  (memLp_circle_mul η F).coeFn_toLp

lemma circleMul_add (η : C(Circle₁, ℝ)) (F G : Lp ℂ 2 circleMeasure) :
    circleMul η (F + G) = circleMul η F + circleMul η G := by
  apply Lp.ext
  filter_upwards [circleMul_coe η (F + G), circleMul_coe η F, circleMul_coe η G,
    Lp.coeFn_add F G, Lp.coeFn_add (circleMul η F) (circleMul η G)] with w h hF hG ha hb
  simp only [Pi.add_apply] at ha hb
  rw [h, hb, hF, hG, ha, smul_add]

lemma circleMul_smul (η : C(Circle₁, ℝ)) (c : ℂ) (F : Lp ℂ 2 circleMeasure) :
    circleMul η (c • F) = c • circleMul η F := by
  apply Lp.ext
  filter_upwards [circleMul_coe η (c • F), circleMul_coe η F,
    Lp.coeFn_smul c F, Lp.coeFn_smul c (circleMul η F)] with w h hF ha hb
  simp only [Pi.smul_apply] at ha hb
  rw [h, hb, hF, ha, smul_comm]

lemma norm_circleMul_le (η : C(Circle₁, ℝ)) (F : Lp ℂ 2 circleMeasure) :
    ‖circleMul η F‖ ≤ ‖η‖ * ‖F‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [circleMul_coe η F] with w hw
  rw [hw, norm_smul]
  exact mul_le_mul_of_nonneg_right (η.norm_coe_le_norm w) (norm_nonneg _)

def circleMulCLM (η : C(Circle₁, ℝ)) : Lp ℂ 2 circleMeasure →L[ℂ] Lp ℂ 2 circleMeasure :=
  LinearMap.mkContinuous
    { toFun := circleMul η
      map_add' := circleMul_add η
      map_smul' := circleMul_smul η }
    ‖η‖ (norm_circleMul_le η)

lemma inner_circleMul (η : C(Circle₁, ℝ)) (F G : Lp ℂ 2 circleMeasure) :
    inner ℂ F (circleMul η G) = inner ℂ (circleMul η F) G := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circleMul_coe η F, circleMul_coe η G] with w hF hG
  rw [hF, hG]
  simp [Complex.real_smul, mul_comm, mul_left_comm]

lemma circleMul_weakInterval (η : C(Circle₁, ℝ)) {a b : ℝ}
    {f g : ℝ → Lp ℂ 2 circleMeasure}
    (h : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (fun r => circleMul η (f r)) (fun r => circleMul η (g r)) 1 :=
  weakInterval_comp ((circleMulCLM η).restrictScalars ℝ) h

end KsIndex.Trace
