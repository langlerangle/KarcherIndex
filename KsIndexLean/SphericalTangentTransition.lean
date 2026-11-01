module

public import KsIndexLean.SphericalJoinedJacobi
public import KsIndexLean.InversionJetTransition

@[expose] public section


open Set
open scoped Topology
noncomputable section
namespace KsIndex.Spherical

/-- Equatorial reflection as a real continuous linear map. -/
def reflectAmbientCLM : Ambient →L[ℝ] Ambient where
  toFun := reflectAmbient
  map_add' u v := by ext i; fin_cases i <;> simp [reflectAmbient, add_comm]
  map_smul' r u := by ext i; fin_cases i <;> simp [reflectAmbient]
  cont := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

lemma hasFDerivAt_southPoint (z : ℂ) :
    HasFDerivAt (fun w => (southChart w).val)
      (reflectAmbientCLM.comp (fderiv ℝ stereoPoint z)) z := by
  exact reflectAmbientCLM.hasFDerivAt.comp z
    ((contDiff_stereoPoint.differentiable (by simp)).differentiableAt.hasFDerivAt)

lemma fderiv_southPoint_apply (z w : ℂ) :
    fderiv ℝ (fun a => (southChart a).val) z w =
      reflectAmbient (fderiv ℝ stereoPoint z w) := by
  rw [(hasFDerivAt_southPoint z).fderiv]
  rfl

lemma differentiableAt_sigma {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℝ KsIndex.Bracket.σ z := by
  have hc : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
  have h := (hasFDerivAt_inv' (𝕜 := ℝ) hc).comp z
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  have he : KsIndex.Bracket.σ = fun w => ((starRingEnd ℂ) w)⁻¹ := by
    funext w
    simp [KsIndex.Bracket.σ]
  rw [he]
  exact h.differentiableAt

/-- The geometric inversion transition, differentiated away from its pole. -/
lemma stereoPoint_sigma_tangent {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    fderiv ℝ stereoPoint (KsIndex.Bracket.σ z) (fderiv ℝ KsIndex.Bracket.σ z w) =
      reflectAmbient (fderiv ℝ stereoPoint z w) := by
  have he : (fun a => stereoPoint (KsIndex.Bracket.σ a)) =ᶠ[𝓝 z]
      (fun a => (southChart a).val) := by
    filter_upwards [eventually_ne_nhds hz] with a ha
    exact (congrArg Subtype.val (southChart_eq_sigma ha)).symm
  have h := ((contDiff_stereoPoint.differentiable (by simp)).differentiableAt.hasFDerivAt).comp
    z (differentiableAt_sigma hz).hasFDerivAt
  have hs := h.congr_of_eventuallyEq he.symm
  have heq := hs.fderiv
  have hw := congrArg (fun L : ℂ →L[ℝ] Ambient => L w) heq
  simpa only [fderiv_southPoint_apply, ContinuousLinearMap.comp_apply] using hw.symm

end KsIndex.Spherical
