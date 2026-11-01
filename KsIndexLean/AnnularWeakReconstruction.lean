module

public import KsIndexLean.AnnularCartesianIntegral

@[expose] public section


open Set MeasureTheory
open scoped ContDiff Distributions InnerProductSpace

noncomputable section
namespace KsIndex.Trace

lemma integrableOn_annulus_of_memLp {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    IntegrableOn u (annulusSet a b) volume := by
  simpa only [one_smul] using
    integrableOn_continuous_real_smul ha hab (S := fun _ => 1) continuous_const hu

/-- A genuine annular test vanishes on each endpoint circle. -/
lemma annular_test_endpoints {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (φ : 𝓓(annulusOpens a b, ℝ)) :
    (∀ w : Circle₁, φ (a • (w : ℂ)) = 0) ∧ (∀ w : Circle₁, φ (b • (w : ℂ)) = 0) := by
  have hzero {z : ℂ} (hz : ‖z‖ = a ∨ ‖z‖ = b) : φ z = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    have hs := φ.tsupport_subset ht
    change a < ‖z‖ ∧ ‖z‖ < b at hs
    rcases hz with hz | hz
    · exact (lt_irrefl a) (hz ▸ hs.1)
    · exact (lt_irrefl b) (hz ▸ hs.2)
  constructor
  · intro w
    apply hzero (Or.inl _)
    simp [Real.norm_eq_abs, abs_of_pos ha]
  · intro w
    apply hzero (Or.inr _)
    simp [Real.norm_eq_abs, abs_of_pos (ha.trans hab)]

/-- Local integrability and actual annular test integrals give the genuine weak derivative. -/
lemma weakLine_annulus_of_test_integrals {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u X : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (hX : MemLp X 2 (volume.restrict (annulusSet a b))) (d : ℂ)
    (ht : ∀ φ : 𝓓(annulusOpens a b, ℝ),
      (∫ z in annulusSet a b, fderiv ℝ (φ : ℂ → ℝ) z d • u z + φ z • X z) = 0) :
    TauCeti.HasWeakLineDerivOn volume (annulusOpens a b) u X d := by
  have huI := integrableOn_annulus_of_memLp ha hab hu
  have hXI := integrableOn_annulus_of_memLp ha hab hX
  apply TauCeti.hasWeakLineDerivOn_iff_testFunction.mpr
  refine ⟨inferInstance, huI.locallyIntegrableOn, hXI.locallyIntegrableOn, fun φ => ?_⟩
  have hd : Continuous (fun z => fderiv ℝ (φ : ℂ → ℝ) z d) :=
    (contDiff_infty_iff_fderiv.mp φ.contDiff).2.continuous.clm_apply continuous_const
  have hi := integrableOn_continuous_real_smul ha hab hd hu
  have hj := integrableOn_continuous_real_smul ha hab φ.continuous hX
  have hz := ht φ
  rw [integral_add hi hj] at hz
  have hline : ∀ z, lineDeriv ℝ (φ : ℂ → ℝ) z d = fderiv ℝ (φ : ℂ → ℝ) z d :=
    fun z => (φ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv
  simp_rw [← hline] at hz
  change (∫ z in (annulusOpens a b : Set ℂ), lineDeriv ℝ (φ : ℂ → ℝ) z d • u z) +
    (∫ z in (annulusOpens a b : Set ℂ), φ z • X z) = 0 at hz
  rw [TauCeti.setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ d,
    TauCeti.setIntegral_smul_eq_integral_smul φ] at hz
  exact add_eq_zero_iff_eq_neg.mp hz

def reconstructedJet (v q : ℂ → ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (reconstructedX v q z) + Complex.imCLM.smulRight (reconstructedY v q z)

lemma memLp_reconstructedJet {a b : ℝ} (ha : 0 < a) {v q : ℂ → ℂ}
    (hv : MemLp v 2 (volume.restrict (annulusSet a b)))
    (hq : MemLp q 2 (volume.restrict (annulusSet a b))) :
    MemLp (reconstructedJet v q) 2 (volume.restrict (annulusSet a b)) :=
  ((memLp_reconstructedX ha hv hq).continuousLinearMap_comp
    (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.reCLM)).add
    ((memLp_reconstructedY ha hv hq).continuousLinearMap_comp
      (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM))

/-- Reconstruct the actual annular weak Fréchet derivative from radial and angular weak data. -/
theorem annular_weak_reconstruction {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u v q : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (hv : MemLp v 2 (volume.restrict (annulusSet a b)))
    (hq : MemLp q 2 (volume.restrict (annulusSet a b)))
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (sliceLp a b u) (sliceLp a b v) 1)
    (hθ : ∀ᵐ r ∂volume.restrict (Ioo a b),
      (sliceLp a b u r, sliceLp a b q r) ∈ circleAngularGraph) :
    TauCeti.HasWeakFDerivOn volume (annulusOpens a b) u (reconstructedJet v q) := by
  have hx : TauCeti.HasWeakLineDerivOn volume (annulusOpens a b) u (reconstructedX v q) 1 := by
    apply weakLine_annulus_of_test_integrals ha hab hu (memLp_reconstructedX ha hv hq)
    intro φ
    exact annular_cartesian_integral_one ha hab hu hv hq hw hθ φ.contDiff
      (annular_test_endpoints ha hab φ).1 (annular_test_endpoints ha hab φ).2
  have hy : TauCeti.HasWeakLineDerivOn volume (annulusOpens a b) u (reconstructedY v q)
      Complex.I := by
    apply weakLine_annulus_of_test_integrals ha hab hu (memLp_reconstructedY ha hv hq)
    intro φ
    exact annular_cartesian_integral_I ha hab hu hv hq hw hθ φ.contDiff
      (annular_test_endpoints ha hab φ).1 (annular_test_endpoints ha hab φ).2
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro e
  have h := (hx.smul_direction e.re).add_direction (hy.smul_direction e.im)
  have he : e.re • (1 : ℂ) + e.im • Complex.I = e := by
    apply Complex.ext <;> simp [Complex.real_smul]
  rw [he] at h
  exact h

end KsIndex.Trace
