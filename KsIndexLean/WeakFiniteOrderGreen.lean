module

public import KsIndexLean.FiniteOrderGreen
public import KsIndexLean.SmoothWeakGreen
public import KsIndexLean.SphericalEigenPotential
public import KsIndexLean.WeakDirichletModeSelection

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk KsIndex.GradOrtho KsIndex.Surface
/-- Green identity for H¹ carriers represented by a C² first function and a C¹ test. -/
lemma weakJacobi_C2_representative_test_green (V : BoundedRealPotential)
    (u v : ℂ → ℂ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 1 v)
    (uH1 vH1 : ComplexH1)
    (huval : valueCLM uH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] u)
    (hux : dxCLM uH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun w => fderiv ℝ u w 1))
    (huy : dyCLM uH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun w => fderiv ℝ u w Complex.I))
    (hval : valueCLM vH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] v)
    (hdx : dxCLM vH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun w => fderiv ℝ v w 1))
    (hdy : dyCLM vH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun w => fderiv ℝ v w Complex.I))
    (hjac : ∀ w ∈ (WeakH1.disk : Set ℂ), laplacian u w + (V.V w : ℂ) * u w = 0) :
    weakJacobi V uH1 vH1 =
      ∫ w : Circle₁, (starRingEnd ℂ) (fderiv ℝ u w w) * v w ∂circleMeasure := by
  have hp : Integrable (fun w => (V.V w : ℂ) * (starRingEnd ℂ) (u w) * v w)
      (volume.restrict (WeakH1.disk : Set ℂ)) := by
    apply (potential_integrable V uH1 vH1).congr
    filter_upwards [huval, hval] with w h1 h2
    rw [h1, h2]
  have hg : Integrable (gradInner u v) (volume.restrict (WeakH1.disk : Set ℂ)) := by
    apply (dirichlet_integrable uH1 vH1).congr
    filter_upwards [hux, huy,
      hdx, hdy] with w h1 h2 h3 h4
    simp only [gradInner, h1, h2, h3, h4]
  rw [weakJacobi_integral_representatives V _ _ (huval)
    (hval) (hux) (huy)
    (hdx) (hdy)]
  change (∫ w in (WeakH1.disk : Set ℂ), gradInner u v w) - _ = _
  rw [← integral_sub hg hp, ← first_green_C2 u v hu hv]
  apply setIntegral_congr_fun WeakH1.disk.isOpen.measurableSet
  intro w hw
  have hl : laplacian u w = -((V.V w : ℂ) * u w) := eq_neg_of_add_eq_zero_left (hjac w hw)
  dsimp only
  rw [hl, map_neg, map_mul, Complex.conj_ofReal]
  ring

/-- The C² representative Green identity extended to every weak H¹ test by density. -/
lemma weak_C2_green_of_flux (V : BoundedRealPotential) (u : ℂ → ℂ)
    (hu : ContDiff ℝ 2 u) (uH1 : ComplexH1)
    (huval : valueCLM uH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] u)
    (hux : dxCLM uH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun w => fderiv ℝ u w 1))
    (huy : dyCLM uH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun w => fderiv ℝ u w Complex.I))
    (hjac : ∀ w ∈ (WeakH1.disk : Set ℂ), laplacian u w + (V.V w : ℂ) * u w = 0)
    (F : Lp ℂ 2 circleMeasure)
    (hF : (F : Circle₁ → ℂ) =ᵐ[circleMeasure] fun w => fderiv ℝ u w w)
    (v : ComplexH1) :
    weakJacobi V uH1 v = inner ℂ F (diskTraceCLM v) := by
  have hc : Continuous (fun v : mixedCharacterDomain 1 0 true true =>
      weakJacobi V uH1 v) :=
    (continuous_weakJacobi_fixed_left V uH1).comp continuous_subtype_val
  have hb : Continuous (fun v : mixedCharacterDomain 1 0 true true =>
      inner ℂ F (diskTraceCLM v)) :=
    continuous_const.inner (diskTraceCLM.continuous.comp continuous_subtype_val)
  have he := (naturalCharacterToMixed_denseRange (k := 1) (by decide) 0 true true).equalizer
    hc hb (by
      funext f
      let ff : KsIndex.SingleDisk.NatCc 1 true true := ⟨f.val, f.property.1⟩
      obtain ⟨G, hG, hv, hx, hy, ht⟩ := naturalCoreH1_C1_representative (by decide : 1 ≤ 1) ff
      have hg := weakJacobi_C2_representative_test_green V u G hu hG uH1
        (naturalCoreH1 (by decide) ff) huval hux huy hv hx hy hjac
      change weakJacobi V uH1 (naturalCoreH1 (by decide) ff) =
        inner ℂ F (diskTraceCLM (naturalCoreH1 (by decide) ff))
      rw [hg, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hF, ht] with w hw htw
      simp only [RCLike.inner_apply, hw, htw, mul_comm])
  exact congrFun he ⟨v, mem_trivial_NN_sector v⟩

open KsIndex.Spherical
/-- A C² representative satisfying the spherical chart PDE gives the full
Dirichlet weak eigenvalue equation. -/
lemma C2_spherical_eigen_weak (V : BoundedRealPotential) (lam : ℝ)
    (u : ℂ → ℂ) (hu : ContDiff ℝ 2 u) (uH1 : ComplexH1)
    (huval : valueCLM uH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] u)
    (hux : dxCLM uH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun w => fderiv ℝ u w 1))
    (huy : dyCLM uH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun w => fderiv ℝ u w Complex.I))
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ), Surface.laplacian u z +
      ((V.V z + lam * stereoAreaDensity z : ℝ) : ℂ) * u z = 0)
    (v : ComplexH1) (hv : v ∈ zeroTraceDomain Set.univ) :
    weakJacobi V uH1 v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM uH1)
        (weightedDiskValueCLM v) := by
  have hc : Continuous (fun w : Circle₁ => fderiv ℝ u w w) :=
    ((hu.continuous_fderiv (by norm_num)).comp continuous_subtype_val).clm_apply
      continuous_subtype_val
  let flux : C(Circle₁, ℂ) := ⟨_, hc⟩
  have hf := flux.memLp (μ := circleMeasure) (p := 2) ℂ
  apply (spherical_eigen_equation_iff V lam _ _).mpr
  rw [weak_C2_green_of_flux (sphericalEigenPotential V lam) u hu uH1 huval hux huy he
    (hf.toLp flux) (MemLp.coeFn_toLp hf) v,
    (mem_fullZeroTrace_iff v).mp hv, inner_zero_right]
end KsIndex.Trace
