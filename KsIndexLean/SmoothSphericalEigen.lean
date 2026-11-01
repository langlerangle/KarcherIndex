module

public import KsIndexLean.WeakDirichletModeSelection
public import KsIndexLean.SmoothWeakGreen
public import KsIndexLean.SphericalEigenPotential

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical
/-- A smooth chart eigenfunction satisfies the spherical-mass weak equation
against every full Dirichlet test; the boundary flux is constructed from its derivative. -/
lemma smooth_spherical_eigen_weak (V : BoundedRealPotential) (lam : ℝ)
    (u : ℂ → ℂ) (hu : ContDiff ℝ ∞ u)
    (he : ∀ z ∈ (disk : Set ℂ), Surface.laplacian u z +
      ((V.V z + lam * stereoAreaDensity z : ℝ) : ℂ) * u z = 0)
    (v : ComplexH1) (hv : v ∈ zeroTraceDomain Set.univ) :
    weakJacobi V (globalSmoothH1 u hu) v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM (globalSmoothH1 u hu))
        (weightedDiskValueCLM v) := by
  have hc : Continuous (fun w : Circle₁ => fderiv ℝ u w w) :=
    ((hu.continuous_fderiv (by norm_num)).comp continuous_subtype_val).clm_apply
      continuous_subtype_val
  let flux : C(Circle₁, ℂ) := ⟨_, hc⟩
  have hf := flux.memLp (μ := circleMeasure) (p := 2) ℂ
  apply (spherical_eigen_equation_iff V lam _ _).mpr
  rw [smooth_weak_green_of_flux (sphericalEigenPotential V lam) u hu he
    (hf.toLp flux) (MemLp.coeFn_toLp hf) v,
    (mem_fullZeroTrace_iff v).mp hv, inner_zero_right]
/-- Pointwise vanishing on the circle gives the full Sobolev Dirichlet condition. -/
lemma globalSmoothH1_zeroTrace_of_boundary (u : ℂ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hb : ∀ w : Circle₁, u w = 0) :
    globalSmoothH1 u hu ∈ zeroTraceDomain Set.univ := by
  apply (mem_fullZeroTrace_iff _).mpr
  apply Lp.ext
  filter_upwards [globalSmoothH1_trace u hu, Lp.coeFn_zero ℂ 2 circleMeasure] with w hw hz
  rw [hw, hb, hz]
  rfl
end KsIndex.Trace
