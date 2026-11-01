module

public import KsIndexLean.SphericalChartOperator
public import KsIndexLean.SmoothSphericalEigen
public import KsIndexLean.GeneralDirichletLowest

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral
/-- The eigenvalue equation for minus the spherical chart operator is the
flat Jacobi equation with the spherical mass term added to the potential. -/
lemma sphericalChart_eigen_pde (k : ℕ) (lam : ℝ) (u : ℂ → ℂ) (z : ℂ)
    (he : sphericalChartJacobiOperator k u z = -(lam : ℂ) * u z) :
    Surface.laplacian u z +
      (((surfacePotential k).V z + lam * stereoAreaDensity z : ℝ) : ℂ) * u z = 0 := by
  rw [sphericalChartJacobiOperator_eq] at he
  have hd : (stereoAreaDensity z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (stereoAreaDensity_pos z))
  have hh := congrArg (fun x : ℂ => (stereoAreaDensity z : ℂ) * x) he
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul] at hh
  change Surface.laplacian u z +
    (((Surface.potV k z) + lam * stereoAreaDensity z : ℝ) : ℂ) * u z = 0
  push_cast
  linear_combination hh

local instance : CompleteSpace (zeroTraceDomain Set.univ) :=
  (isClosed_zeroTraceDomain Set.univ).completeSpace_coe

/-- A globally smooth chart eigenfunction with pointwise zero boundary belongs
to the full weak Dirichlet eigenspace with canonical spherical mass. -/
lemma sphericalChart_dirichlet_mem_eigenspace (k : ℕ) (lam : ℝ)
    (u : ℂ → ℂ) (hu : ContDiff ℝ ∞ u) (hb : ∀ w : Circle₁, u w = 0)
    (he : ∀ z ∈ (disk : Set ℂ), sphericalChartJacobiOperator k u z = -(lam : ℂ) * u z) :
    (⟨globalSmoothH1 u hu, globalSmoothH1_zeroTrace_of_boundary u hu hb⟩ :
      zeroTraceDomain Set.univ) ∈
      diskWeakEigenspace (zeroTraceDomain Set.univ) (surfacePotential k) lam := by
  apply (mem_diskWeakEigenspace_all _ _ _ _).mpr
  intro v
  exact smooth_spherical_eigen_weak (surfacePotential k) lam u hu
    (fun z hz => sphericalChart_eigen_pde k lam u z (he z hz)) v v.property

/-- Such a nonzero Dirichlet eigenfunction cannot have negative eigenvalue. -/
lemma sphericalChart_dirichlet_eigenvalue_nonnegative {k : ℕ} (hk : 3 ≤ k) (lam : ℝ)
    (u : ℂ → ℂ) (hu : ContDiff ℝ ∞ u) (hb : ∀ w : Circle₁, u w = 0)
    (hne : globalSmoothH1 u hu ≠ 0)
    (he : ∀ z ∈ (disk : Set ℂ), sphericalChartJacobiOperator k u z = -(lam : ℂ) * u z) :
    0 ≤ lam := by
  apply fullDirichlet_eigenvalue_nonnegative hk lam
    ⟨globalSmoothH1 u hu, globalSmoothH1_zeroTrace_of_boundary u hu hb⟩
  · intro h
    exact hne (congrArg Subtype.val h)
  · exact sphericalChart_dirichlet_mem_eigenspace k lam u hu hb he
end KsIndex.Spherical
