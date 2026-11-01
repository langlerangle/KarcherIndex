module

public import KsIndexLean.SphericalTwoChartJacobi
public import KsIndexLean.SphericalSlitDomain

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

lemma sphericalSlit_subset_equator (k : ℕ) :
    sphericalSlit k ⊆ {p : Sphere | p.val 2 = 0} := by
  rintro p ⟨z, hz, rfl⟩
  exact (stereoPoint_equator_iff z).mpr hz.1

lemma sphericalSlit_null (k : ℕ) :
    (volume : Measure Ambient).toSphere (sphericalSlit k) = 0 :=
  measure_mono_null (sphericalSlit_subset_equator k) sphere_equator_null

/-- Removing the slits preserves area measure, but need not preserve weak domains. -/
lemma canonicalArea_restrict_slitSphere (k : ℕ) :
    (volume : Measure Ambient).toSphere.restrict (slitSphere k) =
      (volume : Measure Ambient).toSphere := by
  apply Measure.restrict_eq_self_of_ae_mem
  change ∀ᵐ p ∂(volume : Measure Ambient).toSphere, p ∉ sphericalSlit k
  simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using sphericalSlit_null k

theorem sum_weakJacobi_eq_slitSphere_integral (k : ℕ) (V : BoundedRealPotential)
    (uN uS vN vS : ComplexH1) :
    weakJacobi V uN vN + weakJacobi V uS vS =
      ∫ p in slitSphere k, twoChartJacobiDensity V uN uS vN vS p
        ∂(volume : Measure Ambient).toSphere := by
  rw [canonicalArea_restrict_slitSphere]
  exact sum_weakJacobi_eq_sphere_integral V uN uS vN vS

end KsIndex.Spherical
