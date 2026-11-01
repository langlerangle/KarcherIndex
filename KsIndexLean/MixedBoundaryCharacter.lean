module

public import KsIndexLean.MixedClassicalUniqueness

@[expose] public section


/-! The paper rotation character extends to the physical punctured boundary
by continuity and invariance of the deleted-point set. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.WeakH1 KsIndex.FormIndex

/-- The paper rotation preserves the physical closed half-disk domain. -/
lemma paperRotation_mapsTo_puncturedClosedDisk {k : ℕ} (hk : 0 < k) :
    MapsTo (planeRotation (-(2 * Real.pi) / k))
      (Metric.closedBall (0 : ℂ) 1 \ punctures k)
      (Metric.closedBall (0 : ℂ) 1 \ punctures k) := by
  intro z hz
  have he : planeRotation (-(2 * Real.pi) / k) z = (SurfaceSym.rotUnit k : ℂ) * z := by
    simp only [planeRotation_apply, SurfaceSym.rotUnit, Circle.coe_exp]
  have hp : (SurfaceSym.rotUnit k : ℂ) ^ (2 * k) = 1 := by
    rw [two_mul, pow_add, SurfaceSym.rotUnit_pow hk, one_mul]
  constructor
  · simpa only [Metric.mem_closedBall, dist_zero_right, (planeRotation _).norm_map] using hz.1
  · rw [he]
    simpa only [punctures, Set.mem_setOf_eq, mul_pow, hp, one_mul] using hz.2

/-- Interior character covariance determines the boundary covariance too;
no values at deleted punctures or exterior points are involved. -/
theorem mixed_character_on_puncturedClosedDisk {k : ℕ} (hk : 2 ≤ k)
    {b1 b0 : Bool} (U : ClassicalMixedHalfDiskJacobi k b1 b0) (j : ℕ)
    (hi : ∀ z ∈ (Surface.disk : Set ℂ),
      U.value (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * U.value z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1 \ punctures k,
      U.value (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * U.value z := by
  have hc := U.continuousOn_puncturedClosedDisk
  apply Set.EqOn.of_subset_closure hi
    (hc.comp (planeRotation _).continuous.continuousOn
      (paperRotation_mapsTo_puncturedClosedDisk (by omega)))
    (continuousOn_const.mul hc)
  · intro z hz
    exact ⟨Metric.ball_subset_closedBall hz, punctures_notMem_disk (by omega) hz⟩
  · change Metric.closedBall (0 : ℂ) 1 \ punctures k ⊆ closure (Metric.ball 0 1)
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact sdiff_subset

/-- The bounded inverse retains the paper character on its entire physical domain. -/
theorem dn_radical_classical_closed_character {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) (hu : u ∈ mixedCharacterDomain k j true false)
    (hQ : ∀ v ∈ mixedCharacterDomain k j true false,
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ U : ClassicalMixedHalfDiskJacobi k true false, U.toH1 hk = u ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1 \ punctures k,
        U.value (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * U.value z := by
  obtain ⟨U, he, hc⟩ := dn_radical_classical_character hk j u hu hQ
  exact ⟨U, he, mixed_character_on_puncturedClosedDisk hk U j hc⟩

end KsIndex.Trace
