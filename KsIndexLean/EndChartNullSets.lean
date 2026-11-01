module

public import KsIndexLean.EndChartSheets

@[expose] public section


/-! Null sets pull back to null sets under the finite branched end chart.
The only possible zero of the Jacobian is the center, itself a null set. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.EndChart

theorem volume_preimage_endChart_eq_zero (p : ℂ) {m : ℕ} (hm : 0 < m)
    {T : Set ℂ} (hT : MeasurableSet T) (hnull : volume T = 0) :
    volume (endChart p m ⁻¹' T) = 0 := by
  let S : ℕ → Set ℂ := fun j => (endChart p m ⁻¹' T ∩ powSector m j) \ {0}
  have hc : Continuous (endChart p m) := by
    unfold endChart
    fun_prop
  have hS : ∀ j, MeasurableSet (S j) := fun j =>
    ((hT.preimage hc.measurable).inter (measurableSet_powSector m j)).diff
      (measurableSet_singleton 0)
  have hzero : ∀ j, volume (S j) = 0 := by
    intro j
    have hi : InjOn (endChart p m) (S j) :=
      (injOn_endChart_powSector p hm j).mono (fun z hz => hz.1.2)
    have him : volume (endChart p m '' S j) = 0 :=
      measure_mono_null (by rintro _ ⟨z, hz, rfl⟩; exact hz.1.1) hnull
    have he := lintegral_endChart_sheet p m (hS j) hi (fun _ => 1)
    simp only [lintegral_one, Measure.restrict_apply_univ, mul_one] at he
    rw [him] at he
    have hmeas : Measurable (fun z : ℂ =>
        ENNReal.ofReal ((m : ℝ)^2 * ‖z‖^(2*(m-1)))) := by fun_prop
    have hae := (lintegral_eq_zero_iff hmeas).mp he.symm
    have hf : ∀ᵐ z : ℂ ∂volume.restrict (S j), False := by
      filter_upwards [hae, ae_restrict_mem (hS j)] with z hz hzs
      have hz0 : z ≠ 0 := by simpa using hzs.2
      have hpos : 0 < (m : ℝ)^2 * ‖z‖^(2*(m-1)) := by
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm
        have hn := norm_pos_iff.mpr hz0
        positivity
      exact (ne_of_gt (ENNReal.ofReal_pos.mpr hpos)) hz
    simpa [ae_iff] using hf
  have hsub : endChart p m ⁻¹' T ⊆ {0} ∪ ⋃ j, S j := by
    intro z hz
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · obtain ⟨j, _, hj⟩ := exists_mem_powSector hm z
      exact Or.inr (mem_iUnion.mpr ⟨j, ⟨hz, hj⟩, hz0⟩)
  apply measure_mono_null hsub
  exact measure_union_null (measure_singleton _) (measure_iUnion_null hzero)

theorem volume_endChart_seam_eq_zero (p : ℂ) {m : ℕ} (hm : 0 < m) :
    volume {z : ℂ | ‖endChart p m z‖ = 1} = 0 := by
  have h := volume_preimage_endChart_eq_zero p hm
    (Metric.isClosed_sphere.measurableSet : MeasurableSet (Metric.sphere (0 : ℂ) 1))
    (Measure.addHaar_sphere volume 0 1)
  simpa [Metric.sphere, dist_zero_right] using h

end KsIndex.EndChart
