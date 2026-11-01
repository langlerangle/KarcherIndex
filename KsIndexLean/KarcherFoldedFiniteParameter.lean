module

public import KsIndexLean.KarcherFilledVertexTopology
public import KsIndexLean.KarcherUpperSeamFormula
public import KsIndexLean.KarcherEndProjectionExtension

@[expose] public section


/-! The folded disk coordinate in terms of the finite sphere parameter. -/
noncomputable section
namespace KsIndex.KarcherData

/-- Fold the exterior of the unit disk by inversion in its boundary circle. -/
def foldUnitDisk (z : ℂ) : ℂ := if ‖z‖ ≤ 1 then z else (starRingEnd ℂ z)⁻¹

/-- Inversion agrees with the identity on the unit circle, so folding is
continuous even across the seam. -/
lemma continuous_foldUnitDisk : Continuous foldUnitDisk := by
  apply continuous_if_le continuous_norm continuous_const continuous_id.continuousOn
  · apply (Complex.continuous_conj.continuousOn).inv₀
    intro z hz
    apply (map_ne_zero (starRingEnd ℂ)).mpr
    intro he
    simp only [Set.mem_ofPred_eq, he, norm_zero] at hz
    norm_num at hz
  · intro z hz
    rw [Complex.inv_eq_conj (by simpa using hz)]
    simp

@[simp] lemma foldUnitDisk_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : foldUnitDisk z = z := by
  simp [foldUnitDisk, hz]

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma foldedDiskCoordinate_finite (R : PaperHalfPeriodRealization k)
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m)
    (z : PuncturedPlane k)
    (hp : HeightLift.quotientProjection m q = finiteParameter z) :
    R.foldedDiskCoordinate q = foldUnitDisk z.val := by
  obtain ⟨j, w, rfl | rfl⟩ := R.periodDiskCopies_cover m q
  · have he : w.val = z := finiteParameter_injective k
      ((R.evenDiskPoint_projection j w).symm.trans hp)
    have hc : R.foldedDiskCoordinate (R.evenPeriodPoint m j w) = w.val.val := by
      rw [← R.orderedDiskPoint_even_int]
      exact R.foldedDiskCoordinate_apply _ _
    rw [hc, ← he, foldUnitDisk, ite_eq_left w.property]
  · obtain ⟨hw0, hz⟩ := R.oddPoint_finite_parameter j w z hp
    have hc : R.foldedDiskCoordinate (R.oddPeriodPoint m j w) = w.val.val := by
      rw [← R.orderedDiskPoint_odd_int]
      exact R.foldedDiskCoordinate_apply _ _
    rw [hc, foldUnitDisk]
    split_ifs with hn
    · have hmul : ‖z.val‖ * ‖w.val.val‖ = 1 := by
        rw [hz, norm_inv, Complex.norm_conj]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)
      have hw1 : ‖w.val.val‖ = 1 := by
        nlinarith [w.property, norm_nonneg z.val, norm_nonneg w.val.val]
      rw [hz, Complex.inv_eq_conj (by simpa using hw1)]
      simp
    · rw [hz, map_inv₀, starRingEnd_self_apply, inv_inv]

/-- Approaching a puncture in the finite parameter approaches the corresponding
added vertex, regardless of which period sheets occur along the approach. -/
theorem tendsto_filled_of_finite_parameter (R : PaperHalfPeriodRealization k)
    {α : Type*} {l : Filter α}
    {f : α → HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m}
    {z : α → PuncturedPlane k} (w : ℂ) (hw : w ∈ Surface.punctures k)
    (hp : ∀ a, HeightLift.quotientProjection m (f a) = finiteParameter (z a))
    (hz : Filter.Tendsto (fun a => (z a).val) l (nhds w)) :
    Filter.Tendsto (fun a => (DiskCompactification.periodQuotientHomeomorph R (f a)).val)
      l (nhds (DiskCompactification.vertex w hw)) := by
  rw [DiskCompactification.tendsto_periodQuotient_vertex_iff]
  have he : (fun a => R.foldedDiskCoordinate (f a)) =
      (fun a => foldUnitDisk (z a).val) :=
    funext (fun a => R.foldedDiskCoordinate_finite _ _ (hp a))
  rw [he]
  simpa only [Function.comp_def, foldUnitDisk_of_norm_one (puncture_norm h.out hw)] using
    continuous_foldUnitDisk.continuousAt.tendsto.comp hz

/-- The inverse of the existing punctured root chart converges to the filled
vertex as its root coordinate approaches zero. -/
theorem tendsto_filled_of_endRoot (R : PaperHalfPeriodRealization k)
    {α : Type*} {l : Filter α}
    {f : α → HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m}
    {z : α → PuncturedPlane k} (w : ℂ) (hw : w ∈ Surface.punctures k)
    (hp : ∀ a, HeightLift.quotientProjection m (f a) = finiteParameter (z a))
    (hs : ∀ a, (z a).val ∈ (endCoordinateChart h.out hw).source)
    (ht : Filter.Tendsto (fun a => quotientEndRoot h.out (NeZero.pos m)
      (reflectionBasepoint k) w R.C (f a)) l (nhds 0)) :
    Filter.Tendsto (fun a => (DiskCompactification.periodQuotientHomeomorph R (f a)).val)
      l (nhds (DiskCompactification.vertex w hw)) := by
  apply R.tendsto_filled_of_finite_parameter w hw hp
  have he : (fun a => (z a).val) = (fun a =>
      filledEndParameter h.out hw (reflectionBasepoint k) (m := m)
        (quotientEndRoot h.out (NeZero.pos m) (reflectionBasepoint k) w R.C (f a))) := by
    funext a
    exact (filledEndParameter_quotientEndRoot h.out (NeZero.pos m) hw
      (reflectionBasepoint k) R.C (f a) (z a) (hs a) (hp a)).symm
  rw [he]
  simpa only [Function.comp_def, filledEndParameter_zero h.out (NeZero.pos m)] using
    (continuousAt_filledEndParameter_zero h.out (NeZero.pos m) hw
      (reflectionBasepoint k)).tendsto.comp ht

end PaperHalfPeriodRealization
end KsIndex.KarcherData
