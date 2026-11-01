module

public import KsIndexLean.KarcherSeamBands
public import KsIndexLean.KarcherDiskEncoding

@[expose] public section


/-! The paper's gluing formula is the actual parameter expression on an upper-seam band. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma encoded_evenPoint (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    encodeDiskFunction (R.diskFunctionPullback f) (evenCopyIndex (j : ZMod m)) w.val.val =
      f (R.evenPeriodPoint m j w) := by
  rw [encodeDiskFunction_on_disk]
  change f (R.orderedDiskPoint (evenCopyIndex (j : ZMod m)) w) = _
  rw [orderedDiskPoint_even_int]

lemma encoded_oddPoint (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    encodeDiskFunction (R.diskFunctionPullback f) (oddCopyIndex (j : ZMod m)) w.val.val =
      f (R.oddPeriodPoint m j w) := by
  rw [encodeDiskFunction_on_disk]
  change f (R.orderedDiskPoint (oddCopyIndex (j : ZMod m)) w) = _
  rw [orderedDiskPoint_odd_int]

lemma oddPoint_finite_parameter (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) (z : PuncturedPlane k)
    (hp : HeightLift.projection (R.oddDiskPoint j w) = finiteParameter z) :
    w.val.val ≠ 0 ∧ z.val = (starRingEnd ℂ w.val.val)⁻¹ := by
  rw [oddDiskPoint_projection] at hp
  have hw : w.val.val ≠ 0 := by
    intro hz
    have he : w.val = ⟨0, zero_not_puncture h.out⟩ := Subtype.ext hz
    rw [he, parameterSeamReflection_zero] at hp
    exact finiteParameter_ne_infinity z hp.symm
  refine ⟨hw, ?_⟩
  rw [parameterSeamReflection_finite h.out w.val hw
    (inverse_conjugate_not_puncture w.val.property)] at hp
  exact (congrArg Subtype.val (finiteParameter_injective k hp)).symm

lemma upperSeamBand_glue_formula (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (z : PuncturedPlane k) (hq : q ∈ R.upperSeamBand j)
    (hp : HeightLift.projection q = finiteParameter z) :
    f (HeightLift.periodQuotientMap m q) =
      Surface.glue (encodeDiskFunction (R.diskFunctionPullback f))
        (evenCopyIndex (j : ZMod m)) z.val := by
  obtain ⟨w, rfl | rfl⟩ := R.upperSeamBand_copies j hq
  · rw [evenDiskPoint_projection] at hp
    have he : w.val = z := finiteParameter_injective k hp
    rw [← he]
    rw [Surface.glue, if_pos w.property]
    exact (R.encoded_evenPoint f j w).symm
  · obtain ⟨hw0, hz⟩ := R.oddPoint_finite_parameter j w z hp
    by_cases hn : ‖z.val‖ ≤ 1
    · have hmul : ‖z.val‖ * ‖w.val.val‖ = 1 := by
        rw [hz, norm_inv, Complex.norm_conj]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)
      have hw1 : ‖w.val.val‖ = 1 := by nlinarith [w.property, norm_nonneg z.val, norm_nonneg w.val.val]
      have hew := R.even_eq_odd_on_circle_in_band j w hw1 hq
      have hez : w.val = z := by
        rw [← hew, evenDiskPoint_projection] at hp
        exact finiteParameter_injective k hp
      rw [← hez, Surface.glue, if_pos w.property]
      rw [← hew]
      exact (R.encoded_evenPoint f j w).symm
    · have hz' : 1 / starRingEnd ℂ z.val = w.val.val := by
        rw [hz]
        rw [map_inv₀, starRingEnd_self_apply, one_div, inv_inv]
      rw [Surface.glue, if_neg hn, evenCopyIndex_succ, hz']
      exact (R.encoded_oddPoint f j w).symm

end KsIndex.KarcherData.PaperHalfPeriodRealization
