module

public import KsIndexLean.KarcherQuotientDirichlet

@[expose] public section


/-! The actual immersion's curvature magnitude in quotient disk coordinates,
and its contribution to the global Jacobi energy. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open scoped QuotientArea

lemma absA_conj (k : ℕ) (z : ℂ) :
    Surface.absA k ((starRingEnd ℂ) z) = Surface.absA k z := by
  simp only [Surface.absA, rho_conj, Complex.norm_conj]

lemma absA_sigma {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ 0)
    (hp : z ∉ Surface.punctures k) : Surface.absA k (Bracket.σ z) = Surface.absA k z := by
  simp only [Bracket.σ, one_div]
  rw [absA_inv hk (by simpa using hz) (conjugate_not_puncture hp), absA_conj]

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- Curvature magnitude in the common disk coordinate. Its geometric
identification uses the actual second fundamental form, below. -/
def quotientAbsA
    (x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) : ℝ :=
  Surface.absA k (R.diskCoordinate x).val.val

lemma measurable_quotientAbsA : Measurable (R.quotientAbsA (m := m)) :=
  (measurable_absA k).comp R.continuous_diskCoordinate_val.measurable

lemma quotientAbsA_even_geometry (j : ZMod m) (w : PuncturedClosedDisk k) :
    R.quotientAbsA (R.orderedDiskPoint (evenCopyIndex j) w) =
      conformalSecondFundamentalNorm (R.centeredChart (R.evenDiskPoint j.val w))
        w.val.val (Surface.rho k w.val.val ^ 2) := by
  rw [quotientAbsA, R.diskCoordinate_orderedDiskPoint]
  exact (R.centeredChart_finite_curvature _ w.val (R.evenDiskPoint_projection j.val w)).2.symm

lemma quotientAbsA_odd_geometry (j : ZMod m) (w : PuncturedClosedDisk k) (hw : w.val.val ≠ 0) :
    R.quotientAbsA (R.orderedDiskPoint (oddCopyIndex j) w) =
      conformalSecondFundamentalNorm (R.centeredChart (R.oddDiskPoint j.val w))
        (Bracket.σ w.val.val) (Surface.rho k (Bracket.σ w.val.val) ^ 2) := by
  let v : PuncturedPlane k := ⟨Bracket.σ w.val.val,
    by simpa only [Bracket.σ, one_div] using inverse_conjugate_not_puncture w.val.property⟩
  have hp : HeightLift.projection (R.oddDiskPoint j.val w) = finiteParameter v := by
    rw [R.oddDiskPoint_projection]
    simpa only [v, Bracket.σ, one_div] using
      parameterSeamReflection_finite h.out w.val hw (inverse_conjugate_not_puncture w.val.property)
  have hc := (R.centeredChart_finite_curvature _ v hp).2
  change conformalSecondFundamentalNorm _ (Bracket.σ w.val.val)
    (Surface.rho k (Bracket.σ w.val.val) ^ 2) = Surface.absA k (Bracket.σ w.val.val) at hc
  rw [quotientAbsA, R.diskCoordinate_orderedDiskPoint, hc, absA_sigma h.out hw w.val.property]

lemma quotientAbsA_ae_geometry :
    ∀ᵐ x ∂(R.quotientArea (m := m)),
      ∃ (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (v : PuncturedPlane k),
        HeightLift.periodQuotientMap m q = x ∧ HeightLift.projection q = finiteParameter v ∧
        R.quotientAbsA x = conformalSecondFundamentalNorm (R.centeredChart q)
          v.val (Surface.rho k v.val ^ 2) := by
  filter_upwards [R.ae_quotient_interior_nonzero (m := m)] with x hx
  obtain ⟨n, w, hw, hw0, rfl⟩ := hx
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · exact ⟨R.evenDiskPoint j.val w, w.val, (R.orderedDiskPoint_even j w).symm,
      R.evenDiskPoint_projection j.val w, R.quotientAbsA_even_geometry j w⟩
  · let v : PuncturedPlane k := ⟨Bracket.σ w.val.val,
      by simpa only [Bracket.σ, one_div] using inverse_conjugate_not_puncture w.val.property⟩
    refine ⟨R.oddDiskPoint j.val w, v, (R.orderedDiskPoint_odd j w).symm, ?_,
      R.quotientAbsA_odd_geometry j w hw0⟩
    rw [R.oddDiskPoint_projection]
    simpa only [v, Bracket.σ, one_div] using
      parameterSeamReflection_finite h.out w.val hw0 (inverse_conjugate_not_puncture w.val.property)

lemma lintegral_quotientPotential
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hG : Continuous G) :
    ∫⁻ q, ENNReal.ofReal (R.quotientAbsA q ^ 2 * ‖G q‖ ^ 2) ∂(R.quotientArea) =
      ewPotentialEnergyGeom R G := by
  rw [R.lintegral_quotientArea (fun q => ENNReal.ofReal (R.quotientAbsA q ^ 2 * ‖G q‖ ^ 2))
    ((R.measurable_quotientAbsA.pow_const 2).mul
    (hG.measurable.norm.pow_const 2)).ennreal_ofReal]
  unfold ewPotentialEnergyGeom
  apply Finset.sum_congr rfl
  intro n _
  have he : (fun w : PuncturedClosedDisk k => ENNReal.ofReal
      (R.quotientAbsA (R.orderedDiskPoint n w) ^ 2 * ‖G (R.orderedDiskPoint n w)‖ ^ 2)) =
      (fun w : PuncturedClosedDisk k => ENNReal.ofReal (Surface.absA k w.val.val ^ 2 *
        ‖encodeDiskFunction (R.diskFunctionPullback G) n w.val.val‖ ^ 2)) := by
    funext w
    rw [quotientAbsA, R.diskCoordinate_orderedDiskPoint, encodeDiskFunction_on_disk]
    rfl
  rw [he, lintegral_ewDiskMeasure h.out
    (fun z => ENNReal.ofReal (Surface.absA k z ^ 2 *
      ‖encodeDiskFunction (R.diskFunctionPullback G) n z‖ ^ 2))]
  symm
  apply lintegral_ew_eq_disk_of_exterior
  intro z hz
  simp [encodeDiskFunction_exterior _ n z hz]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
