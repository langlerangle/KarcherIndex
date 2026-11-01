module

public import KsIndexLean.KarcherDiskJacobiOperator

@[expose] public section


/-! Identification of the actual Jacobi operator on ordered disk interiors. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
lemma diskJacobi_congr {k : ℕ} {f g : ℂ → ℂ} {z : ℂ}
    (hg : f =ᶠ[𝓝 z] g) : diskJacobi k f z = diskJacobi k g z := by
  unfold diskJacobi Surface.laplacianG
  rw [JacobiFamily.laplacian_congr hg, hg.eq_of_nhds]

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

omit [NeZero m] in
lemma geometricJacobiAt_eq_diskJacobi
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.geometricJacobiAt G q = diskJacobi k
      (G ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm)
      (R.chartCenter q) := by
  rw [R.geometricJacobiAt_eq]
  have hc : (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q))
      (HeightLift.periodQuotientMap m q) = R.chartCenter q := by
    rw [HeightLift.periodChart_apply, chartCenter, HeightLift.liftChart_apply]
    rfl
  have hv := (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).left_inv
    (HeightLift.periodChart_mem R.hC m _)
  rw [hc] at hv
  simp only [diskJacobi, Function.comp_apply, hv]

lemma geometricJacobi_evenCopy
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) :
    R.geometricJacobi G (R.evenPeriodPoint m j w) =
      diskJacobi k (encodeDiskFunction (R.diskFunctionPullback G)
        (evenCopyIndex (j : ZMod m))) w.val.val := by
  change R.geometricJacobiAt G (R.evenDiskPoint j w) = _
  rw [R.geometricJacobiAt_eq_diskJacobi,
    R.chartCenter_finite _ w.val (R.evenDiskPoint_projection j w)]
  exact diskJacobi_congr ((R.upperSeam_glue_germ G j (R.evenDiskPoint j w) w.val
    (R.evenDiskPoint_mem_upper_interior j w hw) (R.evenDiskPoint_projection j w)).trans
      (glue_interior_germ _ _ hw))

lemma geometricJacobi_oddCopy_nonzero
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hG : letI := HeightLift.periodChartedSpace R.hC m;
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) (hw0 : w.val.val ≠ 0) :
    R.geometricJacobi G (R.oddPeriodPoint m j w) =
      diskJacobi k (encodeDiskFunction (R.diskFunctionPullback G)
        (oddCopyIndex (j : ZMod m))) w.val.val := by
  let q := R.oddDiskPoint j w
  let v : PuncturedPlane k := ⟨Bracket.σ w.val.val,
    by simpa only [Bracket.σ, one_div] using inverse_conjugate_not_puncture w.val.property⟩
  have hp : HeightLift.projection q = finiteParameter v := by
    rw [R.oddDiskPoint_projection]
    simpa only [v, Bracket.σ, one_div] using
      parameterSeamReflection_finite h.out w.val hw0 (inverse_conjugate_not_puncture w.val.property)
  let f := G ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm
  have hc : R.chartCenter q = Bracket.σ w.val.val := R.chartCenter_finite q v hp
  have hf : ContDiffAt ℝ 2 f (Bracket.σ w.val.val) := by
    have hh := R.smooth_quotient_chart_pullback G hG q
    rw [hc] at hh
    exact hh.of_le Surface.two_le_infty
  change R.geometricJacobiAt G q = _
  rw [R.geometricJacobiAt_eq_diskJacobi, hc]
  change diskJacobi k f (Bracket.σ w.val.val) = _
  rw [← diskJacobi_comp_sigma h.out hw0 w.val.property hf]
  apply diskJacobi_congr
  have hg0 := R.centeredChart_scalar_pullback_germ G q
  rw [hc] at hg0
  have hg := hg0.comp_tendsto (Bracket.continuousAt_σ hw0).tendsto
  have hl := R.lowerParameterLift_finite_germ q w.val v hw0 rfl hp
  have hs : parameterSeamReflection h.out (HeightLift.projection q) = finiteParameter w.val := by
    rw [R.oddDiskPoint_projection, parameterSeamReflection_involutive]
  have he := (R.lowerSeam_glue_germ G j q w.val
    (R.oddDiskPoint_mem_lower_interior j w hw) hs).trans (glue_interior_germ _ _ hw)
  filter_upwards [hg, hl, he] with z hz hzl hze
  change f (Bracket.σ z) = _
  change G (HeightLift.periodQuotientMap m ((HeightLift.liftChart R.hC q).symm (Bracket.σ z))) =
    f (Bracket.σ z) at hz
  simp only [Function.comp_apply] at hzl
  rw [← hz, ← hzl]
  exact hze

lemma geometricJacobi_oddCopy_zero
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ZMod m) (w : PuncturedClosedDisk k) (hw : w.val.val = 0) :
    R.geometricJacobi G (R.oddPeriodPoint m j.val w) =
      diskJacobi k (encodeDiskFunction (R.diskFunctionPullback G) (oddCopyIndex j)) 0 := by
  let q := R.oddDiskPoint j.val w
  let x := R.oddPeriodPoint m j.val w
  let e := HeightLift.periodChart R.hC m x
  let u := encodeDiskFunction (R.diskFunctionPullback G) (oddCopyIndex j)
  have hw' : w.val = (⟨0, zero_not_puncture h.out⟩ : PuncturedPlane k) := Subtype.ext hw
  have hp : HeightLift.projection q = infinityParameter k := by
    rw [R.oddDiskPoint_projection, hw', parameterSeamReflection_zero]
  have hx : x ∈ R.quotientCopyInterior (oddCopyIndex j) :=
    ⟨w, by simp [hw], R.orderedDiskPoint_odd j w⟩
  have hec : e x = 0 := by
    change HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q) x = 0
    rw [R.periodChart_infinity_on_odd j q hp x hx]
    rw [show x = R.orderedDiskPoint (oddCopyIndex j) w from (R.orderedDiskPoint_odd j w).symm,
      R.diskCoordinate_orderedDiskPoint, hw, map_zero]
  have ht : (0 : ℂ) ∈ e.target := hec ▸ e.map_source (HeightLift.periodChart_mem R.hC m x)
  have he0 : e.symm 0 = x := by
    rw [← hec]
    exact e.left_inv (HeightLift.periodChart_mem R.hC m x)
  have hsupport : ∀ᶠ z in 𝓝 (0 : ℂ), e.symm z ∈ R.quotientCopyInterior (oddCopyIndex j) := by
    apply (e.continuousAt_symm ht).preimage_mem_nhds
    rw [he0]
    exact (R.isOpen_quotientCopyInterior _).mem_nhds hx
  have hg : G ∘ e.symm =ᶠ[𝓝 (0 : ℂ)] u ∘ (starRingEnd ℂ) := by
    filter_upwards [hsupport, e.open_target.mem_nhds ht] with z hz hzt
    have hc := R.periodChart_infinity_on_odd j q hp (e.symm z) hz
    have hi := e.right_inv hzt
    change e (e.symm z) = _ at hc
    rw [hi] at hc
    obtain ⟨v, hv, he⟩ := hz
    rw [← he, R.diskCoordinate_orderedDiskPoint] at hc
    have hzv : (starRingEnd ℂ) z = v.val.val := by rw [hc]; simp
    change G (e.symm z) = u ((starRingEnd ℂ) z)
    rw [hzv]
    dsimp only [u]
    rw [encodeDiskFunction_on_disk]
    exact congrArg G he.symm
  change R.geometricJacobiAt G q = _
  rw [R.geometricJacobiAt_eq_diskJacobi, R.chartCenter_infinity q hp]
  change diskJacobi k (G ∘ e.symm) 0 = _
  rw [diskJacobi_congr hg, diskJacobi_comp_conj, map_zero]

/-- Exact operator identity on every ordered open disk, including its center. -/
lemma geometricJacobi_orderedCopy
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hG : letI := HeightLift.periodChartedSpace R.hC m;
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G)
    (n : ZMod (2*m)) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) :
    R.geometricJacobi G (R.orderedDiskPoint n w) =
      diskJacobi k (encodeDiskFunction (R.diskFunctionPullback G) n) w.val.val := by
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · rw [R.orderedDiskPoint_even]
    simpa using R.geometricJacobi_evenCopy G (j.val : ℤ) w hw
  · rw [R.orderedDiskPoint_odd]
    by_cases h0 : w.val.val = 0
    · simpa only [h0] using R.geometricJacobi_oddCopy_zero G j w h0
    · simpa using R.geometricJacobi_oddCopy_nonzero G hG (j.val : ℤ) w hw h0

/-- The paper's disk equation is precisely the restriction of the actual
geometric equation to all open disk copies. Seam extension is a separate step. -/
lemma encoding_isJacobiField_iff_openCopies
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hG : letI := HeightLift.periodChartedSpace R.hC m;
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G) :
    Surface.IsJacobiField k m (encodeDiskFunction (R.diskFunctionPullback G)) ↔
      ∀ n (w : PuncturedClosedDisk k), ‖w.val.val‖ < 1 →
        R.geometricJacobi G (R.orderedDiskPoint n w) = 0 := by
  constructor
  · intro hJ n w hw
    rw [R.geometricJacobi_orderedCopy G hG n w hw]
    simpa only [diskJacobi, Complex.ofReal_pow] using
      hJ n w.val.val (by simpa [Surface.disk, Metric.mem_ball, dist_zero_right] using hw)
  · intro hJ n z hz
    have hn : ‖z‖ < 1 := by simpa [Surface.disk, Metric.mem_ball, dist_zero_right] using hz
    let w : PuncturedClosedDisk k := ⟨⟨z, Surface.punctures_notMem_disk (by have hk := h.out; omega) hz⟩, hn.le⟩
    have hh := hJ n w hn
    rw [R.geometricJacobi_orderedCopy G hG n w hn] at hh
    simpa only [diskJacobi, Complex.ofReal_pow] using hh

end PaperHalfPeriodRealization
end KsIndex.KarcherData
