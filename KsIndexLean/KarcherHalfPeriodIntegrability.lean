module

public import KsIndexLean.NaturalCoreIntegrability
public import KsIndexLean.KarcherNeumannTestSpace
public import KsIndexLean.KarcherDirichletIndex

@[expose] public section


/-! Finite area integrals for the actual compact half-period test fields. -/
noncomputable section
open Set MeasureTheory
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SingleDisk
namespace KsIndex.KarcherData
open scoped QuotientArea HalfPeriodArea
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma integrable_halfPeriodArea_coordinate_iff (R : PaperHalfPeriodRealization k)
    (F : ℂ → ℝ) :
    Integrable (fun q => F (R.diskHomeomorph q).val.val) R.halfPeriodArea ↔
      IntegrableOn (fun z => rho k z^2 * F z) disk := by
  have he := (measurableEmbedding_puncturedClosedDisk_coe.comp
    R.diskHomeomorph.measurableEmbedding).integrable_map_iff
      (μ := R.halfPeriodArea) (g := F)
  simp only [Function.comp_def] at he
  rw [R.map_halfPeriodArea_coordinate] at he
  rw [← he,ewAreaMeasure,restrict_withDensity (s := disk)
    (show MeasurableSet disk from measurableSet_ball),
    integrable_withDensity_iff_integrable_smul'
      ((measurable_rho k).pow_const 2).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]
  rfl

theorem halfPeriod_integrable_of_nat (R : PaperHalfPeriodRealization k)
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ} {b1 b0 : Bool}
    (hf : R.halfPeriodCoordinate f ∈ NatCc k b1 b0) :
    Integrable (R.halfPeriodGradSq f) R.halfPeriodArea ∧
      Integrable (fun q => (R.halfPeriodAbsA q * ‖f q‖)^2) R.halfPeriodArea := by
  obtain ⟨hd,hp⟩ := Trace.natCc_integrable_conformal_densities h.out hf
  constructor
  · change Integrable (fun q => R.halfPeriodGradSq f q) R.halfPeriodArea
    simp_rw [halfPeriodGradSq_eq]
    apply (R.integrable_halfPeriodArea_coordinate_iff (fun z =>
      (rho k z^2)⁻¹ * gradSq (R.halfPeriodCoordinate f) z)).mpr
    convert hd using 1
    funext z
    ring
  · have he : ∀ q, R.halfPeriodCoordinate f (R.diskHomeomorph q).val.val = f q := by
      intro q
      exact (R.halfPeriodCoordinate_apply f (R.diskHomeomorph q)).trans
        (congrArg f (R.diskHomeomorph.symm_apply_apply q))
    simp_rw [halfPeriodAbsA_eq,← he]
    apply (R.integrable_halfPeriodArea_coordinate_iff (fun z =>
      (absA k z * ‖R.halfPeriodCoordinate f z‖)^2)).mpr
    convert hp using 1
    funext z
    ring

theorem neumannTest_integrable (R : PaperHalfPeriodRealization k)
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ} (hf : R.IsNeumannTest f) :
    Integrable (R.halfPeriodGradSq f) R.halfPeriodArea ∧
      Integrable (fun q => (R.halfPeriodAbsA q * ‖f q‖)^2) R.halfPeriodArea :=
  R.halfPeriod_integrable_of_nat (R.neumannTest_to_nat hf)

lemma openHalfPeriodExtension_coordinate (R : PaperHalfPeriodRealization k)
    (f : R.OpenHalfPeriod → ℂ) :
    R.halfPeriodCoordinate (R.openHalfPeriodExtension f) = R.openHalfPeriodCoordinate f := by
  funext z
  by_cases hz : ‖z‖ ≤ 1 ∧ z ∉ punctures k
  · exact R.halfPeriodCoordinate_ofCoordinate _ hz.1 hz.2
  · have hd : z ∉ disk := by
      intro hd
      exact hz ⟨(mem_disk_iff.mp hd).le,
        punctures_notMem_disk (k := k) (by have := h.out; omega) hd⟩
    simp only [halfPeriodCoordinate,dite_eq_right hz,openHalfPeriodCoordinate,
      zeroExtendSet,dite_eq_right hd]

theorem dirichletTest_integrable (R : PaperHalfPeriodRealization k)
    {f : R.OpenHalfPeriod → ℂ} (hf : f ∈ R.dirichletTests) :
    Integrable (R.halfPeriodGradSq (R.openHalfPeriodExtension f)) R.halfPeriodArea ∧
      Integrable (fun q => (R.halfPeriodAbsA q * ‖R.openHalfPeriodExtension f q‖)^2)
        R.halfPeriodArea := by
  apply R.halfPeriod_integrable_of_nat (b1 := false) (b0 := false)
  rw [R.openHalfPeriodExtension_coordinate]
  exact hf

end PaperHalfPeriodRealization
end KsIndex.KarcherData
