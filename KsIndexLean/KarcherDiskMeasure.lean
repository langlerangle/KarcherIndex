module

public import KsIndexLean.KarcherChartArea

@[expose] public section


/-! # Area measure in the EW disk coordinate

The conformal density defines a measure on the plane and, by pullback, on the
closed disk with the punctures removed. The disk boundary has zero area.
`KarcherQuotientArea` assembles the ordered copies into a Borel measure on the
period quotient; local compatibility with the immersion's induced area is
proved in the subsequent area-chart modules.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace KsIndex.KarcherData
variable {k : ℕ}

/-- Canonical (subtype = Borel-of-subspace, since `ℂ` is a `BorelSpace`) measurable structure on the
puncture-complement; the geometry layer set up only the topology. -/
instance : MeasurableSpace (PuncturedPlane k) := Subtype.instMeasurableSpace
/-- Canonical measurable structure on the closed-disk-minus-punctures subtype. -/
instance : MeasurableSpace (PuncturedClosedDisk k) := Subtype.instMeasurableSpace

/-- The nested-subtype coercion `PuncturedClosedDisk k → ℂ` is a measurable embedding: both
`w ∉ punctures k` (complement of the closed puncture set) and `‖w‖ ≤ 1` cut out measurable sets. -/
lemma measurableEmbedding_puncturedClosedDisk_coe :
    MeasurableEmbedding (fun w : PuncturedClosedDisk k => (w.val.val : ℂ)) := by
  have hpp : MeasurableEmbedding (Subtype.val : PuncturedPlane k → ℂ) :=
    MeasurableEmbedding.subtype_coe
      (isClosed_eq (continuous_id.pow (2 * k)) continuous_const).measurableSet.compl
  have hball : MeasurableSet {w : PuncturedPlane k | ‖w.val‖ ≤ 1} :=
    measurableSet_le (continuous_norm.comp continuous_subtype_val).measurable measurable_const
  exact hpp.comp (MeasurableEmbedding.subtype_coe hball)

/-- The EW area measure pulled back to the closed-disk-minus-punctures subtype. Since the seam
boundary `‖w‖ = 1` is `ewAreaMeasure`-null (`ewAreaMeasure_unitCircle_null`), this is the
disk-interior EW area measure in the disk coordinate. -/
def ewDiskMeasure (k : ℕ) : Measure (PuncturedClosedDisk k) :=
  (ewAreaMeasure k).comap (fun w => w.val.val)

/-- `ρ_k` is measurable (continuous numerator and denominator-norm; division is measurable even
where the denominator vanishes, at the punctures). -/
lemma measurable_rho (k : ℕ) : Measurable (Surface.rho k) := by
  unfold Surface.rho
  fun_prop

/-- Integration against the EW area measure is integration against planar volume
with weight `ρ_k²`. This identity applies to measurable nonnegative extended-real
functions on the plane and supplies the weighted integrals used in the copywise forms. -/
lemma lintegral_ewAreaMeasure {k : ℕ} {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ w, F w ∂(ewAreaMeasure k) = ∫⁻ w, ENNReal.ofReal (Surface.rho k w ^ 2) * F w ∂volume := by
  rw [show ewAreaMeasure k
        = volume.withDensity (fun w => ENNReal.ofReal (Surface.rho k w ^ 2)) from rfl,
    lintegral_withDensity_eq_lintegral_mul _ ((measurable_rho k).pow_const 2).ennreal_ofReal hF]
  rfl

end KsIndex.KarcherData
