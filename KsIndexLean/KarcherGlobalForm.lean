module

public import KsIndexLean.KarcherDiskForm
public import KsIndexLean.KarcherDiskEncoding
public import KsIndexLean.KarcherDiskFunctions

@[expose] public section


/-! # Disk-coordinate Dirichlet and potential energies of quotient functions

Each energy is the sum over the `2m` ordered disk copies of the integrals of
`encodeDiskFunction (diskFunctionPullback G)`. There is no averaging factor.
The weighted expressions use inverse-metric or curvature densities against
`ewAreaMeasure`; the flat expressions use the corresponding model densities
against volume. `KarcherDiskForm` identifies them copy by copy.

The `_Geom_eq_flat` theorems establish these weighted-to-flat equalities in
disk coordinates. They do not by themselves identify the sums with intrinsic
area or energy on the quotient surface: that requires a separate transport
through the charts and their seams. The names `Geom` refer here to the
weighted disk expressions.

Both nonnegative energies are extended-real `lintegral`s. This module does
not form their signed difference or assert the integrability needed for a
real-valued Jacobi form.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)
  (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)

/-- Flat (model) global Dirichlet energy: `Σ over the 2m copies` of the flat gradient-square
integral of the copy's canonical encoding. -/
def ewDirichletEnergyFlat : ℝ≥0∞ :=
  ∑ n : ZMod (2 * m), ∫⁻ w, ENNReal.ofReal
    (Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n) w) ∂volume

/-- Weighted disk-coordinate Dirichlet energy: the inverse-metric gradient
density integrated against the EW area measure, summed over the copies. -/
def ewDirichletEnergyGeom : ℝ≥0∞ :=
  ∑ n : ZMod (2 * m), ∫⁻ w,
    ENNReal.ofReal ((Surface.rho k w ^ 2)⁻¹ *
      Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n) w) ∂(ewAreaMeasure k)

/-- Equality of weighted and flat disk-coordinate Dirichlet energies.
This holds for arbitrary `G`, using measurability of the totalized derivative.
It does not itself identify the sums with intrinsic quotient energy. -/
lemma ewDirichletEnergyGeom_eq_flat :
    ewDirichletEnergyGeom R G = ewDirichletEnergyFlat R G :=
  Finset.sum_congr rfl fun _ _ =>
    lintegral_ewAreaMeasure_invMetricGradSq h.out _

/-- Flat (model) global potential energy: `Σ over the 2m copies` of `∫ potV·|encoding|² d(vol)`. -/
def ewPotentialEnergyFlat : ℝ≥0∞ :=
  ∑ n : ZMod (2 * m), ∫⁻ w,
    ENNReal.ofReal (Surface.potV k w *
      ‖encodeDiskFunction (R.diskFunctionPullback G) n w‖ ^ 2) ∂volume

/-- Weighted disk-coordinate potential energy: the sum over the `2m` copies
of `∫ |A|²·|encoding|² d(ewAreaMeasure)`. -/
def ewPotentialEnergyGeom : ℝ≥0∞ :=
  ∑ n : ZMod (2 * m), ∫⁻ w,
    ENNReal.ofReal (Surface.absA k w ^ 2 *
      ‖encodeDiskFunction (R.diskFunctionPullback G) n w‖ ^ 2) ∂(ewAreaMeasure k)

/-- For a continuous quotient function `G`, the squared encoding is measurable: on the (measurable)
disk set the encoding is `G ∘ orderedDiskPoint` (both continuous) read in the disk subtype, and `0`
off it (`Measurable.dite`). Discharges the potential-energy measurability from `Continuous G`. -/
lemma measurable_encodeSq (hG : Continuous G) (n : ZMod (2 * m)) :
    Measurable (fun w => ‖encodeDiskFunction (R.diskFunctionPullback G) n w‖ ^ 2) := by
  classical
  have hs : MeasurableSet {w : ℂ | w ∉ Surface.punctures k ∧ ‖w‖ ≤ 1} :=
    ((isClosed_eq (continuous_id.pow (2 * k)) continuous_const).measurableSet.compl).inter
      (measurableSet_le continuous_norm.measurable measurable_const)
  have hf : Measurable (fun ws : {w : ℂ | w ∉ Surface.punctures k ∧ ‖w‖ ≤ 1} =>
      (R.diskFunctionPullback G).val (n, ⟨⟨ws.val, ws.property.1⟩, ws.property.2⟩)) :=
    (hG.comp ((R.continuous_orderedDiskPoint n).comp
      ((continuous_subtype_val.subtype_mk fun ws => ws.property.1).subtype_mk
        fun ws => ws.property.2))).measurable
  have henc : Measurable (encodeDiskFunction (R.diskFunctionPullback G) n) :=
    Measurable.dite hf (measurable_const (a := (0 : ℂ))) hs
  exact henc.norm.pow_const 2

/-- Equality of weighted and flat disk-coordinate potential energies.
Continuity of `G` supplies the required measurability of its squared encoding.
Intrinsic quotient-energy identification is a separate assertion. -/
lemma ewPotentialEnergyGeom_eq_flat (hG : Continuous G) :
    ewPotentialEnergyGeom R G = ewPotentialEnergyFlat R G :=
  Finset.sum_congr rfl fun n _ =>
    lintegral_ewAreaMeasure_potential h.out _ (R.measurable_encodeSq G hG n)

end KsIndex.KarcherData.PaperHalfPeriodRealization
