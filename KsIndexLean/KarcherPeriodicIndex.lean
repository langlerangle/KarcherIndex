module

public import KsIndexLean.KarcherPeriodicNullity

@[expose] public section


/-! The Jacobi form over one period of the lifted EW surface. -/
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- The `2m` lifted disks representing one m-period cell, in the paper's order. -/
def periodicDiskPoint (n : ZMod (2 * m)) (w : PuncturedClosedDisk k) :
    PeriodicEWCarrier h.out (reflectionBasepoint k) R.C :=
  if n.val % 2 = 0 then R.evenDiskPoint (n.val / 2 : ℕ) w
  else R.oddDiskPoint (n.val / 2 : ℕ) w

omit [NeZero m] in
lemma periodicDiskPoint_projects (n : ZMod (2 * m)) (w : PuncturedClosedDisk k) :
    HeightLift.periodQuotientMap m (R.periodicDiskPoint n w) = R.orderedDiskPoint n w := by
  unfold periodicDiskPoint orderedDiskPoint
  split_ifs <;> rfl

open scoped Classical in
/-- Disk-coordinate restriction to one period, zero outside the actual disk. -/
def periodicEncoding (f : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ℂ)
    (n : ZMod (2 * m)) (w : ℂ) : ℂ :=
  if hw : w ∉ Surface.punctures k ∧ ‖w‖ ≤ 1 then
    f (R.periodicDiskPoint n ⟨⟨w,hw.1⟩,hw.2⟩) else 0

lemma periodicEncoding_pullback
    (g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    R.periodicEncoding (R.periodicPullback g) = encodeDiskFunction (R.diskFunctionPullback g) := by
  funext n w
  dsimp only [periodicEncoding, encodeDiskFunction]
  split_ifs
  · change g (HeightLift.periodQuotientMap m (R.periodicDiskPoint n _)) =
      g (R.orderedDiskPoint n _)
    exact congrArg g (R.periodicDiskPoint_projects n _)
  · rfl

/-- Signed per-period geometric energy, with no averaging by the period length.
Finiteness on the smooth test domain follows from quotient transport below. -/
def periodicJacobiQ (f : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ℂ) : ℝ :=
  (∑ n : ZMod (2*m), ∫⁻ w, ENNReal.ofReal ((Surface.rho k w ^ 2)⁻¹ *
    Surface.gradSq (R.periodicEncoding f n) w) ∂(ewAreaMeasure k)).toReal -
  (∑ n : ZMod (2*m), ∫⁻ w, ENNReal.ofReal (Surface.absA k w ^ 2 *
    ‖R.periodicEncoding f n w‖ ^ 2) ∂(ewAreaMeasure k)).toReal

lemma periodicJacobiQ_pullback_copywise
    (g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    R.periodicJacobiQ (m := m) (R.periodicPullback g) = R.ewJacobiQ g := by
  unfold periodicJacobiQ
  rw [R.periodicEncoding_pullback]
  rfl

lemma periodicJacobiQ_pullback
    (g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hg : g ∈ R.compactSmoothDomain) :
    R.periodicJacobiQ (m := m) (R.periodicPullback g) = R.quotientJacobiQ g := by
  rw [R.periodicJacobiQ_pullback_copywise,
    R.compactSmooth_quotientJacobiQ_eq_copywise g hg.1 hg.2]

/-- Smooth periodic tests with support compact modulo the deck subgroup. -/
def periodicTestDomain : Submodule ℂ
    (PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ℂ) :=
  R.compactSmoothDomain.map (R.periodicPullback (m := m))

omit [NeZero m] in
lemma mem_periodicTestDomain
    (f : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ℂ) :
    letI := HeightLift.liftChartedSpace R.hC
    f ∈ R.periodicTestDomain (m := m) ↔
      f ∈ HeightLift.periodicFunctions m ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HeightLift.HasCompactSupportModulo m f := by
  let := HeightLift.liftChartedSpace R.hC
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact ⟨(HeightLift.periodicFunctionEquiv m g).property,
      (HeightLift.periodicFunctionEquiv_testDomain_iff R.hC m g).mpr hg⟩
  · rintro ⟨hp,hs,hc⟩
    let fp : HeightLift.periodicFunctions
        (F := extendedEWMap h.out (reflectionBasepoint k) R.C) m := ⟨f,hp⟩
    let g := (HeightLift.periodicFunctionEquiv m).symm fp
    have he : R.periodicPullback g = f :=
      congrArg Subtype.val ((HeightLift.periodicFunctionEquiv m).apply_symm_apply fp)
    refine ⟨g, ?_, he⟩
    apply (HeightLift.periodicFunctionEquiv_testDomain_iff R.hC m g).mp
    change ContMDiff _ _ ∞ (R.periodicPullback g) ∧ _
    rw [he]
    exact ⟨hs,hc⟩

/-- Both nonnegative energies are finite on periodic smooth tests. -/
lemma periodicTest_energy_lt_top
    (f : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ℂ)
    (hf : f ∈ R.periodicTestDomain (m := m)) :
    (∑ n : ZMod (2*m), ∫⁻ w, ENNReal.ofReal ((Surface.rho k w ^ 2)⁻¹ *
      Surface.gradSq (R.periodicEncoding f n) w) ∂(ewAreaMeasure k)) < ⊤ ∧
    (∑ n : ZMod (2*m), ∫⁻ w, ENNReal.ofReal (Surface.absA k w ^ 2 *
      ‖R.periodicEncoding f n w‖ ^ 2) ∂(ewAreaMeasure k)) < ⊤ := by
  obtain ⟨g,hg,rfl⟩ := hf
  rw [R.periodicEncoding_pullback]
  exact R.compactSmooth_energy_lt_top g hg.1 hg.2

/-- Index computed over one period of the infinite lift. -/
def periodicIndex : ℕ∞ :=
  FormIndex.formIndex (R.periodicJacobiQ (m := m)) (R.periodicTestDomain (m := m))

lemma periodicJacobiQ_zero : R.periodicJacobiQ (m := m) 0 = 0 := by
  have he : R.periodicEncoding (m := m) 0 = 0 := by
    funext n w
    simp [periodicEncoding]
  simp [periodicJacobiQ, he, Surface.gradSq]

lemma periodicIndex_eq_geometricIndex :
    R.periodicIndex (m := m) = R.geometricIndex (m := m) := by
  symm
  apply FormIndex.formIndex_transport_surj R.periodicPullback
  · intro g hg
    exact ⟨g,hg,rfl⟩
  · rintro f ⟨g,hg,rfl⟩
    exact ⟨g,hg,rfl⟩
  · intro g hg
    exact (R.periodicJacobiQ_pullback g hg).symm
  · exact R.periodicJacobiQ_zero

lemma periodicIndex_eq_model : R.periodicIndex (m := m) = Surface.indSurface k m := by
  rw [R.periodicIndex_eq_geometricIndex, R.geometricIndex_eq_model]

end KsIndex.KarcherData.PaperHalfPeriodRealization
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.periodicJacobiQ_pullback
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.mem_periodicTestDomain
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.periodicIndex_eq_model

#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.periodicTest_energy_lt_top
