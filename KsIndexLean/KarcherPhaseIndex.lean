module

public import KsIndexLean.KarcherSlitIndex
public import KsIndexLean.SurfacePhaseDecomposition

@[expose] public section


/-! Index decomposition on the actual quotient inside one translation phase. -/
noncomputable section
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.SurfaceForm KsIndex.FormIndex
variable {m : ℕ} [h : Fact (2 ≤ 3)] [NeZero m] (R : PaperHalfPeriodRealization 3)
local instance phaseQuotientCharted : ChartedSpace ℂ
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint 3) R.C) m) :=
  HeightLift.periodChartedSpace R.hC m

/-- Compact smooth tests on the quotient with a fixed translation character. -/
def geometricSmoothPhase (n : ℕ) :=
  (Dom 3 m ⊓ Module.End.eigenspace (shiftE m) (zeta m ^ n)).map
    (R.geometricTestDescent (m := m))

lemma mem_geometricSmoothPhase (n : ℕ) (f : HeightLift.PeriodQuotient
    (extendedEWMap h.out (reflectionBasepoint 3) R.C) m → ℂ) :
    f ∈ R.geometricSmoothPhase (m := m) n ↔
      (ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f) ∧
      (∀ q, f (HeightLift.periodDeck m 1 q) = zeta m ^ n * f q) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    let v : CcSmooth 3 m := ⟨(uncurryE m).symm u, mem_Dom.mp hu.1⟩
    refine ⟨R.modelTestFunction_compactSmooth v, ?_⟩
    apply (R.translation_eigenvalue_iff _ _).mpr
    change ∀ a z, shiftF (encodeDiskFunction (R.diskFunctionPullback
      (R.modelTestFunction v.val))) a z = zeta m ^ n *
      encodeDiskFunction (R.diskFunctionPullback (R.modelTestFunction v.val)) a z
    rw [R.modelTestFunction_encoding]
    apply FaithfulInjection.testTrace_shift_character
    intro a z
    exact congrFun (Module.End.mem_eigenspace_iff.mp hu.2) (a,z)
  · rintro ⟨hf, ht⟩
    let v : CcSmooth 3 m := ⟨encodeDiskFunction (R.diskFunctionPullback f),
      (R.compactSmooth_iff_encoding_mem_CcSmooth f).mp hf⟩
    refine ⟨uncurryE m v.val, ⟨?_, ?_⟩, ?_⟩
    · exact ⟨v.val, v.property, rfl⟩
    · apply Module.End.mem_eigenspace_iff.mpr
      exact funext (fun p => (R.translation_eigenvalue_iff f _).mp ht p.1 p.2)
    · exact R.modelTestFunction_encoding_section f

lemma geometricSmoothPhase_index_eq_model (n : ℕ) :
    formIndex R.quotientJacobiQ (R.geometricSmoothPhase (m := m) n) =
      formIndex (Qs 3 m) (Dom 3 m ⊓ Module.End.eigenspace (shiftE m) (zeta m ^ n)) := by
  let D := Dom 3 m ⊓ Module.End.eigenspace (shiftE m) (zeta m ^ n)
  have hmap : ∀ u ∈ D,
      R.geometricTestDescent u ∈ R.geometricSmoothPhase (m := m) n :=
    fun u hu => ⟨u, hu, rfl⟩
  have hsurj : ∀ f ∈ R.geometricSmoothPhase (m := m) n,
      ∃ u ∈ D, R.geometricTestDescent u = f := fun _ hf => hf
  have hform : ∀ u ∈ D, Qs 3 m u = R.quotientJacobiQ (R.geometricTestDescent u) := by
    intro u hu
    let v : CcSmooth 3 m := ⟨(uncurryE m).symm u, mem_Dom.mp hu.1⟩
    have hs := R.modelTestFunction_compactSmooth v
    change Surface.jacobiQ 3 m v.val = R.quotientJacobiQ (R.modelTestFunction v.val)
    rw [R.compactSmooth_quotientJacobiQ_eq_model _ hs.1 hs.2, R.modelTestFunction_modelForm]
  have hz := hform 0 (Submodule.zero_mem _)
  rw [map_zero] at hz
  have h0 : R.quotientJacobiQ (0 : HeightLift.PeriodQuotient
      (extendedEWMap h.out (reflectionBasepoint 3) R.C) m → ℂ) = 0 := by
    rw [← hz]
    simp [Qs, Surface.jacobiQ, Surface.gradSq, Surface.dirichletG, Surface.potentialG]
  exact (formIndex_transport_surj (R.geometricTestDescent (m := m)) hmap hsurj hform h0).symm

/-- A phase-only geometric index is the sum of its three rotation-character indices. -/
theorem geometricSmoothPhase_index_eq_sum_rotation (n : ℕ) :
    formIndex R.quotientJacobiQ (R.geometricSmoothPhase (m := m) n) =
      ∑ j : Fin 3, formIndex R.quotientJacobiQ
        (R.geometricSmoothJointSector (m := m) n j) := by
  rw [R.geometricSmoothPhase_index_eq_model, phase_index_eq_sum_rotation (by omega)]
  apply Finset.sum_congr rfl
  intro j _
  exact (R.geometricSmoothJointSector_index_eq_model n j).symm

end KsIndex.KarcherData.PaperHalfPeriodRealization
