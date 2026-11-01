module

public import KsIndexLean.KarcherJacobiEquivalence
public import KsIndexLean.SingleDisk

@[expose] public section


/-! Variational index and bounded-field nullity on the actual EW quotient. -/
noncomputable section
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)
local instance invariantQuotientCharted : ChartedSpace ℂ
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :=
  HeightLift.periodChartedSpace R.hC m

/-- Actual compactly supported smooth complex test functions. -/
def compactSmoothDomain : Submodule ℂ
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) where
  carrier := {f | ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f}
  zero_mem' := ⟨contMDiff_const, by simp [HasCompactSupport]⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    have hc : ContDiff ℝ ∞ (fun z : ℂ => c * z) := contDiff_const.mul contDiff_id
    exact ⟨hc.contMDiff.comp hf.1, (show HasCompactSupport f from hf.2).smul_left⟩

/-- Variational index of the intrinsic geometric form, using complex test spaces. -/
def geometricIndex : ℕ∞ := FormIndex.formIndex R.quotientJacobiQ (R.compactSmoothDomain (m := m))

/-- Complex dimension of bounded smooth geometric Jacobi fields. -/
def geometricNullity : ℕ∞ := Cardinal.toENat (Module.rank ℂ (R.boundedGeometricJacobi (m := m)))

lemma geometricNullity_eq_model : R.geometricNullity (m := m) = Surface.nulSurface k m := by
  unfold geometricNullity Surface.nulSurface
  rw [R.geometricJacobiEquiv.rank_eq]

lemma geometricIndex_eq_model : R.geometricIndex (m := m) = Surface.indSurface k m := by
  let L := R.modelTestFunction.comp (Surface.uncurryE m).symm.toLinearMap
  have hmap : ∀ u ∈ (Surface.CcSmooth k m).map (Surface.uncurryE m).toLinearMap,
      L u ∈ R.compactSmoothDomain := by
    rintro _ ⟨u, hu, rfl⟩
    exact R.modelTestFunction_compactSmooth ⟨u, hu⟩
  have hsurj : ∀ f ∈ R.compactSmoothDomain (m := m),
      ∃ u ∈ (Surface.CcSmooth k m).map (Surface.uncurryE m).toLinearMap, L u = f := by
    intro f hf
    obtain ⟨u, he⟩ := R.modelTestFunction_surjective_compactSmooth f hf.1 hf.2
    exact ⟨Surface.uncurryE m u.val, ⟨u.val, u.property, rfl⟩, he⟩
  have hform : ∀ u ∈ (Surface.CcSmooth k m).map (Surface.uncurryE m).toLinearMap,
      Surface.jacobiQ k m ((Surface.uncurryE m).symm u) = R.quotientJacobiQ (L u) := by
    rintro _ ⟨u, hu, rfl⟩
    have hs := R.modelTestFunction_compactSmooth ⟨u, hu⟩
    change Surface.jacobiQ k m u = R.quotientJacobiQ (R.modelTestFunction u)
    rw [R.compactSmooth_quotientJacobiQ_eq_model _ hs.1 hs.2, R.modelTestFunction_modelForm]
  have h0 : R.quotientJacobiQ (0 : HeightLift.PeriodQuotient
      (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) = 0 := by
    have hz : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (0 : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) := contMDiff_const
    rw [R.compactSmooth_quotientJacobiQ_eq_model 0 hz (by simp [HasCompactSupport])]
    have he : encodeDiskFunction (R.diskFunctionPullback
        (0 : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)) = 0 := by
      funext n z
      dsimp only [encodeDiskFunction]
      split_ifs <;> rfl
    rw [he]
    simp [Surface.jacobiQ, Surface.gradSq, Surface.dirichletG, Surface.potentialG]
  exact (FormIndex.formIndex_transport_surj L hmap hsurj hform h0).symm

end KsIndex.KarcherData.PaperHalfPeriodRealization
