module

public import KsIndexLean.KarcherPeriodicJacobi
public import KsIndexLean.KarcherGeometricInvariants

@[expose] public section


/-! Nullity under periodic deformations of the infinite EW lift. -/
noncomputable section
open scoped KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- Linear pullback from the period quotient to the infinite height lift. -/
def periodicPullback :
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) →ₗ[ℂ]
      (PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ℂ) :=
  (HeightLift.periodicFunctions m).subtype.comp
    (HeightLift.periodicFunctionEquiv m).toLinearMap

lemma periodicPullback_injective : Function.Injective (R.periodicPullback (m := m)) :=
  Subtype.val_injective.comp (HeightLift.periodicFunctionEquiv m).injective

/-- The image space is characterized below by the intrinsic periodic Jacobi conditions. -/
def boundedPeriodicJacobi : Submodule ℂ
    (PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ℂ) :=
  (R.boundedGeometricJacobi (m := m)).map R.periodicPullback

lemma mem_boundedPeriodicJacobi
    (f : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ℂ) :
    f ∈ R.boundedPeriodicJacobi (m := m) ↔ R.IsBoundedPeriodicJacobi (m := m) f := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (R.boundedPeriodicJacobi_pullback_iff g).mpr hg
  · intro hf
    let fp : HeightLift.periodicFunctions
        (F := extendedEWMap h.out (reflectionBasepoint k) R.C) m :=
      ⟨f, hf.1⟩
    let g := (HeightLift.periodicFunctionEquiv m).symm fp
    have he : R.periodicPullback g = f :=
      congrArg Subtype.val ((HeightLift.periodicFunctionEquiv m).apply_symm_apply fp)
    refine ⟨g, ?_, he⟩
    apply (R.boundedPeriodicJacobi_pullback_iff g).mp
    change R.IsBoundedPeriodicJacobi (R.periodicPullback g)
    rw [he]
    exact hf

/-- Complex dimension of bounded smooth periodic Jacobi fields on the lift. -/
def periodicNullity : ℕ∞ :=
  Cardinal.toENat (Module.rank ℂ (R.boundedPeriodicJacobi (m := m)))

lemma periodicNullity_eq_geometricNullity [NeZero m] :
    R.periodicNullity (m := m) = R.geometricNullity (m := m) := by
  unfold periodicNullity geometricNullity boundedPeriodicJacobi
  rw [rank_map_eq R.periodicPullback_injective]

lemma periodicNullity_eq_model [NeZero m] :
    R.periodicNullity (m := m) = Surface.nulSurface k m := by
  rw [R.periodicNullity_eq_geometricNullity, R.geometricNullity_eq_model]

end KsIndex.KarcherData.PaperHalfPeriodRealization
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.mem_boundedPeriodicJacobi
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.periodicNullity_eq_geometricNullity
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.periodicNullity_eq_model
