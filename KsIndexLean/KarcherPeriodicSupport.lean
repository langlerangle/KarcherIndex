module

public import KsIndexLean.KarcherPeriodicFunctions
public import KsIndexLean.KarcherPeriodQuotientCharts
public import Mathlib.Topology.Algebra.Support

@[expose] public section


/-! Continuity and compact support modulo vertical periods. -/
noncomputable section
open Set
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} [TopologicalSpace P] {F : P → PeriodTarget}

lemma periodicFunctionEquiv_continuous_iff (m : ℕ) (g : PeriodQuotient F m → ℂ) :
    Continuous (periodicFunctionEquiv m g).val ↔ Continuous g := by
  exact (periodQuotientMap_isQuotientMap (F := F) m).continuous_iff.symm

/-- Topological support pulls back exactly under the open period quotient map. -/
lemma periodicFunctionEquiv_tsupport (m : ℕ) (g : PeriodQuotient F m → ℂ) :
    tsupport (periodicFunctionEquiv m g).val =
      periodQuotientMap m ⁻¹' tsupport g := by
  change closure (Function.support (g ∘ periodQuotientMap m)) =
    periodQuotientMap m ⁻¹' closure (Function.support g)
  rw [Function.support_comp_eq_preimage]
  exact ((periodQuotientMap_isOpenMap m).preimage_closure_eq_closure_preimage
    (periodQuotientMap_isQuotientMap m).continuous _).symm

/-- Compactness modulo periods means compactness of the image of the support. -/
def HasCompactSupportModulo (m : ℕ) (f : HeightLift F → ℂ) : Prop :=
  IsCompact (periodQuotientMap m '' tsupport f)

lemma periodicFunctionEquiv_compactSupport_iff (m : ℕ) (g : PeriodQuotient F m → ℂ) :
    HasCompactSupportModulo m (periodicFunctionEquiv m g).val ↔ HasCompactSupport g := by
  unfold HasCompactSupportModulo
  rw [periodicFunctionEquiv_tsupport,
    Set.image_preimage_eq _ (periodQuotientMap_isQuotientMap m).surjective]
  rfl

end KsIndex.KarcherData.HeightLift
#print axioms KsIndex.KarcherData.HeightLift.periodicFunctionEquiv_tsupport
#print axioms KsIndex.KarcherData.HeightLift.periodicFunctionEquiv_compactSupport_iff
