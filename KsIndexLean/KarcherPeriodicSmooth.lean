module

public import KsIndexLean.KarcherPeriodicSupport
public import KsIndexLean.KarcherAreaLiftAgreement

@[expose] public section


/-! Smooth descent between the height lift and its period quotient. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} [TopologicalSpace P] [ChartedSpace ℂ P]
variable {F : P → PeriodTarget} (hF : Continuous F)

lemma periodicFunctionEquiv_contMDiffAt_iff (m : ℕ)
    (g : PeriodQuotient F m → ℂ) (q : HeightLift F) :
    letI := liftChartedSpace hF
    letI := periodChartedSpace hF m
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (periodicFunctionEquiv m g).val q ↔
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g (periodQuotientMap m q) := by
  let := liftChartedSpace hF
  let := periodChartedSpace hF m
  rw [contMDiffAt_iff_source, contMDiffAt_iff_source]
  simp only [mfld_simps]
  change ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (g ∘ periodQuotientMap m ∘ (liftChart hF q).symm) Set.univ
      (liftChart hF q q) ↔
    ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (g ∘ (periodChart hF m (periodQuotientMap m q)).symm) Set.univ
      (periodChart hF m (periodQuotientMap m q) (periodQuotientMap m q))
  rw [contMDiffWithinAt_univ, contMDiffWithinAt_univ, liftChart_apply, periodChart_apply]
  have he : (g ∘ periodQuotientMap m ∘ (liftChart hF q).symm) =ᶠ[
      𝓝 (chartAt ℂ (projection q) (projection q))]
      (g ∘ (periodChart hF m (periodQuotientMap m q)).symm) := by
    filter_upwards [periodChart_symm_lift_germ hF m q] with z hz
    exact congrArg g hz
  exact ⟨fun h => h.congr_of_eventuallyEq he.symm,
    fun h => h.congr_of_eventuallyEq he⟩

lemma periodicFunctionEquiv_contMDiff_iff (m : ℕ)
    (g : PeriodQuotient F m → ℂ) :
    letI := liftChartedSpace hF
    letI := periodChartedSpace hF m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (periodicFunctionEquiv m g).val ↔
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g := by
  let := liftChartedSpace hF
  let := periodChartedSpace hF m
  constructor
  · intro hg x
    obtain ⟨q, rfl⟩ := (periodQuotientMap_isQuotientMap (F := F) m).surjective x
    exact (periodicFunctionEquiv_contMDiffAt_iff hF m g q).mp (hg q)
  · intro hg q
    exact (periodicFunctionEquiv_contMDiffAt_iff hF m g q).mpr (hg _)

/-- Smooth compactly supported quotient tests correspond to smooth periodic
lift tests whose support is compact modulo the period subgroup. -/
lemma periodicFunctionEquiv_testDomain_iff (m : ℕ)
    (g : PeriodQuotient F m → ℂ) :
    letI := liftChartedSpace hF
    letI := periodChartedSpace hF m
    (ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (periodicFunctionEquiv m g).val ∧
      HasCompactSupportModulo m (periodicFunctionEquiv m g).val) ↔
    (ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g ∧ HasCompactSupport g) := by
  let := liftChartedSpace hF
  let := periodChartedSpace hF m
  exact and_congr (periodicFunctionEquiv_contMDiff_iff hF m g)
    (periodicFunctionEquiv_compactSupport_iff m g)

end KsIndex.KarcherData.HeightLift
#print axioms KsIndex.KarcherData.HeightLift.periodicFunctionEquiv_contMDiff_iff
#print axioms KsIndex.KarcherData.HeightLift.periodicFunctionEquiv_testDomain_iff
