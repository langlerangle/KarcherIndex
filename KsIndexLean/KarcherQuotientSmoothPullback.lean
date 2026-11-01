module

public import KsIndexLean.KarcherPeriodProjectionSmooth

@[expose] public section


/-! Smooth pullback along continuous quotient maps with smooth parameter action. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} [TopologicalSpace P] [ChartedSpace ℂ P]
variable [IsManifold 𝓘(ℝ, ℂ) ∞ P]
variable {F : P → PeriodTarget} (hF : Continuous F) (m : ℕ)

lemma contMDiff_comp_of_parameter_action
    (a : PeriodQuotient F m → PeriodQuotient F m) (b : P → P)
    (ha : Continuous a) (hb : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ b)
    (hp : ∀ q, quotientProjection m (a q) = b (quotientProjection m q))
    (f : PeriodQuotient F m → ℂ) :
    letI := periodChartedSpace hF m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f →
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f ∘ a) := by
  letI := periodChartedSpace hF m
  intro hf q
  let e := (quotientProjection_isLocalHomeomorph hF m).localInverseAt (a q)
  have hf' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f ∘ e) (quotientProjection m (a q)) :=
    (contMDiffAt_iff_local_parameter hF m f (a q)).mp (hf (a q))
  rw [hp q] at hf'
  have hg := hf'.comp q ((hb.comp (quotientProjection_contMDiff hF m)) q)
  apply hg.congr_of_eventuallyEq
  have ht : ∀ᶠ r in 𝓝 q, a r ∈ e.target :=
    ha.continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds
        (quotientProjection_isLocalHomeomorph hF m).self_mem_localInverseAt_target)
  filter_upwards [ht] with r hr
  change f (a r) = f (e (b (quotientProjection m r)))
  rw [← hp r]
  have he : e (quotientProjection m (a r)) = a r := by
    simpa only [e, IsLocalHomeomorph.localInverseAt_symm] using e.right_inv hr
  rw [he]

end KsIndex.KarcherData.HeightLift
