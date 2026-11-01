module

public import KsIndexLean.InteriorPartitionRemainder
public import KsIndexLean.WeakH1Localization
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

@[expose] public section


open Set Filter Topology MeasureTheory Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- A smooth disk-supported cutoff equal to one on any closed set inside the disk. -/
theorem exists_disk_support_cutoff {K : Set ℂ} (hK : IsClosed K) (hs : K ⊆ disk) :
    ∃ η : ℂ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ disk ∧ EqOn η 1 K := by
  obtain ⟨r, hr, hsub⟩ := exists_pos_lt_subset_ball (by norm_num : (0 : ℝ) < 1) hK hs
  let η : ContDiffBump (0 : ℂ) := ⟨r, (r + 1) / 2, hr.1, by linarith [hr.2]⟩
  refine ⟨η, η.contDiff, η.hasCompactSupport, ?_, ?_⟩
  · rw [η.tsupport_eq]
    exact closedBall_subset_ball (by change (r + 1) / 2 < 1; linarith [hr.2])
  · intro z hz
    exact η.one_of_mem_closedBall (ball_subset_closedBall (hsub hz))

/-- Replace the value-level remainder by an actual smooth localization of the original carrier. -/
theorem interior_remainder_localizer (u : ComplexH1) {a : ℂ → ℝ}
    (ha : ContDiff ℝ ∞ a) {v : ℂ → ℂ} (hs : tsupport v ⊆ disk)
    (hv : v =ᵐ[volume.restrict disk] (fun z => (1 - a z) • valueCLM u z)) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ disk ∧
      (fun z => χ z • valueCLM u z) =ᵐ[volume.restrict disk] v := by
  obtain ⟨η, hη, hc, hsd, he⟩ := exists_disk_support_cutoff isClosed_closure hs
  let χ : ℂ → ℝ := fun z => η z * (1 - a z)
  refine ⟨χ, hη.mul (contDiff_const.sub ha), hc.mul_right,
    tsupport_mul_subset_left.trans hsd, ?_⟩
  filter_upwards [hv] with z hz
  have heta : η z • v z = v z := by
    by_cases hm : z ∈ tsupport v
    · rw [he hm]
      exact one_smul ℝ (v z)
    · rw [image_eq_zero_of_notMem_tsupport hm, smul_zero]
  change (η z * (1 - a z)) • valueCLM u z = v z
  rw [mul_smul, ← hz]
  exact heta

/-- The interior partition remainder has a genuine whole-plane weak H1 representative. -/
theorem interior_remainder_weak (u : ComplexH1) {H : Set ℂ} (hH : IsOpen H)
    {a : ℂ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hu : ∀ᵐ z ∂volume.restrict disk, z ∈ H → valueCLM u z = 0)
    (hb : ∀ p : ℂ, ‖p‖ = 1 → p ∉ H → a =ᶠ[𝓝 p] 1) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ disk ∧
      (fun z => χ z • valueCLM u z) =ᵐ[volume.restrict disk]
        (fun z => (1 - a z) • valueCLM u z) ∧
      TauCeti.HasWeakFDerivOn volume ⊤ (fun z => χ z • valueCLM u z)
        (fun z => χ z • Dxy (dxLp u) (dyLp u) z +
          (fderiv ℝ χ z).smulRight (valueCLM u z)) ∧
      MemLp (fun z => χ z • valueCLM u z) 2 volume ∧
      ∀ d, MemLp (fun z => (χ z • Dxy (dxLp u) (dyLp u) z +
        (fderiv ℝ χ z).smulRight (valueCLM u z)) d) 2 volume := by
  obtain ⟨v, _, hs, hv⟩ := exists_interior_remainder_rep hH hu hb
  obtain ⟨χ, hχ, hc, hsd, he⟩ := interior_remainder_localizer u ha hs hv
  exact ⟨χ, hχ, hc, hsd, he.trans hv, diskH1_localization u hχ hc hsd⟩

end KsIndex.Trace
