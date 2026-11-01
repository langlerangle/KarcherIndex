module

public import KsIndexLean.InteriorRemainderWeak
public import KsIndexLean.ReflectedWeakLocalization

@[expose] public section


open Set Filter Topology MeasureTheory
open scoped ContDiff BigOperators
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Inside the disk the joined value is the original weak carrier, for any phase. -/
lemma joined_value_on_disk (u v : ComplexH1) (s : ℂ) {z : ℂ} (hz : z ∈ disk) :
    joinedDiskValue u v s z = valueCLM u z := by
  simp only [joinedDiskValue, radialJoin,
    ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hz).le]

/-- The actual whole-plane interior localization and joined boundary pieces
reconstruct the original value on the disk. The interior jet is the genuine
product-rule jet; reconstruction of the sum of jets is a separate obligation. -/
theorem finite_weak_partition_values {ι : Type*} (t : Finset ι)
    (ρ : ι → ℂ → ℝ) (s : ι → ℂ) (u : ComplexH1)
    (hρ : ∀ i, ContDiff ℝ ∞ (ρ i)) {H : Set ℂ} (hH : IsOpen H)
    (hu : ∀ᵐ z ∂volume.restrict disk, z ∈ H → valueCLM u z = 0)
    (hb : ∀ p : ℂ, ‖p‖ = 1 → p ∉ H →
      (fun z => ∑ i ∈ t, ρ i z) =ᶠ[𝓝 p] 1) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ disk ∧
      (fun z => χ z • valueCLM u z +
        ∑ i ∈ t, ρ i z • joinedDiskValue u u (s i) z) =ᵐ[volume.restrict disk]
        (valueCLM u : ℂ → ℂ) ∧
      TauCeti.HasWeakFDerivOn volume ⊤ (fun z => χ z • valueCLM u z)
        (fun z => χ z • Dxy (dxLp u) (dyLp u) z +
          (fderiv ℝ χ z).smulRight (valueCLM u z)) ∧
      MemLp (fun z => χ z • valueCLM u z) 2 volume ∧
      ∀ d, MemLp (fun z => (χ z • Dxy (dxLp u) (dyLp u) z +
        (fderiv ℝ χ z).smulRight (valueCLM u z)) d) 2 volume := by
  have ha : ContDiff ℝ ∞ (fun z => ∑ i ∈ t, ρ i z) :=
    ContDiff.sum (fun i _ => hρ i)
  obtain ⟨χ, hχ, hc, hs, he, hw, hv, hJ⟩ := interior_remainder_weak u hH ha hu hb
  refine ⟨χ, hχ, hc, hs, ?_, hw, hv, hJ⟩
  filter_upwards [he, ae_restrict_mem KsIndex.SurfaceForm.measurableSet_disk] with z hz hzd
  simp only [joined_value_on_disk u u _ hzd]
  rw [hz, ← Finset.sum_smul, ← add_smul]
  simp

end KsIndex.Trace
