module

public import KsIndexLean.SeamCutoff

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped ContDiff Topology

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

def joinedDiskJet (u v : ComplexH1) (c : ℂ) : ℂ → ℂ →L[ℝ] ℂ :=
  reconstructedJet (joinedDiskRadial u v c) (joinedDiskAngular u v c)

lemma memLp_joinedDiskJet (u v : ComplexH1) (c : ℂ) :
    MemLp (joinedDiskJet u v c) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) :=
  memLp_reconstructedJet (by norm_num) (memLp_joinedDiskRadial u v c)
    (memLp_joinedDiskAngular u v c)

lemma cutoffDiskJet_eq_of_coefficients {η : ℂ → ℝ} (u v : ComplexH1) (c : ℂ) {z : ℂ}
    (h1 : η (nUnit z) = 1) (h0 : angularTestDeriv η (nUnit z) = 0) :
    reconstructedJet (cutoffDiskRadial η u v c) (cutoffDiskAngular η u v c) z =
      joinedDiskJet u v c z := by
  have hr : cutoffDiskRadial η u v c z = joinedDiskRadial u v c z := by
    simp only [cutoffDiskRadial, angularCutoffField, h1, one_smul]
  have hq : cutoffDiskAngular η u v c z = joinedDiskAngular u v c z := by
    simp only [cutoffDiskAngular, angularCutoffField, h1, h0, one_smul, zero_smul, add_zero]
  simp only [joinedDiskJet, reconstructedJet, reconstructedX, reconstructedY, hr, hq]

lemma cutoffDisk_eventually_eq_uncut {η : ℂ → ℝ} {w : Circle₁}
    (h : η =ᶠ[𝓝 (w : ℂ)] (fun _ => 1)) (u v : ComplexH1) (c : ℂ) :
    ∀ᶠ z in 𝓝 (w : ℂ), cutoffDiskValue η u v c z = joinedDiskValue u v c z ∧
      reconstructedJet (cutoffDiskRadial η u v c) (cutoffDiskAngular η u v c) z =
        joinedDiskJet u v c z := by
  filter_upwards [cutoff_coefficients_near_circle h] with z hz
  refine ⟨?_, cutoffDiskJet_eq_of_coefficients u v c hz.1 hz.2⟩
  simp only [cutoffDiskValue, angularCutoffField, hz.1, one_smul]

/-- The uncut field is weakly differentiable near each interior matching seam point. -/
theorem local_uncut_disk_gluing {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (hm : arcTrace A u = c • arcTrace A v)
    {w : Circle₁} (hw : w ∈ A) :
    ∃ Ω : Opens ℂ, (w : ℂ) ∈ Ω ∧ Ω ≤ annulusOpens (1 / 2) 2 ∧
      TauCeti.HasWeakFDerivOn volume Ω (joinedDiskValue u v c) (joinedDiskJet u v c) := by
  obtain ⟨η, hη, hηA, hηw⟩ := exists_seam_cutoff hA hw
  have he := cutoffDisk_eventually_eq_uncut hηw u v c
  obtain ⟨s, hs, hso, hws⟩ := eventually_nhds_iff.mp he
  let Ω : Opens ℂ := ⟨s ∩ annulusSet (1 / 2 : ℝ) 2,
    hso.inter (annulusOpens (1 / 2) 2).isOpen⟩
  have hΩ : Ω ≤ annulusOpens (1 / 2) 2 := fun _ hz => hz.2
  have hwa : (w : ℂ) ∈ annulusSet (1 / 2 : ℝ) 2 := by
    constructor <;> norm_num
  refine ⟨Ω, ⟨hws, hwa⟩, hΩ, ?_⟩
  have hg := (cutoffDisk_weak_reconstruction hA.measurableSet hη hηA u v c hm).mono hΩ
  have hv : cutoffDiskValue η u v c =ᵐ[volume.restrict (Ω : Set ℂ)] joinedDiskValue u v c := by
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with z hz
    exact (hs z hz.1).1
  have hj : reconstructedJet (cutoffDiskRadial η u v c) (cutoffDiskAngular η u v c)
      =ᵐ[volume.restrict (Ω : Set ℂ)] joinedDiskJet u v c := by
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with z hz
    exact (hs z hz.1).2
  exact (hg.congr_ae hv).congr_ae_deriv hj

end KsIndex.Trace
