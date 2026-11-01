module

public import KsIndexLean.GeneralDiskClassical
public import KsIndexLean.WeakSmoothGluing
public import KsIndexLean.PaperSlitTestTransport
public import KsIndexLean.SurfacePotentialFacts
public import KsIndexLean.DiskSmoothRepresentative

@[expose] public section


/-! Interior regularity for actual paper slit-character radical vectors.
Both weak-equation and coefficient hypotheses are discharged. This is an
interior result; seam gluing and the global smooth carrier are separate steps. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Weq
open KsIndex.WeakH1

lemma memLp_potV_three_real (u : RealH1) :
    MemLp (fun z => Surface.potV 3 z * TauCeti.W1p.value u z) 2
      (volume.restrict (disk : Set ℂ)) :=
  memLp_potV_general_real (by decide) u

theorem exists_smooth_near_of_disk_weakSol (u : RealH1)
    (he : PunctureRemoval.IsWeakSolOn (Surface.potV 3) disk u)
    {z : ℂ} (hz : z ∈ (disk : Set ℂ)) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ (disk : Set ℂ) ∧ ∃ g : ℂ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧
      (TauCeti.W1p.value u : ℂ → ℝ) =ᵐ[volume.restrict (Metric.ball z r)] g :=
  exists_smooth_near_of_general_disk_weakSol (by decide) u he hz

theorem exists_smooth_near_of_disk_complex_weakSol (u : ComplexH1)
    (hr : PunctureRemoval.IsWeakSolOn (Surface.potV 3) disk (rePart u))
    (hi : PunctureRemoval.IsWeakSolOn (Surface.potV 3) disk (imPart u))
    {z : ℂ} (hz : z ∈ (disk : Set ℂ)) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ (disk : Set ℂ) ∧ ∃ g : ℂ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧
      value u =ᵐ[volume.restrict (Metric.ball z r)] g :=
  exists_smooth_near_of_general_disk_complex_weakSol (by decide) u hr hi hz

end KsIndex.Weq

namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1 KsIndex.PaperSlitAdapter

/-- Every upper hemisphere component of a paper pair-radical vector has a
smooth local representative at each interior point, without regularity assumptions. -/
theorem pair_radical_smooth_near_fst {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    {z : ℂ} (hz : z ∈ (disk : Set ℂ)) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ (disk : Set ℂ) ∧ ∃ g : ℂ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧
      value u.val.1 =ᵐ[volume.restrict (Metric.ball z r)] g := by
  apply Weq.exists_smooth_near_of_disk_complex_weakSol u.val.1 ?_ ?_ hz
  · intro φ hφ hc hs
    exact (pair_radical_D1_fst u hrad φ hφ hc hs).1
  · intro φ hφ hc hs
    exact (pair_radical_D1_fst u hrad φ hφ hc hs).2

/-- The lower hemisphere has the same actual interior regularity. -/
theorem pair_radical_smooth_near_snd {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    {z : ℂ} (hz : z ∈ (disk : Set ℂ)) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ (disk : Set ℂ) ∧ ∃ g : ℂ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧
      value u.val.2 =ᵐ[volume.restrict (Metric.ball z r)] g := by
  apply Weq.exists_smooth_near_of_disk_complex_weakSol u.val.2 ?_ ?_ hz
  · intro φ hφ hc hs
    exact (pair_radical_D1_snd u hrad φ hφ hc hs).1
  · intro φ hφ hc hs
    exact (pair_radical_D1_snd u hrad φ hφ hc hs).2

/-- Both actual radical components admit single smooth representatives on their
whole open disks. This asserts neither seam regularity nor the classical PDE yet. -/
theorem pair_radical_smooth_representatives {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0) :
    ∃ f g : ℂ → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) f (disk : Set ℂ) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) g (disk : Set ℂ) ∧
      valueCLM u.val.1 =ᵐ[volume.restrict (disk : Set ℂ)] f ∧
      valueCLM u.val.2 =ᵐ[volume.restrict (disk : Set ℂ)] g := by
  obtain ⟨f, hf, ha⟩ := Weq.exists_contDiffOn_ae_of_smooth_near
    (fun z hz => pair_radical_smooth_near_fst u hrad hz)
  obtain ⟨g, hg, hb⟩ := Weq.exists_contDiffOn_ae_of_smooth_near
    (fun z hz => pair_radical_smooth_near_snd u hrad hz)
  exact ⟨f, g, hf, hg, (valueLp_ae u.val.1).trans ha, (valueLp_ae u.val.2).trans hb⟩

end KsIndex.PaperSlitTransport
