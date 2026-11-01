module

public import KsIndexLean.PhasePairPunctureSupport
public import KsIndexLean.TwistedPair

@[expose] public section


open Set Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

/-- One-period copy order: lower is copy zero, upper is copy one. -/
def smoothPairCopies (f g : ℂ → ℂ) (n : ZMod (2 * 1)) : ℂ → ℂ :=
  if n = 0 then closedDiskRestriction g else closedDiskRestriction f

lemma smoothPairCopies_twistedCc {k : ℕ} (c : ℂ) {f g : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h1 : ∀ p ∈ KsIndex.Surface.arc k 1,
      ContDiffAt ℝ ∞ (phaseGerm 1 (closedDiskRestriction g) (closedDiskRestriction f)) p)
    (h0 : ∀ p ∈ KsIndex.Surface.arc k 0,
      ContDiffAt ℝ ∞ (phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g)) p)
    (hP : ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ KsIndex.Surface.punctures k, ∀ z, ‖z - p‖ < δ →
      f z = 0 ∧ g z = 0) :
    smoothPairCopies f g ∈ KsIndex.Twisted.TwistedCc k c := by
  have he0 : KsIndex.Surface.glue (smoothPairCopies f g) 0 =
      phaseGerm 1 (closedDiskRestriction g) (closedDiskRestriction f) := by
    funext z
    simp [KsIndex.Surface.glue, smoothPairCopies, phaseGerm, σ]
  have he1 : KsIndex.Twisted.glueTw c (smoothPairCopies f g) =
      phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g) := by
    funext z
    simp [KsIndex.Twisted.glueTw, smoothPairCopies, phaseGerm, σ]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n
    unfold smoothPairCopies
    split_ifs
    · exact closedDiskRestriction_smoothOn hg
    · exact closedDiskRestriction_smoothOn hf
  · intro p hp
    rw [he0]
    exact h1 p (by simpa only [KsIndex.Twisted.seamArc_one_zero] using hp)
  · intro p hp
    rw [he1]
    exact h0 p (by simpa only [KsIndex.Twisted.seamArc_one_one] using hp)
  · intro n z hz
    by_cases hn : n = 0 <;> simp [smoothPairCopies, hn, closedDiskRestriction, not_le.mpr hz]
  · obtain ⟨δ, hδ, hzero⟩ := hP
    refine ⟨δ, hδ, ?_⟩
    intro n z hz
    obtain ⟨p, hp, hzp⟩ := hz
    obtain ⟨hF, hG⟩ := hzero p hp z hzp
    by_cases hn : n = 0 <;> simp [smoothPairCopies, hn, closedDiskRestriction, hF, hG]

/-- Extend a smooth pair with the stated seam conditions and puncture holes
into the cyclic `CcSmooth` space. The relation `c ^ m = 1` closes the last seam. -/
theorem smoothPairCopies_cyclic {k m : ℕ} [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    {f g : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h1 : ∀ p ∈ KsIndex.Surface.arc k 1,
      ContDiffAt ℝ ∞ (phaseGerm 1 (closedDiskRestriction g) (closedDiskRestriction f)) p)
    (h0 : ∀ p ∈ KsIndex.Surface.arc k 0,
      ContDiffAt ℝ ∞ (phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g)) p)
    (hP : ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ KsIndex.Surface.punctures k, ∀ z, ‖z - p‖ < δ →
      f z = 0 ∧ g z = 0) :
    KsIndex.Twisted.extF m c (smoothPairCopies f g) ∈ KsIndex.Surface.CcSmooth k m :=
  KsIndex.Twisted.extF_mem hc (smoothPairCopies_twistedCc c hf hg h1 h0 hP)

/-- Reconstruct the cyclic smooth function from exactly the local data
retained by the punctured partition theorem. -/
theorem finite_phase_pair_cyclic {ι : Type*} (t : Finset ι) {k m : ℕ}
    (hk : 1 ≤ k) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (a : ι → ℕ) (phase : ℕ → ℂ) (hphase0 : phase 0 = c) (hphase1 : phase 1 = 1)
    (f g : ι → ℂ → ℂ) (f₀ g₀ : ℂ → ℂ)
    (ha : ∀ i ∈ t, a i = 0 ∨ a i = 1)
    (hp : ∀ i ∈ t, SmoothSeamPair k (a i) (phase (a i)) (f i) (g i))
    (hf₀ : tsupport f₀ ⊆ (disk : Set ℂ)) (hg₀ : tsupport g₀ ⊆ (disk : Set ℂ))
    (hF : ContDiff ℝ ∞ (fun z => f₀ z + ∑ i ∈ t, f i z))
    (hG : ContDiff ℝ ∞ (fun z => g₀ z + ∑ i ∈ t, g i z)) :
    KsIndex.Twisted.extF m c (smoothPairCopies
      (fun z => f₀ z + ∑ i ∈ t, f i z) (fun z => g₀ z + ∑ i ∈ t, g i z))
      ∈ KsIndex.Surface.CcSmooth k m := by
  apply smoothPairCopies_cyclic c hc hF hG
  · intro p hpt
    have h := finite_phase_pair_global_seams t k a (fun b => (phase b)⁻¹)
      g f g₀ f₀ ha (fun i hi => (hp i hi).swap) hg₀ hf₀ (Or.inr rfl) hpt
    simpa only [hphase1, inv_one] using h
  · intro p hpt
    simpa only [hphase0] using
      finite_phase_pair_global_seams t k a phase f g f₀ g₀ ha hp hf₀ hg₀ (Or.inl rfl) hpt
  · exact finite_phase_pair_puncture_holes t hk a phase f g f₀ g₀ hp hf₀ hg₀

end KsIndex.Trace
