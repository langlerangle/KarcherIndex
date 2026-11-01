module

public import KsIndexLean.PhasePairGlobalSeams

@[expose] public section


open Set Filter Topology Metric
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

lemma seam_support_excludes_puncture {k a : ℕ} {f : ℂ → ℂ}
    (hk : 1 ≤ k)
    (hs : tsupport f ⊆ seamDomain (boundaryArc k a) (isOpen_boundaryArc k a))
    {p : ℂ} (hp : p ∈ KsIndex.Surface.punctures k) : p ∉ tsupport f := by
  intro hf
  have hn := KsIndex.JacobiFamily.punctures_norm_eq_one hk hp
  let w : Circle₁ := ⟨p, mem_sphere_zero_iff_norm.mpr hn⟩
  have hm := (mem_seamDomain_iff (isOpen_boundaryArc k a) p).mp (hs hf)
  have hw : w ∈ boundaryArc k a := hm.2 w rfl
  exact KsIndex.JacobiFamily.arc_notMem_punctures hw hp

/-- Finitely many support exclusions give a common positive hole radius for
both representatives. The radius is allowed to depend on the approximant. -/
lemma finite_pair_zero_holes (P : Finset ℂ) (f g : ℂ → ℂ)
    (hf : ∀ p ∈ P, p ∉ tsupport f) (hg : ∀ p ∈ P, p ∉ tsupport g) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ P, ∀ z, dist z p < δ → f z = 0 ∧ g z = 0 := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert p P hp ih =>
    have he := (notMem_tsupport_iff_eventuallyEq.mp (hf p (Finset.mem_insert_self p P))).and
      (notMem_tsupport_iff_eventuallyEq.mp (hg p (Finset.mem_insert_self p P)))
    obtain ⟨r, hr, hzero⟩ := Metric.eventually_nhds_iff.mp he
    obtain ⟨s, hs, hs0⟩ := ih (fun q hq => hf q (Finset.mem_insert_of_mem hq))
      (fun q hq => hg q (Finset.mem_insert_of_mem hq))
    refine ⟨min r s, lt_min hr hs, ?_⟩
    intro q hq z hz
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hzero (lt_of_lt_of_le hz (min_le_left _ _))
    · exact hs0 q hq z (lt_of_lt_of_le hz (min_le_right _ _))

lemma finite_sum_support_exclusion {ι : Type*} (t : Finset ι) (f₀ : ℂ → ℂ)
    (f : ι → ℂ → ℂ) {p : ℂ} (h₀ : p ∉ tsupport f₀)
    (hf : ∀ i ∈ t, p ∉ tsupport (f i)) :
    p ∉ tsupport (fun z => f₀ z + ∑ i ∈ t, f i z) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  have hall : ∀ᶠ z in 𝓝 p, ∀ i ∈ t, f i z = 0 :=
    (eventually_all_finset t).mpr (fun i hi => notMem_tsupport_iff_eventuallyEq.mp (hf i hi))
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp h₀, hall] with z hz hi
  simp [hz, Finset.sum_eq_zero hi]

/-- Each assembled pair admits ONE positive radius avoiding every puncture
on both disks. This is the support requirement needed for cyclic CcSmooth. -/
theorem finite_phase_pair_puncture_holes {ι : Type*} (t : Finset ι) {k : ℕ} (hk : 1 ≤ k)
    (a : ι → ℕ) (c : ℕ → ℂ) (f g : ι → ℂ → ℂ) (f₀ g₀ : ℂ → ℂ)
    (hp : ∀ i ∈ t, SmoothSeamPair k (a i) (c (a i)) (f i) (g i))
    (hf₀ : tsupport f₀ ⊆ (disk : Set ℂ)) (hg₀ : tsupport g₀ ⊆ (disk : Set ℂ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ KsIndex.Surface.punctures k, ∀ z, ‖z - p‖ < δ →
      (f₀ z + ∑ i ∈ t, f i z) = 0 ∧ (g₀ z + ∑ i ∈ t, g i z) = 0 := by
  have hout p (h : p ∈ KsIndex.Surface.punctures k) : p ∉ (disk : Set ℂ) := by
    intro hd
    have hn := KsIndex.SurfaceForm.mem_disk_iff.mp hd
    rw [KsIndex.JacobiFamily.punctures_norm_eq_one hk h] at hn
    exact (lt_irrefl 1) hn
  obtain ⟨δ, hδ, hz⟩ := finite_pair_zero_holes (KsIndex.PunctureCutoff.pF k)
    (fun z => f₀ z + ∑ i ∈ t, f i z) (fun z => g₀ z + ∑ i ∈ t, g i z)
    (fun p h => finite_sum_support_exclusion t f₀ f
      (fun hh => hout p ((KsIndex.PunctureCutoff.mem_pF hk).mp h) (hf₀ hh))
      (fun i hi => seam_support_excludes_puncture hk (hp i hi).2.2.2.2.1
        ((KsIndex.PunctureCutoff.mem_pF hk).mp h)))
    (fun p h => finite_sum_support_exclusion t g₀ g
      (fun hh => hout p ((KsIndex.PunctureCutoff.mem_pF hk).mp h) (hg₀ hh))
      (fun i hi => seam_support_excludes_puncture hk (hp i hi).2.2.2.2.2.1
        ((KsIndex.PunctureCutoff.mem_pF hk).mp h)))
  refine ⟨δ, hδ, ?_⟩
  intro p hp z hd
  exact hz p ((KsIndex.PunctureCutoff.mem_pF hk).mpr hp) z (by simpa [dist_eq_norm] using hd)

end KsIndex.Trace
