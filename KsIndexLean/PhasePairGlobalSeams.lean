module

public import KsIndexLean.SlitPairPartitionApproximation

@[expose] public section


open Set Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

/-- Two functions vanishing near a circle point have a zero phase germ there,
regardless of the phase used to glue them. -/
lemma restricted_phase_zero_germ (c : ℂ) {f g : ℂ → ℂ} {p : ℂ}
    (hp : ‖p‖ = 1) (hf : p ∉ tsupport f) (hg : p ∉ tsupport g) :
    ContDiffAt ℝ ∞ (phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g)) p := by
  have he : f =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hf
  have hj : g =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hg
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have ht : Tendsto σ (𝓝 p) (𝓝 p) := by
    simpa only [σ_self hp] using (continuousAt_σ hp0).tendsto
  have hzero : phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g)
      =ᶠ[𝓝 p] 0 := by
    filter_upwards [he, ht.eventually hj] with z hz hi
    simp [phaseGerm, closedDiskRestriction, hz, hi]
  exact contDiffAt_const.congr_of_eventuallyEq hzero

lemma restricted_phase_add (c : ℂ) (f g F G : ℂ → ℂ) :
    phaseGerm c (closedDiskRestriction (fun z => f z + F z))
      (closedDiskRestriction (fun z => g z + G z)) =
    fun z => phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g) z +
      phaseGerm c (closedDiskRestriction F) (closedDiskRestriction G) z := by
  funext z
  simp only [phaseGerm, closedDiskRestriction]
  split_ifs <;> simp_all [mul_add]

lemma restricted_phase_sum {ι : Type*} (t : Finset ι) (c : ℂ)
    (f g : ι → ℂ → ℂ) :
    phaseGerm c (closedDiskRestriction (fun z => ∑ i ∈ t, f i z))
      (closedDiskRestriction (fun z => ∑ i ∈ t, g i z)) =
    fun z => ∑ i ∈ t, phaseGerm c (closedDiskRestriction (f i)) (closedDiskRestriction (g i)) z := by
  funext z
  by_cases hz : ‖z‖ ≤ 1
  · simp [phaseGerm, closedDiskRestriction, hz]
  · by_cases hi : ‖σ z‖ ≤ 1
    · simp [phaseGerm, closedDiskRestriction, hz, hi, Finset.mul_sum]
    · simp [phaseGerm, closedDiskRestriction, hz, hi]

/-- Retain both orientations of the exact local seam construction. -/
lemma SmoothSeamPair.swap {k a : ℕ} {c : ℂ} {f g : ℂ → ℂ}
    (h : SmoothSeamPair k a c f g) : SmoothSeamPair k a c⁻¹ g f := by
  refine ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.2.2, ?_⟩
  simpa only [inv_inv] using h.2.2.2.2.2.2.1

/-- Each supported seam piece satisfies both global seam conditions: its own
phase identity applies on its seam, and its support excludes the other seam. -/
lemma SmoothSeamPair.germ_at {k a : ℕ} {c : ℕ → ℂ} {f g : ℂ → ℂ}
    (h : SmoothSeamPair k a (c a) f g) (ha : a = 0 ∨ a = 1)
    {b : ℕ} (hb : b = 0 ∨ b = 1) {p : ℂ} (hp : p ∈ KsIndex.Surface.arc k b) :
    ContDiffAt ℝ ∞ (phaseGerm (c b) (closedDiskRestriction f) (closedDiskRestriction g)) p := by
  by_cases hab : a = b
  · subst b
    rw [h.2.2.2.2.2.2.1]
    exact h.1.contDiffAt
  · have hd : Disjoint (boundaryArc k a) (boundaryArc k b) := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hab rfl).elim
      · exact boundaryArc_disjoint k
      · exact (boundaryArc_disjoint k).symm
      · exact (hab rfl).elim
    exact restricted_phase_zero_germ (c b) hp.1
      (seam_support_excludes_arc h.2.2.2.2.1 hd hp)
      (seam_support_excludes_arc h.2.2.2.2.2.1 hd hp)

/-- The finite sums, including independent interior pieces, satisfy the actual
smooth phase-germ condition on BOTH paper arcs. -/
theorem finite_phase_pair_global_seams {ι : Type*} (t : Finset ι) (k : ℕ)
    (a : ι → ℕ) (c : ℕ → ℂ) (f g : ι → ℂ → ℂ) (f₀ g₀ : ℂ → ℂ)
    (ha : ∀ i ∈ t, a i = 0 ∨ a i = 1)
    (hp : ∀ i ∈ t, SmoothSeamPair k (a i) (c (a i)) (f i) (g i))
    (hf₀ : tsupport f₀ ⊆ (disk : Set ℂ)) (hg₀ : tsupport g₀ ⊆ (disk : Set ℂ))
    {b : ℕ} (hb : b = 0 ∨ b = 1) {p : ℂ} (hpt : p ∈ KsIndex.Surface.arc k b) :
    ContDiffAt ℝ ∞ (phaseGerm (c b)
      (closedDiskRestriction (fun z => f₀ z + ∑ i ∈ t, f i z))
      (closedDiskRestriction (fun z => g₀ z + ∑ i ∈ t, g i z))) p := by
  have hnd : p ∉ (disk : Set ℂ) := by
    intro h
    have hh := KsIndex.SurfaceForm.mem_disk_iff.mp h
    rw [hpt.1] at hh
    exact (lt_irrefl 1) hh
  rw [restricted_phase_add, restricted_phase_sum]
  exact (restricted_phase_zero_germ (c b) hpt.1
    (fun h => hnd (hf₀ h)) (fun h => hnd (hg₀ h))).add
    (ContDiffAt.sum (fun i hi => (hp i hi).germ_at (ha i hi) hb hpt))

end KsIndex.Trace
