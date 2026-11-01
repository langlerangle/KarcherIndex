module

public import KsIndexLean.SeamDomainWeakGluing
public import KsIndexLean.WeakTransmissionDomains

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma isOpen_boundaryArc (k n : ℕ) : IsOpen (boundaryArc k n) := by
  have h : boundaryArc k n = {w : Circle₁ | (-1 : ℝ) ^ n * ((w : ℂ) ^ k).re < 0} :=
    Set.ext (mem_boundaryArc k n)
  rw [h]
  exact isOpen_lt (by fun_prop) continuous_const

lemma boundaryArc_disjoint (k : ℕ) : Disjoint (boundaryArc k 0) (boundaryArc k 1) := by
  rw [Set.disjoint_left]
  intro w h0 h1
  simp only [mem_boundaryArc, pow_zero, one_mul, pow_one, neg_one_mul] at h0 h1
  linarith

lemma boundaryArc_union (k : ℕ) (w : Circle₁) :
    w ∈ boundaryArc k 0 ∪ boundaryArc k 1 ↔ ((w : ℂ) ^ k).re ≠ 0 := by
  simp only [mem_union, mem_boundaryArc, pow_zero, one_mul, pow_one, neg_one_mul]
  constructor
  · rintro (h | h) <;> linarith
  · intro h
    rcases lt_or_gt_of_ne h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)

lemma mem_seamDomain_iff {A : Set Circle₁} (hA : IsOpen A) (z : ℂ) :
    z ∈ seamDomain A hA ↔ z ∈ annulusSet (1 / 2 : ℝ) 2 ∧
      ∀ w : Circle₁, (w : ℂ) = z → w ∈ A := by
  constructor
  · intro hz
    refine ⟨hz.1, ?_⟩
    intro w hw
    by_contra hn
    exact hz.2 ⟨w, hn, hw⟩
  · rintro ⟨hz, h⟩
    refine ⟨hz, ?_⟩
    rintro ⟨w, hw, he⟩
    exact hw (h w he)

/-- The two gauge domains overlap only off the middle circle. -/
lemma slit_seam_overlap (k : ℕ) (z : ℂ) :
    z ∈ seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0) ∧
      z ∈ seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) ↔
    z ∈ annulusSet (1 / 2 : ℝ) 2 ∧ ‖z‖ ≠ 1 := by
  simp only [mem_seamDomain_iff]
  constructor
  · rintro ⟨⟨hz, h0⟩, ⟨_, h1⟩⟩
    refine ⟨hz, ?_⟩
    intro hn
    let w : Circle₁ := ⟨z, by simpa using hn⟩
    exact Set.disjoint_left.mp (boundaryArc_disjoint k) (h0 w rfl) (h1 w rfl)
  · rintro ⟨hz, hn⟩
    have he : ∀ w : Circle₁, (w : ℂ) ≠ z := by
      intro w hw
      apply hn
      rw [← hw]
      exact mem_sphere_zero_iff_norm.mp w.property
    exact ⟨⟨hz, fun w hw => (he w hw).elim⟩, ⟨hz, fun w hw => (he w hw).elim⟩⟩

/-- Ordinary gluing on the unslit arcs, for the actual ordered transmission pair. -/
theorem slitTrace_ordinary_weak (k : ℕ) (c : ℂ) (p : slitTraceDomain k c) :
    TauCeti.HasWeakFDerivOn volume
      (seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1))
      (joinedDiskValue p.val.1 p.val.2 1) (joinedDiskJet p.val.1 p.val.2 1) := by
  apply seamDomain_weak_gluing
  simpa using ((mem_slitTraceDomain k c p.val).mp p.property).1

/-- Scalar-adjusted extension across the slit arcs, used for local smoothing.
The scalar may be any complex number, including zero. -/
theorem slitTrace_phase_weak (k : ℕ) (c : ℂ) (p : slitTraceDomain k c) :
    TauCeti.HasWeakFDerivOn volume
      (seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0))
      (joinedDiskValue p.val.1 p.val.2 c) (joinedDiskJet p.val.1 p.val.2 c) :=
  seamDomain_weak_gluing _ _ _ _ ((mem_slitTraceDomain k c p.val).mp p.property).2

lemma joinedDiskValue_inner_transition (u v : ComplexH1) (c : ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    joinedDiskValue u v c z = joinedDiskValue u v 1 z := by
  simp [joinedDiskValue, radialJoin, hz]

lemma joinedDiskValue_outer_transition (u v : ComplexH1) (c : ℂ) {z : ℂ} (hz : 1 < ‖z‖) :
    joinedDiskValue u v c z = c • joinedDiskValue u v 1 z := by
  simp [joinedDiskValue, radialJoin, not_le.mpr hz]

end KsIndex.Trace
