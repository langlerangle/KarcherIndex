module

public import KsIndexLean.SlitGaugeTransitions
public import KsIndexLean.Bracket

@[expose] public section


open Set MeasureTheory TopologicalSpace

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma isClosed_planarSlit (k : ℕ) : IsClosed (KsIndex.Bracket.slit k) := by
  change IsClosed ({z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | (z ^ k).re ≤ 0})
  exact (isClosed_eq continuous_norm continuous_const).inter
    (isClosed_le (by fun_prop) continuous_const)

/-- The planar slit complement restricted to the seam collar. -/
def slitAnnulus (k : ℕ) : Opens ℂ :=
  ⟨annulusSet (1 / 2 : ℝ) 2 \ KsIndex.Bracket.slit k,
    (annulusOpens (1 / 2) 2).isOpen.sdiff (isClosed_planarSlit k)⟩

lemma ordinary_seam_eq_slitAnnulus (k : ℕ) :
    seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) = slitAnnulus k := by
  ext z
  change z ∈ seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) ↔ z ∈ slitAnnulus k
  rw [mem_seamDomain_iff]
  change (_ ∧ ∀ w : Circle₁, (w : ℂ) = z → w ∈ boundaryArc k 1) ↔
    _ ∧ ¬ (‖z‖ = 1 ∧ (z ^ k).re ≤ 0)
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, ?_⟩
    rintro ⟨hn, hre⟩
    let w : Circle₁ := ⟨z, by simpa using hn⟩
    have hw := h w rfl
    simp only [mem_boundaryArc, pow_one, neg_one_mul] at hw
    change -(z ^ k).re < 0 at hw
    linarith
  · rintro ⟨hz, h⟩
    refine ⟨hz, ?_⟩
    intro w hw
    have hn : ‖z‖ = 1 := hw ▸ mem_sphere_zero_iff_norm.mp w.property
    have hre : 0 < (z ^ k).re := lt_of_not_ge (fun he => h ⟨hn, he⟩)
    simp only [mem_boundaryArc, pow_one, neg_one_mul, hw]
    linarith

/-- Ordinary weak gluing on the planar slit complement within the seam collar. -/
theorem slitAnnulus_weak (k : ℕ) (c : ℂ) (p : slitTraceDomain k c) :
    TauCeti.HasWeakFDerivOn volume (slitAnnulus k)
      (joinedDiskValue p.val.1 p.val.2 1) (joinedDiskJet p.val.1 p.val.2 1) := by
  rw [← ordinary_seam_eq_slitAnnulus]
  exact slitTrace_ordinary_weak k c p

lemma slitAnnulus_value_memLp (k : ℕ) (u v : ComplexH1) :
    MemLp (joinedDiskValue u v 1) 2 (volume.restrict (slitAnnulus k : Set ℂ)) := by
  rw [← ordinary_seam_eq_slitAnnulus]
  exact seamDomain_value_memLp _ u v 1

lemma slitAnnulus_jet_memLp (k : ℕ) (u v : ComplexH1) :
    MemLp (joinedDiskJet u v 1) 2 (volume.restrict (slitAnnulus k : Set ℂ)) := by
  rw [← ordinary_seam_eq_slitAnnulus]
  exact seamDomain_jet_memLp _ u v 1

end KsIndex.Trace
