module

public import KsIndexLean.SeamMollificationSupport
public import KsIndexLean.SingleDisk

@[expose] public section


/-!
# Compact seam support stays away from the closed slit

A compactly supported function living in arc-1's seam domain vanishes on a
uniform neighborhood of the CLOSED slit: the slit (`(w^k).re ≤ 0` on the
circle) and arc 1 (`(w^k).re > 0`) are disjoint by arithmetic — endpoints
included, no case analysis — and the positive radius follows from compactness of the support
inside the open complement of the slit.
-/

open Set MeasureTheory Filter Topology Metric
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk KsIndex.Surface

lemma isClosed_slit (k : ℕ) : IsClosed (Bracket.slit k) := by
  apply IsClosed.inter
  · exact isClosed_eq continuous_norm continuous_const
  · exact isClosed_le (Complex.continuous_re.comp (continuous_pow k))
      continuous_const

/-- The closed slit is disjoint from arc-1's seam domain: circle points of
the seam domain lie in the OPEN arc 1 (`(w^k).re > 0`), while slit points
have `(w^k).re ≤ 0` — endpoints included, uniformly. -/
lemma slit_notMem_seamDomain {k : ℕ} {p : ℂ} (hp : p ∈ Bracket.slit k) :
    p ∉ (seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) : Set ℂ) := by
  intro hmem
  have hm := (mem_seamDomain_iff (isOpen_boundaryArc k 1) p).mp hmem
  have hpn : ‖p‖ = 1 := hp.1
  have harc : (⟨p, mem_sphere_zero_iff_norm.mpr hpn⟩ : Circle₁) ∈
      boundaryArc k 1 := hm.2 _ rfl
  have hgt : (-1 : ℝ) ^ 1 * ((p ^ k).re) < 0 := harc.2
  have hle : (p ^ k).re ≤ 0 := hp.2
  simp only [pow_one, neg_one_mul] at hgt
  linarith

/-- Compact support inside arc-1's seam domain gives uniform
vanishing near the closed slit. -/
lemma suppAwaySlit1_of_seam1_support {k : ℕ} {f : ℂ → ℂ}
    (hc : HasCompactSupport f)
    (hs : tsupport f ⊆
      (seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) : Set ℂ)) :
    SuppAwaySlit1 k f := by
  have hopen : IsOpen (Bracket.slit k)ᶜ := (isClosed_slit k).isOpen_compl
  have hsub : tsupport f ⊆ (Bracket.slit k)ᶜ := fun z hz hslit =>
    slit_notMem_seamDomain hslit (hs hz)
  obtain ⟨ε, hε, hth⟩ := hc.exists_cthickening_subset_open hopen hsub
  refine ⟨ε, hε, fun w ⟨p, hp, hwp⟩ => ?_⟩
  by_contra h0
  have hw : w ∈ tsupport f := subset_closure (Function.mem_support.mpr h0)
  have hpc : p ∈ cthickening ε (tsupport f) := by
    apply mem_cthickening_of_dist_le p w ε _ hw
    rw [dist_eq_norm, norm_sub_rev]
    exact hwp.le
  exact (hth hpc) hp

end KsIndex.Trace
