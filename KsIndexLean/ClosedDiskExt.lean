module

/-
KsIndexLean — ClosedDiskExt: gluing local one-sided smooth extensions into one global finite-order
smooth function on the closed unit disk.

If every point `x` of the closed disk carries a function `F` that is `C^∞` at `x` and agrees with
`f` on `ball 0 1` near `x`, then for every finite order `m` there is a compactly supported, globally
`C^m` function `G` agreeing with `f` on the open disk (`exists_finite_order_extension`).  The
consumer needs this only at a fixed finite `m` (the radial modes need only `C¹`/`C²`), so the honest
partition-of-unity content is all that is required — the `C^∞` strengthening (a telescoping-series
upgrade) is deliberately not ported.

Every `f ∈ NatCc k b₁ b₀` satisfies the hypothesis: interior points from `ContDiffOn` on the open
disk, Neumann-arc points from `OneSided`, and Dirichlet-arc/puncture points from local vanishing.

Proof by Harmonic's Aristotle (`exists_finite_order_extension`), written from a statement by Kai.
-/
public import Mathlib

@[expose] public section


noncomputable section

open Metric Set
open scoped ContDiff Manifold

namespace KsIndex.ClosedDiskExt

/-- **Finite-order closed-disk extension.**  Given, at every point of the closed unit disk, a
function that is `C^∞` there and agrees with `f` on the open disk nearby, there is for each finite
order `m` a compactly supported globally `C^m` function agreeing with `f` on the open disk. -/
theorem exists_finite_order_extension (f : ℂ → ℂ)
    (h : ∀ x ∈ closedBall (0 : ℂ) 1, ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F x ∧
      ∀ᶠ y in nhds x, y ∈ ball (0 : ℂ) 1 → f y = F y) (m : ℕ) :
    ∃ G : ℂ → ℂ, ContDiff ℝ m G ∧ HasCompactSupport G ∧ ∀ y ∈ ball (0 : ℂ) 1, f y = G y := by
  classical
  -- Localize: an open neighbourhood on which some `C^m` function agrees with `f` on the disk.
  have hloc : ∀ x : closedBall (0 : ℂ) 1, ∃ (U : Set ℂ) (F : ℂ → ℂ), IsOpen U ∧ (x : ℂ) ∈ U ∧
      ContDiffOn ℝ m F U ∧ ∀ y ∈ U, y ∈ ball (0 : ℂ) 1 → f y = F y := by
    rintro ⟨x, hx⟩
    obtain ⟨F, hF, hfF⟩ := h x hx
    obtain ⟨u, hu, hFu⟩ := hF.contDiffOn (m := (m : ℕ)) (by exact_mod_cast le_top) (by simp)
    have hW : u ∩ {y : ℂ | y ∈ ball (0 : ℂ) 1 → f y = F y} ∈ nhds x :=
      Filter.inter_mem hu hfF
    refine ⟨interior (u ∩ {y : ℂ | y ∈ ball (0 : ℂ) 1 → f y = F y}), F, isOpen_interior,
      mem_interior_iff_mem_nhds.2 hW, ?_, ?_⟩
    · exact hFu.mono (le_trans interior_subset Set.inter_subset_left)
    · intro y hy hyb
      exact (interior_subset hy).2 hyb
  choose U F hUopen hxU hFU hfFU using hloc
  have hcover : closedBall (0 : ℂ) 1 ⊆ ⋃ i, U i := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℂ))
    (isClosed_closedBall) U hUopen hcover
  set G₀ : ℂ → ℂ := fun x => ∑ᶠ i, ρ i x • F i x with hG₀def
  have hG₀ : ContDiff ℝ (m : ℕ) G₀ := by
    rw [← contMDiff_iff_contDiff]
    exact hρ.contMDiff_finsum_smul (n := (m : ℕ∞)) hUopen
      (fun i => contMDiffOn_iff_contDiffOn.2 (hFU i))
  have hG₀ball : ∀ y ∈ ball (0 : ℂ) 1, G₀ y = f y := by
    intro y hy
    have hpt : ∀ i, ρ i y • F i y = ρ i y • f y := by
      intro i
      rcases eq_or_ne (ρ i y) 0 with h0 | h0
      · simp [h0]
      · have hmem : y ∈ U i := hρ i (subset_tsupport _ (Function.mem_support.2 h0))
        rw [← hfFU i y hmem hy]
    simp only [hG₀def, hpt]
    rw [← finsum_smul, ρ.sum_eq_one (ball_subset_closedBall hy), one_smul]
  -- Cut off to get compact support.
  let χ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨(χ : ℂ → ℝ) • G₀, ?_, HasCompactSupport.smul_right χ.hasCompactSupport, ?_⟩
  · exact (χ.contDiff.of_le (by exact_mod_cast le_top)).smul hG₀
  · intro y hy
    have h1 : (χ : ℂ → ℝ) y = 1 := χ.one_of_mem_closedBall
      (by simpa [mem_closedBall, dist_eq_norm] using le_of_lt (by simpa using hy))
    show f y = ((χ : ℂ → ℝ) • G₀) y
    simp only [Pi.smul_apply', h1, one_smul]
    exact (hG₀ball y hy).symm

end KsIndex.ClosedDiskExt
