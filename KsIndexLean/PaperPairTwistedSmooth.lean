module

public import KsIndexLean.PaperSmoothPair
public import KsIndexLean.SmoothPairCyclicReconstruction

@[expose] public section


/-! Convert the paper upper/lower pair to the one-period `IsSmoothTw` carrier.
Copy zero is lower and copy one is upper, so the twist remains `c`. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.Surface KsIndex.Bracket

lemma arc_mem_seamDomain (a : ℕ) {z : ℂ} (hz : z ∈ arc 3 a) :
    z ∈ seamDomain (boundaryArc 3 a) (isOpen_boundaryArc 3 a) := by
  refine ⟨⟨by rw [hz.1]; norm_num, by rw [hz.1]; norm_num⟩, ?_⟩
  rintro ⟨w, hw, he⟩
  apply hw
  change (w : ℂ) ∈ arc 3 a
  rwa [he]

lemma SmoothSlitPair.reverse_one_smooth {c : ℂ} (p : SmoothSlitPair c)
    {z : ℂ} (hz : z ∈ arc 3 1) :
    ContDiffAt ℝ ∞ (phaseGerm 1 p.lower p.upper) z := by
  have hzD := arc_mem_seamDomain 1 hz
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz.1]; norm_num)
  let F := fun w => if ‖w‖ ≤ 1 then p.upper w else p.lower (σ w)
  have hF : ContDiffAt ℝ ∞ F (σ z) := by
    rw [σ_self hz.1]
    exact p.seam1_smooth.contDiffAt ((seamDomain _ _).isOpen.mem_nhds hzD)
  apply (hF.comp z (contDiffAt_σ hz0)).congr_of_eventuallyEq
  filter_upwards [(seamDomain (boundaryArc 3 1) (isOpen_boundaryArc 3 1)).isOpen.mem_nhds hzD]
    with w hw
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hw.1.1)
  rcases lt_trichotomy ‖w‖ 1 with hn | hn | hn
  · simp only [phaseGerm, ite_eq_left hn.le, Function.comp_apply, F,
      ite_eq_right (not_norm_σ_le hw0 hn), σ_σ]
  · have hwa : w ∈ arc 3 1 := by
      let b : Circle₁ := ⟨w, mem_sphere_zero_iff_norm.mpr hn⟩
      have hb : b ∈ boundaryArc 3 1 := by
        by_contra hh
        exact hw.2 ⟨b, hh, rfl⟩
      exact hb
    simp only [phaseGerm, ite_eq_left hn.le, Function.comp_apply, F, σ_self hn]
    exact (p.seam1_value w hwa).symm
  · have hσ : ‖σ w‖ ≤ 1 := by
      rw [norm_σ]
      exact ((inv_lt_one₀ (norm_pos_iff.mpr hw0)).mpr hn).le
    simp only [phaseGerm, ite_eq_right (not_le.mpr hn), one_mul, Function.comp_apply,
      F, ite_eq_left hσ]

/-- Closed-disk restriction leaves functions vanishing outside the closed disk unchanged. -/
lemma closedDiskRestriction_eq_of_exterior {f : ℂ → ℂ}
    (hf : ∀ z, 1 < ‖z‖ → f z = 0) : closedDiskRestriction f = f := by
  funext z
  by_cases hz : ‖z‖ ≤ 1
  · exact ite_eq_left hz
  · simp only [closedDiskRestriction, ite_eq_right hz, hf z (lt_of_not_ge hz)]

/-- The paper pair satisfies `IsSmoothTw 3 c` under `smoothPairCopies`. -/
theorem SmoothSlitPair.isSmoothTw {c : ℂ} (p : SmoothSlitPair c) :
    KsIndex.Twisted.IsSmoothTw 3 c (smoothPairCopies p.upper p.lower) := by
  have hU := closedDiskRestriction_eq_of_exterior p.upper_exterior
  have hL := closedDiskRestriction_eq_of_exterior p.lower_exterior
  have h0 : smoothPairCopies p.upper p.lower 0 = p.lower := by simp [smoothPairCopies, hL]
  have h1 : smoothPairCopies p.upper p.lower 1 = p.upper := by simp [smoothPairCopies, hU]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    unfold smoothPairCopies
    split_ifs
    · rw [hL]; exact p.lower_smooth
    · rw [hU]; exact p.upper_smooth
  · intro z hz
    rw [KsIndex.Twisted.seamArc_one_zero] at hz
    have he : glue (smoothPairCopies p.upper p.lower) 0 = phaseGerm 1 p.lower p.upper := by
      funext w
      simp only [glue, zero_add, h0, h1, phaseGerm, one_mul, σ]
    rw [he]
    exact p.reverse_one_smooth hz
  · intro z hz
    rw [KsIndex.Twisted.seamArc_one_one] at hz
    have he : KsIndex.Twisted.glueTw c (smoothPairCopies p.upper p.lower) =
        (fun w => if ‖w‖ ≤ 1 then p.upper w else c * p.lower (σ w)) := by
      funext w
      simp only [KsIndex.Twisted.glueTw, h0, h1, σ]
    rw [he]
    exact p.seam0_smooth.contDiffAt ((seamDomain _ _).isOpen.mem_nhds (arc_mem_seamDomain 0 hz))
  · intro n z hz
    unfold smoothPairCopies
    split_ifs
    · rw [hL]; exact p.lower_exterior z hz
    · rw [hU]; exact p.upper_exterior z hz

end KsIndex.PaperSlitTransport
