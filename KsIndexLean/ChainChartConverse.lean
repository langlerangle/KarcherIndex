module

public import KsIndexLean.SphericalInversionAE

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- Disk representatives equal almost everywhere give seam charts equal almost everywhere. -/
lemma surface_glue_congr_ae {m : ℕ} {f g : ZMod (2 * m) → ℂ → ℂ}
    (h : ∀ n, f n =ᵐ[volume.restrict (disk : Set ℂ)] g n) (n : ZMod (2 * m)) :
    Surface.glue f n =ᵐ[volume] Surface.glue g n := by
  have hi := (ae_restrict_iff' disk.isOpen.measurableSet).mp (h n)
  have ho := ae_comp_sigma ((ae_restrict_iff' disk.isOpen.measurableSet).mp (h (n + 1)))
  filter_upwards [hi, ho, ae_norm_ne_one] with z hiz hoz hne
  unfold Surface.glue
  by_cases hz : ‖z‖ ≤ 1
  · rw [ite_eq_left hz, ite_eq_left hz]
    exact hiz (by simpa [disk, Metric.mem_ball, dist_zero_right] using lt_of_le_of_ne hz hne)
  · rw [ite_eq_right hz, ite_eq_right hz]
    apply hoz
    change dist (Bracket.σ z) 0 < 1
    rw [dist_zero_right, Bracket.norm_σ]
    exact (inv_lt_one₀ (lt_trans zero_lt_one (lt_of_not_ge hz))).mpr (lt_of_not_ge hz)

/-- Every raw finite-energy cyclic chart family has a unique weak-chain realization. -/
theorem chain_chart_reconstruction (k m : ℕ) [NeZero m]
    (f : ZMod (2 * m) → ℂ → ℂ)
    (hd : ∀ n, ChartH1 disk (f n))
    (hs : ∀ n, ChartH1 (extendedSeamDomain (seamBoundary k m n)
      (isOpen_seamBoundary k m n)) (Surface.glue f n)) :
    ∃! u : weakDiskChain k m, ∀ n,
      (valueCLM (u.val n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f n := by
  choose u hu using fun n => (chartH1_disk_exists_unique (hd n)).exists
  have hm : u ∈ weakDiskChain k m := by
    rw [mem_weakDiskChain]
    intro n
    have he := (surface_glue_congr_ae hu n).filter_mono
      (ae_mono (Measure.restrict_le_self : volume.restrict
        (extendedSeamDomain (seamBoundary k m n) (isOpen_seamBoundary k m n) : Set ℂ) ≤ volume))
    have hH := (chartH1_congr_ae he).mpr (hs n)
    rw [← joinedDiskValue_eq_surface_glue] at hH
    exact (extendedSeamDomain_H1_iff_trace (isOpen_seamBoundary k m n) (u n) (u (n + 1)) 1).mp
      hH |>.trans (one_smul ℂ _)
  refine ⟨⟨u, hm⟩, hu, ?_⟩
  intro v hv
  apply Subtype.ext
  funext n
  exact valueCLM_injective (Lp.ext ((hv n).trans (hu n).symm))

end KsIndex.Trace
