module

public import KsIndexLean.SmoothPairCyclicReconstruction
public import KsIndexLean.CcSmoothWeakChain
public import KsIndexLean.ChainPhaseReconstruction

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The cyclic smooth reconstruction has the weak phase coordinates
`weakPhaseCopies`. Equality of H1 carriers follows from their almost-everywhere values. -/
lemma smoothPair_cyclic_weak_coordinates {k m : ℕ} [NeZero m] (c : ℂ)
    (f g : ℂ → ℂ) (u v : ComplexH1)
    (hm : KsIndex.Twisted.extF m c (smoothPairCopies f g) ∈ KsIndex.Surface.CcSmooth k m)
    (hu : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f)
    (hv : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] g) :
    (fun n => ccSmoothCopy ⟨_, hm⟩ n) = weakPhaseCopies m c (u, v) := by
  funext n
  apply valueCLM_injective
  unfold weakPhaseCopies
  rcases Nat.mod_two_eq_zero_or_one n.val with hn | hn
  · simp only [hn, ite_true, map_smul]
    apply Lp.ext
    filter_upwards [ccSmoothCopy_value_ae ⟨_, hm⟩ n, hv,
      Lp.coeFn_smul (c ^ (n.val / 2)) (valueCLM v),
      ae_restrict_mem KsIndex.SurfaceForm.measurableSet_disk] with z hc hz hs hzd
    rw [hs, Pi.smul_apply, hz, hc]
    simp [KsIndex.Twisted.extF, smoothPairCopies, hn, closedDiskRestriction,
      (KsIndex.SurfaceForm.mem_disk_iff.mp hzd).le, smul_eq_mul]
  · simp only [hn, one_ne_zero, ite_false, map_smul]
    apply Lp.ext
    filter_upwards [ccSmoothCopy_value_ae ⟨_, hm⟩ n, hu,
      Lp.coeFn_smul (c ^ (n.val / 2)) (valueCLM u),
      ae_restrict_mem KsIndex.SurfaceForm.measurableSet_disk] with z hc hz hs hzd
    rw [hs, Pi.smul_apply, hz, hc]
    simp [KsIndex.Twisted.extF, smoothPairCopies, hn, closedDiskRestriction,
      (KsIndex.SurfaceForm.mem_disk_iff.mp hzd).le, smul_eq_mul]

lemma smoothPair_cyclic_chart_coordinates {k m : ℕ} [NeZero m] (c : ℂ)
    (f g : ℂ → ℂ) (u v : ComplexH1)
    (hm : KsIndex.Twisted.extF m c (smoothPairCopies f g) ∈ KsIndex.Surface.CcSmooth k m)
    (hu : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f)
    (hv : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] g) :
    chainChartCoordinatesCLM k m (ccSmoothToChainChart k m ⟨_, hm⟩) =
      weakPhaseCopies m c (u, v) := by
  rw [ccSmoothToChainChart_coordinates]
  exact smoothPair_cyclic_weak_coordinates c f g u v hm hu hv

/-- Pair H1 convergence survives quasiperiodic reconstruction on finitely many
copies. No character constraint is needed for this continuity statement. -/
lemma weakPhaseCopies_tendsto (m : ℕ) (c : ℂ)
    {p : ℕ → ComplexH1 × ComplexH1} {q : ComplexH1 × ComplexH1}
    (hp : Tendsto p atTop (𝓝 q)) :
    Tendsto (fun j => weakPhaseCopies m c (p j)) atTop (𝓝 (weakPhaseCopies m c q)) := by
  apply tendsto_pi_nhds.mpr
  intro n
  unfold weakPhaseCopies
  split_ifs
  · exact ((continuous_snd.tendsto q).comp hp).const_smul _
  · exact ((continuous_fst.tendsto q).comp hp).const_smul _

/-- The chart norm is exactly the norm of the original finite weak-copy
coordinates, so convergence of those coordinates detects chart convergence. -/
lemma chainChart_tendsto_of_coordinates (k m : ℕ) [NeZero m]
    {q : ℕ → ChainChartSpace k m} {r : ChainChartSpace k m}
    (h : Tendsto (fun n => chainChartCoordinatesCLM k m (q n)) atTop
      (𝓝 (chainChartCoordinatesCLM k m r))) : Tendsto q atTop (𝓝 r) := by
  have hn (x : ChainChartSpace k m) : ‖chainChartCoordinatesCLM k m x‖ = ‖x‖ :=
    (chainChartLinearIsometryEquiv k m).norm_map x
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  simpa only [← map_sub, hn] using h

/-- Convergence transfers from the approximating H1 pairs through the actual
original-CcSmooth encoding to the reconstructed weak phase sector. -/
theorem smoothPair_cyclic_chart_tendsto {k m : ℕ} [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (p : slitTraceDomain k c) (S : ℕ → KsIndex.Surface.CcSmooth k m)
    (f g : ℕ → ℂ → ℂ) (U V : ℕ → ComplexH1)
    (ht : Tendsto (fun n => (U n, V n)) atTop (𝓝 p.val))
    (he : ∀ᶠ n in atTop, (S n).val = KsIndex.Twisted.extF m c (smoothPairCopies (f n) (g n)))
    (hu : ∀ᶠ n in atTop, (valueCLM (U n) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] f n)
    (hv : ∀ᶠ n in atTop, (valueCLM (V n) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] g n) :
    Tendsto (fun n => ccSmoothToChainChart k m (S n)) atTop
      (𝓝 (reconstructChainPhase k m c hc p).val) := by
  apply chainChart_tendsto_of_coordinates k m
  rw [reconstructChainPhase_coordinates]
  apply (weakPhaseCopies_tendsto m c ht).congr'
  filter_upwards [he, hu, hv] with n hn hU hV
  have hm : KsIndex.Twisted.extF m c (smoothPairCopies (f n) (g n)) ∈
      KsIndex.Surface.CcSmooth k m := hn ▸ (S n).property
  have hs : S n = ⟨_, hm⟩ := Subtype.ext hn
  rw [hs]
  exact (smoothPair_cyclic_chart_coordinates c (f n) (g n) (U n) (V n) hm hU hV).symm

end KsIndex.Trace
