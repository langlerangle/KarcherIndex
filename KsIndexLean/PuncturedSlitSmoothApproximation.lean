module

public import KsIndexLean.SmoothPairWeakCoordinates

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Quasiperiodic extension preserves the exact positive translation phase,
including the cyclic wrap. -/
lemma extF_positive_shift {m : ℕ} [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (v : ZMod (2 * 1) → ℂ → ℂ) (n : ZMod (2 * m)) (z : ℂ) :
    KsIndex.Twisted.extF m c v (n + 2) z = c * KsIndex.Twisted.extF m c v n z := by
  exact (KsIndex.Twisted.mem_shift_iff.mp
    (KsIndex.Twisted.extE_mem_shift hc ((KsIndex.Surface.uncurryE 1) v))) n z

/-- Every slit pair vanishing on a common open puncture neighborhood admits
actual original-CcSmooth cyclic approximants. Their translation phase holds
at every scale, and their weak chart images converge to the reconstructed pair.
No rotation projection or density conclusion is hidden in the hypotheses. -/
theorem punctured_slit_smooth_chain_approximation {k m : ℕ} (hk : 1 ≤ k) [NeZero m]
    (c : ℂ) (hc : c ^ m = 1) (p : slitTraceDomain k c)
    {H : Set ℂ} (hH : IsOpen H) (hpH : KsIndex.Surface.punctures k ⊆ H)
    (hu : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), z ∈ H → valueCLM p.val.1 z = 0)
    (hv : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), z ∈ H → valueCLM p.val.2 z = 0) :
    ∃ S : ℕ → KsIndex.Surface.CcSmooth k m,
      (∀ j n z, (S j).val (n + 2) z = c * (S j).val n z) ∧
      Tendsto (fun j => ccSmoothToChainChart k m (S j)) atTop
        (𝓝 (reconstructChainPhase k m c hc p).val) := by
  classical
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne m)] at hc
    exact zero_ne_one hc
  let phase := fun a : ℕ => if a = 0 then c else 1
  have hphase0 : phase 0 = c := ite_eq_left rfl
  have hphase1 : phase 1 = 1 := ite_eq_right (by decide)
  have hnon a (_ha : a = 0 ∨ a = 1) : phase a ≠ 0 := by
    dsimp [phase]
    split_ifs
    · exact hc0
    · exact one_ne_zero
  obtain ⟨h1, h0⟩ := (mem_slitTraceDomain k c p.val).mp p.property
  have htrace a (ha : a = 0 ∨ a = 1) :
      arcTrace (boundaryArc k a) p.val.1 = phase a • arcTrace (boundaryArc k a) p.val.2 := by
    rcases ha with rfl | rfl
    · simpa only [hphase0] using h0
    · simpa only [hphase1, one_smul] using h1
  obtain ⟨ι, t, a, F, G, F₀, G₀, U, V, ht, ha, hpiece, hint, hrep⟩ :=
    slit_pair_partition_approximation k p.val.1 p.val.2 phase hnon htrace hH hpH hu hv
  let f := fun n z => F₀ n z + ∑ i ∈ t, F i n z
  let g := fun n z => G₀ n z + ∑ i ∈ t, G i n z
  have hmem : ∀ᶠ n in atTop,
      KsIndex.Twisted.extF m c (smoothPairCopies (f n) (g n)) ∈ KsIndex.Surface.CcSmooth k m := by
    have hall := (eventually_all_finset t).mpr hpiece
    filter_upwards [hall, hint, hrep] with n hn hi hr
    exact finite_phase_pair_cyclic t hk c hc a phase hphase0 hphase1
      (fun i => F i n) (fun i => G i n) (F₀ n) (G₀ n) ha hn
      hi.2.2.1 hi.2.2.2.2.2 hr.1 hr.2.2.1
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmem
  let S : ℕ → KsIndex.Surface.CcSmooth k m := fun n =>
    if hn : N ≤ n then ⟨_, hN n hn⟩ else 0
  have hS : ∀ᶠ n in atTop,
      (S n).val = KsIndex.Twisted.extF m c (smoothPairCopies (f n) (g n)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [S, dite_eq_left hn]
  refine ⟨S, ?_, smoothPair_cyclic_chart_tendsto c hc p S f g U V ht hS
    (hrep.mono fun n h => h.2.1.1) (hrep.mono fun n h => h.2.2.2.1)⟩
  intro j n z
  dsimp [S]
  split_ifs with hj
  · exact extF_positive_shift c hc _ n z
  · simp

/-- The radius-form hole condition supplied by the puncture cutoff gives the
open neighborhood required by the assembled smoothing theorem. -/
theorem puncture_radius_slit_smooth_chain_approximation {k m : ℕ} (hk : 1 ≤ k) [NeZero m]
    (c : ℂ) (hc : c ^ m = 1) (p : slitTraceDomain k c) {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ∀ᵐ z ∂volume.restrict (disk : Set ℂ),
      (∃ q ∈ KsIndex.Surface.punctures k, ‖z - q‖ ≤ ρ) → valueCLM p.val.1 z = 0)
    (hv : ∀ᵐ z ∂volume.restrict (disk : Set ℂ),
      (∃ q ∈ KsIndex.Surface.punctures k, ‖z - q‖ ≤ ρ) → valueCLM p.val.2 z = 0) :
    ∃ S : ℕ → KsIndex.Surface.CcSmooth k m,
      (∀ j n z, (S j).val (n + 2) z = c * (S j).val n z) ∧
      Tendsto (fun j => ccSmoothToChainChart k m (S j)) atTop
        (𝓝 (reconstructChainPhase k m c hc p).val) := by
  let H : Set ℂ := ⋃ q ∈ KsIndex.Surface.punctures k, Metric.ball q ρ
  have hH : IsOpen H := isOpen_biUnion (fun q _ => Metric.isOpen_ball)
  have hpH : KsIndex.Surface.punctures k ⊆ H :=
    fun q hq => Set.mem_biUnion hq (Metric.mem_ball_self hρ)
  apply punctured_slit_smooth_chain_approximation hk c hc p hH hpH
  · filter_upwards [hu] with z hz hzH
    obtain ⟨q, hq, hqz⟩ := Set.mem_iUnion₂.mp hzH
    exact hz ⟨q, hq, by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hqz).le⟩
  · filter_upwards [hv] with z hz hzH
    obtain ⟨q, hq, hqz⟩ := Set.mem_iUnion₂.mp hzH
    exact hz ⟨q, hq, by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hqz).le⟩

end KsIndex.Trace
