module

public import KsIndexLean.KarcherGlobalFirstGeometry
public import KsIndexLean.KarcherCoverNormalization
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Separation.Connected

@[expose] public section


/-! Connected-domain and constant-root-ratio steps for covering uniqueness. -/
noncomputable section
open Set
namespace KsIndex.KarcherData

lemma isConnected_nonzero_puncture_complement {k : ℕ} (hk : 2 ≤ k) :
    IsConnected {w : ℂ | w ∉ Surface.punctures k ∧ w ≠ 0} := by
  have hp : Surface.punctures k = (↑(punctureFinset k) : Set ℂ) := by
    ext w
    exact (mem_punctureFinset hk).symm
  have hc : (Surface.punctures k ∪ {0}).Countable := by
    rw [hp]
    exact (punctureFinset k).finite_toSet.countable.union (countable_singleton 0)
  have he : (Surface.punctures k ∪ {0})ᶜ =
      {w : ℂ | w ∉ Surface.punctures k ∧ w ≠ 0} := by
    ext w
    simp only [mem_compl_iff, mem_union, mem_singleton_iff, not_or, mem_ofPred_eq]
  rw [← he]
  exact (hc.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isConnected

lemma finite_complex_power_roots {n : ℕ} (hn : n ≠ 0) :
    Set.Finite {z : ℂ | z ^ n = 1} := by
  have hp : (Polynomial.X ^ n - 1 : Polynomial ℂ) ≠ 0 := by
    intro he
    have hh := congrArg (Polynomial.eval (0 : ℂ)) he
    simp [hn] at hh
  simpa [Polynomial.IsRoot, sub_eq_zero] using Polynomial.finite_setOfPred_isRoot hp

/-- Equality of positive powers on a connected nonzero domain gives one
constant root-of-unity ratio. This is independent of holomorphic extension. -/
theorem exists_constant_power_ratio {S : Set ℂ} (hS : IsConnected S)
    {f : ℂ → ℂ} (hf : ContinuousOn f S) {n : ℕ} (hn : n ≠ 0)
    (hzero : ∀ w ∈ S, w ≠ 0) (hpow : ∀ w ∈ S, f w ^ n = w ^ n) :
    ∃ ζ : ℂ, ζ ^ n = 1 ∧ ∀ w ∈ S, f w = ζ * w := by
  let r : ℂ → ℂ := fun w => f w / w
  have hr : ContinuousOn r S := hf.div continuousOn_id hzero
  have hp (w : ℂ) (hw : w ∈ S) : r w ^ n = 1 := by
    dsimp [r]
    rw [div_pow, hpow w hw, div_self (pow_ne_zero n (hzero w hw))]
  have hfin : (r '' S).Finite := (finite_complex_power_roots hn).subset (by
    rintro z ⟨w, hw, rfl⟩
    exact hp w hw)
  have hpre : IsPreconnected (r '' S) := hS.isPreconnected.image r hr
  obtain ⟨a, ha⟩ := hS.nonempty
  have he (w : ℂ) (hw : w ∈ S) : r a = r w := by
    by_contra hne
    exact hfin.not_infinite (hpre.infinite_of_nontrivial
      ⟨r a, mem_image_of_mem r ha, r w, mem_image_of_mem r hw, hne⟩)
  refine ⟨r a, hp a ha, ?_⟩
  intro w hw
  exact (div_eq_iff (hzero w hw)).mp (he w hw).symm

/-- Finite-coordinate uniqueness after equality of the correctly oriented
Gauss powers has been established. The orientation comparison and spherical
descent needed to apply this to competing coverings remain separate. -/
theorem finite_coordinate_unique {k : ℕ} (hk : 2 ≤ k) {f : ℂ → ℂ}
    (hf : ContinuousOn f {w | w ∉ Surface.punctures k})
    (hpow : ∀ w, w ∉ Surface.punctures k → f w ^ (k - 1) = w ^ (k - 1))
    (havoid : ∀ w, w ∉ Surface.punctures k → f w ∉ Surface.punctures k)
    (harc : f 1 ∈ Surface.arc k 1) :
    ∀ w, w ∉ Surface.punctures k → f w = w := by
  have hz : (0 : ℂ) ∉ Surface.punctures k := by
    simp [Surface.punctures, show 2 * k ≠ 0 by omega]
  have hone : (1 : ℂ) ∉ Surface.punctures k := by norm_num [Surface.punctures]
  obtain ⟨ζ, hζ, he⟩ := exists_constant_power_ratio
    (isConnected_nonzero_puncture_complement hk)
    (hf.mono (fun w hw => hw.1)) (by omega : k - 1 ≠ 0)
    (fun w hw => hw.2) (fun w hw => hpow w hw.1)
  have hrot : ∀ w, w ∉ Surface.punctures k → ζ * w ∉ Surface.punctures k := by
    intro w hw
    by_cases hw0 : w = 0
    · simpa only [hw0, mul_zero] using hz
    · rw [← he w ⟨hw, hw0⟩]
      exact havoid w hw
  have hζarc : ζ ∈ Surface.arc k 1 := by
    have hh := he 1 ⟨hone, one_ne_zero⟩
    rw [mul_one] at hh
    exact hh ▸ harc
  have hnonempty : (punctureFinset k).Nonempty := by
    apply Finset.card_pos.mp
    rw [punctureFinset_card hk]
    omega
  obtain ⟨a, ha⟩ := hnonempty
  have hζone := cover_rotation_normalization hk hζ ((mem_punctureFinset hk).mp ha) hrot hζarc
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    apply eq_zero_of_pow_eq_zero
    simpa only [zero_pow (by omega : k - 1 ≠ 0)] using hpow 0 hz
  · simpa only [hζone, one_mul] using he w ⟨hw, hw0⟩

end KsIndex.KarcherData
