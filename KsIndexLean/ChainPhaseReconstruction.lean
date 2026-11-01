module

public import KsIndexLean.WeakPhaseCopies

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma weakPhaseFamily_iter {m : ℕ} {c : ℂ} {u : ZMod (2 * m) → ComplexH1}
    (hu : ∀ n, u (n + 2) = c • u n) (r j : ℕ) :
    u ((r + 2 * j : ℕ) : ZMod (2 * m)) = c ^ j • u (r : ZMod (2 * m)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : ((r + 2 * (j + 1) : ℕ) : ZMod (2 * m)) =
        ((r + 2 * j : ℕ) : ZMod (2 * m)) + 2 := by push_cast; ring
    rw [h, hu, ih, smul_smul, pow_succ']

lemma weakPhaseFamily_recover (m : ℕ) [NeZero m] (c : ℂ)
    (u : ZMod (2 * m) → ComplexH1) (hu : ∀ n, u (n + 2) = c • u n) :
    weakPhaseCopies m c (u 1, u 0) = u := by
  funext n
  have h : u n = c ^ (n.val / 2) • u ((n.val % 2 : ℕ) : ZMod (2 * m)) := by
    conv_lhs => rw [Twisted.val_decomp n]
    exact weakPhaseFamily_iter hu _ _
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one n.val with hr | hr
  · simp only [weakPhaseCopies, hr, ite_true, Nat.cast_zero]
  · simp only [weakPhaseCopies, hr, one_ne_zero, ite_false, Nat.cast_one]

def reconstructChainPhase (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (p : slitTraceDomain k c) : chainChartPhaseDomain k m c :=
  ⟨weakChainClass k m (reconstructWeakPhase k m c hc p), by
    rw [mem_chainChartPhaseDomain_iff_coordinates, chainChartCoordinates_class]
    exact weakPhaseCopies_shift m c hc p.val⟩

lemma reconstructChainPhase_coordinates (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (p : slitTraceDomain k c) :
    chainChartCoordinatesCLM k m (reconstructChainPhase k m c hc p).val =
      weakPhaseCopies m c p.val :=
  chainChartCoordinates_class k m (reconstructWeakPhase k m c hc p)

lemma chainPhasePair_reconstruct (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (p : slitTraceDomain k c) :
    chainPhasePairLinearMap k m c (reconstructChainPhase k m c hc p) = p := by
  apply Subtype.ext
  change (chainChartCoordinatesCLM k m (reconstructChainPhase k m c hc p).val 1,
    chainChartCoordinatesCLM k m (reconstructChainPhase k m c hc p).val 0) = p.val
  rw [reconstructChainPhase_coordinates, weakPhaseCopies_one, weakPhaseCopies_zero]

lemma reconstruct_chainPhasePair (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (q : chainChartPhaseDomain k m c) :
    reconstructChainPhase k m c hc (chainPhasePairLinearMap k m c q) = q := by
  apply Subtype.ext
  apply chainChartCoordinates_injective k m
  rw [reconstructChainPhase_coordinates]
  exact weakPhaseFamily_recover m c (chainChartCoordinatesCLM k m q.val)
    ((mem_chainChartPhaseDomain_iff_coordinates k m c q.val).mp q.property)

/-- Extraction and quasiperiodic reconstruction are mutually inverse linear identifications. -/
def chainPhasePairLinearEquiv (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1) :
    chainChartPhaseDomain k m c ≃ₗ[ℂ] slitTraceDomain k c :=
  LinearEquiv.ofBijective (chainPhasePairLinearMap k m c)
    ⟨Function.LeftInverse.injective (reconstruct_chainPhasePair k m c hc),
      Function.RightInverse.surjective (chainPhasePair_reconstruct k m c hc)⟩

lemma weakPhaseCopies_norm_le (m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (p : ComplexH1 × ComplexH1) : ‖weakPhaseCopies m c p‖ ≤ ‖p‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr
  intro n
  have hn := Complex.norm_eq_one_of_pow_eq_one hc (NeZero.ne m)
  simp only [weakPhaseCopies, norm_smul, norm_pow, hn, one_pow, one_mul]
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _

lemma chainPhasePair_norm (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (q : chainChartPhaseDomain k m c) : ‖chainPhasePairLinearMap k m c q‖ = ‖q‖ := by
  apply le_antisymm (chainPhasePair_bound k m c q)
  have h := weakPhaseCopies_norm_le m c hc (chainPhasePairLinearMap k m c q).val
  change ‖weakPhaseCopies m c (chainChartCoordinatesCLM k m q.val 1,
    chainChartCoordinatesCLM k m q.val 0)‖ ≤ _ at h
  rw [weakPhaseFamily_recover m c (chainChartCoordinatesCLM k m q.val)
    ((mem_chainChartPhaseDomain_iff_coordinates k m c q.val).mp q.property)] at h
  exact h

def chainPhasePairLinearIsometryEquiv (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1) :
    chainChartPhaseDomain k m c ≃ₗᵢ[ℂ] slitTraceDomain k c where
  toLinearEquiv := chainPhasePairLinearEquiv k m c hc
  norm_map' := chainPhasePair_norm k m c hc

/-- Direct phase-domain equivalence to the orientation-correct spherical realization. -/
def chainPhaseSphereLinearIsometryEquiv (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1) :
    chainChartPhaseDomain k m c ≃ₗᵢ[ℂ] KsIndex.Spherical.SphericalSlitPhaseSpace k c⁻¹ := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne m)] at hc
    exact zero_ne_one hc
  exact (chainPhasePairLinearIsometryEquiv k m c hc).trans
    (KsIndex.Spherical.upperLowerSlitToSphere k c hc0)

lemma chainPhaseSphere_equiv_agrees (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (hc0 : c ≠ 0) (q : chainChartPhaseDomain k m c) :
    chainPhaseSphereLinearIsometryEquiv k m c hc q = chainPhaseToSphereCLM k m c hc0 q := rfl

end KsIndex.Trace
