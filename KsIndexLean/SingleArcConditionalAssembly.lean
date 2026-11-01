module

public import KsIndexLean.SingleArcCounts
public import KsIndexLean.WeakMixedIndex
public import KsIndexLean.CountUnconditional

@[expose] public section


/-! Conditional mixed-sector nullity from a single-arc count bound.
The sum of the single-arc index and nullity is assumed to be at most one;
the proved index-one result then forces nullity zero. The all-class theorem
requires this bound only for middle classes and uses unconditional edge-class results. -/
noncomputable section
namespace KsIndex.SingleArcReindex
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral
open KsIndex.CircleSobolev KsIndex.DtnBridge KsIndex.NegativeDensity

/-- The unscaled single-arc index-plus-nullity bound used as an explicit hypothesis. -/
def SingleArcUpperBound (k j : ℕ) : Prop :=
  negativeIndex (fun f : dnSpace 1 => (singleArcForm k j f f).re) +
    sesqNullity (singleArcForm k j) ≤ 1

/-- The mixed index transports to index one for the single-arc form. -/
theorem singleArc_index_one {k j : ℕ} (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    negativeIndex (fun f : dnSpace 1 => (singleArcForm k j f f).re) = 1 := by
  rw [← dnDisk_index_eq_singleArc hk hj0 hjk]
  exact mixedND_weak_index_one hk hjk

/-- The supplied single-arc count bound forces the corresponding mixed-sector nullity to vanish. -/
theorem mixed_nullity_zero_of_singleArc_bound {k j : ℕ} (hk : 3 ≤ k)
    (hj0 : 0 < j) (hjk : j < k) (hC : SingleArcUpperBound k j) :
    diskWeakNullity (mixedCharacterDomain k j true false) (surfacePotential k) = 0 := by
  unfold SingleArcUpperBound at hC
  rw [singleArc_index_one hk hj0 hjk, ← dnDisk_nullity_eq_singleArc hk hj0 hjk] at hC
  have hn : 1 + diskWeakNullity (mixedCharacterDomain k j true false)
      (surfacePotential k) ≤ 1 := by exact_mod_cast hC
  omega

/-- All classes in this orientation, conditional only on the middle-class bounds.
The edge classes use the already proved unconditional bracketing theorem. -/
theorem all_mixed_nullity_zero_of_middle_bounds {k : ℕ} (hk : 3 ≤ k)
    (hC : ∀ j : ℕ, 2 ≤ j → j + 2 ≤ k → SingleArcUpperBound k j)
    (j : ℕ) (hj : j < k) :
    diskWeakNullity (mixedCharacterDomain k j true false) (surfacePotential k) = 0 := by
  by_cases he : j = 0 ∨ j = 1 ∨ j = k - 1
  · exact zaremba_nullity_zero_edge_uncond hk he (by decide)
  · exact mixed_nullity_zero_of_singleArc_bound hk (by omega) hj
      (hC j (by omega) (by omega))

end KsIndex.SingleArcReindex
