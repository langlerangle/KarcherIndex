module

public import KsIndexLean.SingleArcForm

@[expose] public section


noncomputable section
namespace KsIndex.SingleArcReindex
open KsIndex.Trace KsIndex.CircleSobolev KsIndex.DtnBridge KsIndex.NegativeDensity
open KsIndex.WeakH1 KsIndex.Spectral

lemma dnBoundary_index_eq_singleArc {k j : ℕ} (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    negativeIndex (fun f : dnCharacterSpace k j => (dnBoundaryForm hj0 hjk f f).re) =
      negativeIndex (fun f : dnSpace 1 => (singleArcForm k j f f).re) := by
  have he := negativeIndex_congr (dnEquiv hk (le_of_lt hjk))
    (fun f : dnCharacterSpace k j => (dnBoundaryForm hj0 hjk f f).re)
    (fun f : dnSpace 1 => (k : ℝ) * (singleArcForm k j f f).re)
    (by
      intro f
      rw [dnBoundaryForm_eq_singleArc hk hj0 hjk]
      simp)
  exact he.symm.trans (negativeIndex_pos_mul _ _ (by exact_mod_cast (show 0 < k by omega)))

lemma dnBoundary_nullity_eq_singleArc {k j : ℕ} (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    sesqNullity (dnBoundaryForm hj0 hjk) = sesqNullity (singleArcForm k j) := by
  have he := sesqNullity_congr (dnEquiv hk (le_of_lt hjk))
    (dnBoundaryForm hj0 hjk) (fun f g : dnSpace 1 => (k : ℂ) * singleArcForm k j f g)
    (fun f g => (dnBoundaryForm_eq_singleArc hk hj0 hjk f g).symm)
  exact he.symm.trans (sesqNullity_nonzero_mul _ _ (by exact_mod_cast (show k ≠ 0 by omega)))

/-- The mixed disk index equals the index of the single-arc boundary form. -/
theorem dnDisk_index_eq_singleArc {k j : ℕ} (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    diskWeakIndex (mixedCharacterDomain k j true false) (surfacePotential k) =
      negativeIndex (fun f : dnSpace 1 => (singleArcForm k j f f).re) :=
  (dnJacobi_index_eq_boundary hk hj0 hjk).trans (dnBoundary_index_eq_singleArc hk hj0 hjk)

/-- The mixed disk nullity equals the nullity of the single-arc boundary form. -/
theorem dnDisk_nullity_eq_singleArc {k j : ℕ} (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    (diskWeakNullity (mixedCharacterDomain k j true false) (surfacePotential k) : ℕ∞) =
      sesqNullity (singleArcForm k j) :=
  (dnJacobi_nullity_eq_boundary hk hj0 hjk).trans (dnBoundary_nullity_eq_singleArc hk hj0 hjk)

end KsIndex.SingleArcReindex
