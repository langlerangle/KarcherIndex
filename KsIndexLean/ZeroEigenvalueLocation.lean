module

public import KsIndexLean.SlitNonpositiveBounds
public import KsIndexLean.BracketingCommonEigenfunction

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

lemma finite_eq_level_iff_count_interval {m : ℕ} (ν : Fin m → ℝ)
    (hm : Monotone ν) (L : ℝ) (i : Fin m) :
    ν i = L ↔ (Finset.univ.filter fun j => ν j < L).card ≤ i.val ∧
      i.val < (Finset.univ.filter fun j => ν j ≤ L).card := by
  classical
  have hs := finite_lt_iff_lt_count ν hm L i
  have hw := finite_le_iff_lt_count ν hm L i
  constructor
  · intro h
    constructor
    · by_contra hn
      have hlt := hs.mpr (by omega)
      rw [h] at hlt
      exact lt_irrefl _ hlt
    · exact hw.mp h.le
  · rintro ⟨hs', hw'⟩
    apply le_antisymm (hw.mpr hw')
    by_contra hn
    have hlt := hs.mp (lt_of_not_ge hn)
    omega

lemma finiteCopy_infinite_zero_iff_index_interval
    {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
    [Infinite (finiteSpectralData D V).eigenbasisIndex] (n : ℕ) :
    (finiteSpectralData D V).infiniteReciprocalShift (V.C + 1) n = 0 ↔
      KsIndex.NegativeDensity.negativeIndex (fun u : finiteH1Domain D =>
        (finiteH1Jacobi D V u u).re) ≤ (n : ℕ∞) ∧
      (n : ℕ∞) < finiteCopyIndexNullity D V := by
  rw [finiteCopy_negativeIndex_eq_count, finiteCopy_indexNullity_infinite]
  have h := eq_level_iff_count_interval
    ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_monotone (V.C + 1)) 0 n
  exact_mod_cast h

lemma finiteCopy_finite_zero_iff_index_interval
    {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)]
    (n : Fin (Module.finrank ℂ (WeightedFiniteAmbient D))) :
    (finiteSpectralData D V).finiteReciprocalShift (V.C + 1) n = 0 ↔
      KsIndex.NegativeDensity.negativeIndex (fun u : finiteH1Domain D =>
        (finiteH1Jacobi D V u u).re) ≤ (n.val : ℕ∞) ∧
      (n.val : ℕ∞) < finiteCopyIndexNullity D V := by
  rw [finiteCopy_negativeIndex_eq_finite_count, finiteCopy_indexNullity_finite]
  have h := finite_eq_level_iff_count_interval
    ((finiteSpectralData D V).finiteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).finiteReciprocalShift_monotone (V.C + 1)) 0 n
  exact_mod_cast h

/-- The nonpositive dimension is attained, irrespective of whether the ambient
sector is finite or infinite dimensional. -/
lemma finiteCopy_indexNullity_attained
    {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
    (n : ℕ) (hn : finiteCopyIndexNullity D V = (n : ℕ∞)) :
    ∃ W : Submodule ℂ (finiteH1Domain D), FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n ∧
      ∀ u : W, (finiteH1Jacobi D V u u).re ≤ 0 := by
  by_cases hd : FiniteDimensional ℂ (WeightedFiniteAmbient D)
  · let := hd
    rw [finiteCopy_indexNullity_finite] at hn
    have hc : (finiteSpectralData D V).finiteWeakCount (V.C + 1) 0 = n := by exact_mod_cast hn
    simpa only [hc] using finiteCopy_finite_nonpositive_dimension_attained D V
  · let := (finiteSpectralData D V).eigenbasisIndex_infinite hd
    rw [finiteCopy_indexNullity_infinite] at hn
    have hc : finiteCopyNonpositiveCount D V = n := by exact_mod_cast hn
    simpa only [hc] using finiteCopy_nonpositive_count_attained D V

set_option maxHeartbeats 800000 in
/-- The zero-level equality argument with all dimension alternatives handled.
An attained smaller nonpositive space meets the larger zero eigenspace. -/
lemma finiteCopy_common_zero_of_index_interval
    {ι : Type*} [Fintype ι] (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F) (n : ℕ)
    (hD : finiteCopyIndexNullity D V = ((n + 1 : ℕ) : ℕ∞))
    (hFI : KsIndex.NegativeDensity.negativeIndex (fun u : finiteH1Domain F =>
      (finiteH1Jacobi F V u u).re) ≤ (n : ℕ∞))
    (hFN : (n : ℕ∞) < finiteCopyIndexNullity F V) :
    ∃ u : finiteH1Domain D, u ≠ 0 ∧
      (∀ w : finiteH1Domain F, finiteH1Jacobi F V (finiteH1Inclusion h u) w = 0) ∧
      (∀ w : finiteH1Domain D, finiteH1Jacobi D V u w = 0) := by
  obtain ⟨W, hfd, hdim, hW⟩ := finiteCopy_indexNullity_attained D V (n + 1) hD
  by_cases hf : FiniteDimensional ℂ (WeightedFiniteAmbient F)
  · let := hf
    have hcount : n < (finiteSpectralData F V).finiteWeakCount (V.C + 1) 0 := by
      rw [finiteCopy_indexNullity_finite] at hFN
      exact_mod_cast hFN
    have hbound : (finiteSpectralData F V).finiteWeakCount (V.C + 1) 0 ≤
        Module.finrank ℂ (WeightedFiniteAmbient F) := by
      unfold PositiveCompactSolution.finiteWeakCount
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ.trans (Fintype.card_fin _))
    let k : Fin (Module.finrank ℂ (WeightedFiniteAmbient F)) := ⟨n, lt_of_lt_of_le hcount hbound⟩
    have hz := (finiteCopy_finite_zero_iff_index_interval F V k).mpr ⟨hFI, hFN⟩
    have ht : ∃ W : Submodule ℂ (finiteH1Domain D), FiniteDimensional ℂ W ∧
        Module.finrank ℂ W = k.val + 1 ∧ ∀ u : W,
        (finiteH1Jacobi D V u u).re ≤
          (finiteSpectralData F V).finiteReciprocalShift (V.C + 1) k *
            ‖finiteH1WeightedValue D u‖ ^ 2 := by
      rw [hz]
      exact ⟨W, hfd, hdim, fun u => by simpa only [zero_mul] using hW u⟩
    simpa only [hz, Complex.ofReal_zero, zero_mul] using
      finiteCopy_common_eigenfunction_of_finite_trial D F V h k ht
  · let := (finiteSpectralData F V).eigenbasisIndex_infinite hf
    have hz := (finiteCopy_infinite_zero_iff_index_interval F V n).mpr ⟨hFI, hFN⟩
    have ht : ∃ W : Submodule ℂ (finiteH1Domain D), FiniteDimensional ℂ W ∧
        Module.finrank ℂ W = n + 1 ∧ ∀ u : W,
        (finiteH1Jacobi D V u u).re ≤
          (finiteSpectralData F V).infiniteReciprocalShift (V.C + 1) n *
            ‖finiteH1WeightedValue D u‖ ^ 2 := by
      rw [hz]
      exact ⟨W, hfd, hdim, fun u => by simpa only [zero_mul] using hW u⟩
    simpa only [hz, Complex.ofReal_zero, zero_mul] using
      finiteCopy_common_eigenfunction_of_infinite_trial D F V h n ht

end KsIndex.Spectral
