module

public import KsIndexLean.SlitCommonZero

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

lemma finiteCopy_infinite_positive_of_indexNullity_le
    {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
    [Infinite (finiteSpectralData D V).eigenbasisIndex] (n : ℕ)
    (hn : finiteCopyIndexNullity D V ≤ (n : ℕ∞)) :
    0 < (finiteSpectralData D V).infiniteReciprocalShift (V.C + 1) n := by
  rw [finiteCopy_indexNullity_infinite] at hn
  have hc : finiteCopyNonpositiveCount D V ≤ n := by exact_mod_cast hn
  by_contra h
  have hh := (le_level_iff_lt_weakSpectralCount
    ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_monotone (V.C + 1)) 0 n).mp
      (le_of_not_gt h)
  exact (not_lt_of_ge hc) hh

lemma finiteCopy_finite_positive_of_indexNullity_le
    {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)]
    (n : Fin (Module.finrank ℂ (WeightedFiniteAmbient D)))
    (hn : finiteCopyIndexNullity D V ≤ (n.val : ℕ∞)) :
    0 < (finiteSpectralData D V).finiteReciprocalShift (V.C + 1) n := by
  rw [finiteCopy_indexNullity_finite] at hn
  have hc : (finiteSpectralData D V).finiteWeakCount (V.C + 1) 0 ≤ n.val := by exact_mod_cast hn
  by_contra h
  have hh := (finite_le_iff_lt_count
    ((finiteSpectralData D V).finiteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).finiteReciprocalShift_monotone (V.C + 1)) 0 n).mp
      (le_of_not_gt h)
  exact (not_lt_of_ge hc) hh

lemma three_paperSlit_index_add_nullity_le_two {α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) {j : ℕ} (hj : j < 3) :
    finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α j))
      (surfacePotential 3) ≤ 2 := by
  by_cases hz : j = 0
  · subst j
    exact (three_paperSlit_zero_index_add_nullity α).le
  · exact three_paperSlit_nontrivial_index_add_nullity_le_two h0 h1 hj hz

/-- The third eigenvalue is strictly positive in each actual phase character.
Eigenvalues are zero-indexed, so the third has index 2. -/
lemma three_paperSlit_infinite_third_positive {α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) {j : ℕ} (hj : j < 3)
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j))
      (surfacePotential 3)).eigenbasisIndex] :
    0 < (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j))
      (surfacePotential 3)).infiniteReciprocalShift ((surfacePotential 3).C + 1) 2 :=
  finiteCopy_infinite_positive_of_indexNullity_le _ _ 2
    (three_paperSlit_index_add_nullity_le_two h0 h1 hj)

/-- Finite-sector spelling retains the availability bound for the third
ordered eigenvalue; no fictitious eigenvalue is inserted in smaller sectors. -/
lemma three_paperSlit_finite_third_positive {α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) {j : ℕ} (hj : j < 3)
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitCharacterDomain α j)))]
    (hd : 2 < Module.finrank ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitCharacterDomain α j)))) :
    0 < (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j))
      (surfacePotential 3)).finiteReciprocalShift ((surfacePotential 3).C + 1) ⟨2, hd⟩ :=
  finiteCopy_finite_positive_of_indexNullity_le _ _ ⟨2, hd⟩
    (three_paperSlit_index_add_nullity_le_two h0 h1 hj)

/-- The k3 bracketing proposition on the actual weak slit character spaces. -/
lemma three_paperSlit_bracketing {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    pairWeakIndex (paperSlitCharacterDomain α 0) (surfacePotential 3) = 2 ∧
    finiteCopyWeakNullity (pairFiniteDomain (paperSlitCharacterDomain α 0))
      (surfacePotential 3) = 0 ∧
    ∀ j : ℕ, j < 3 →
      1 ≤ pairWeakIndex (paperSlitCharacterDomain α j) (surfacePotential 3) ∧
      finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α j))
        (surfacePotential 3) ≤ 2 :=
  ⟨three_paperSlit_zero_index_two h0 h1, three_paperSlit_zero_nullity_zero h0 h1,
    fun _j hj => ⟨(three_paperSlit_phase_index_bounds α hj).1,
      three_paperSlit_index_add_nullity_le_two h0 h1 hj⟩⟩

end KsIndex.Spectral
