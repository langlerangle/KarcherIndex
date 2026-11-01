module

public import KsIndexLean.ZeroEigenvalueLocation

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

set_option maxHeartbeats 800000 in
lemma pair_common_zero_of_index_interval
    (D F : Submodule ℂ DiskPairH1)
    [CompleteSpace (finiteH1Domain (pairFiniteDomain D))]
    [CompleteSpace (finiteH1Domain (pairFiniteDomain F))]
    (V : BoundedRealPotential) (h : D ≤ F) (n : ℕ)
    (hD : finiteCopyIndexNullity (pairFiniteDomain D) V = ((n + 1 : ℕ) : ℕ∞))
    (hFI : pairWeakIndex F V ≤ (n : ℕ∞))
    (hFN : (n : ℕ∞) < finiteCopyIndexNullity (pairFiniteDomain F) V) :
    ∃ u : D, u ≠ 0 ∧
      (∀ w : F, weakJacobi V u.val.1 w.val.1 + weakJacobi V u.val.2 w.val.2 = 0) ∧
      (∀ w : D, weakJacobi V u.val.1 w.val.1 + weakJacobi V u.val.2 w.val.2 = 0) := by
  obtain ⟨u, hne, hF, hD'⟩ := finiteCopy_common_zero_of_index_interval
    (pairFiniteDomain D) (pairFiniteDomain F) V (pairFiniteDomain_mono h) n hD hFI hFN
  refine ⟨pairHilbertCoordinates D u, ?_, ?_, ?_⟩
  · intro hz
    apply hne
    exact (pairHilbertCoordinates D).injective (hz.trans (map_zero _).symm)
  · intro w
    have hh := hF ((pairHilbertCoordinates F).symm w)
    rw [pairFiniteJacobi_eq, LinearEquiv.apply_symm_apply] at hh
    exact hh
  · intro w
    have hh := hD' ((pairHilbertCoordinates D).symm w)
    rw [pairFiniteJacobi_eq, LinearEquiv.apply_symm_apply] at hh
    exact hh

/-- A nontrivial phase cannot retain only one negative direction in character
zero: equality at the second eigenvalue would produce the excluded common
vertical Jacobi field. -/
lemma three_paperSlit_zero_index_not_le_one {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    ¬ pairWeakIndex (paperSlitCharacterDomain α 0) (surfacePotential 3) ≤ 1 := by
  intro hi
  have hd := three_slitDirichlet_index_add_nullity (by decide : 0 < 3)
  change finiteCopyIndexNullity (pairFiniteDomain (paperSlitDirichletCharacterDomain 0))
    (surfacePotential 3) = 2 at hd
  have hp := three_paperSlit_zero_index_add_nullity α
  obtain ⟨u, hne, hphase, hdir⟩ := pair_common_zero_of_index_interval
    (paperSlitDirichletCharacterDomain 0) (paperSlitCharacterDomain α 0)
    (surfacePotential 3) (paperSlitDirichletCharacter_le_phase α 0) 1 hd hi
    (by rw [hp]; norm_num)
  apply hne
  apply Subtype.ext
  exact paperSlitDirichlet_zero_common_kernel_zero h0 h1 u hdir
    (fun v hv => hphase ⟨v, hv⟩)

lemma three_paperSlit_zero_index_two {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    pairWeakIndex (paperSlitCharacterDomain α 0) (surfacePotential 3) = 2 := by
  have hb := (three_paperSlit_phase_index_bounds α (by decide : 0 < 3)).2
  have hn := three_paperSlit_zero_index_not_le_one h0 h1
  generalize pairWeakIndex (paperSlitCharacterDomain α 0) (surfacePotential 3) = x at *
  lift x to ℕ using (ne_top_of_le_ne_top (by simp) hb) with n
  have hb' : n ≤ 2 := by exact_mod_cast hb
  have hn' : ¬ n ≤ 1 := by exact_mod_cast hn
  have he : n = 2 := by omega
  exact_mod_cast he

lemma three_paperSlit_zero_nullity_zero {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    finiteCopyWeakNullity (pairFiniteDomain (paperSlitCharacterDomain α 0))
      (surfacePotential 3) = 0 := by
  have ht := three_paperSlit_zero_index_add_nullity α
  change pairWeakIndex (paperSlitCharacterDomain α 0) (surfacePotential 3) +
    (finiteCopyWeakNullity (pairFiniteDomain (paperSlitCharacterDomain α 0))
      (surfacePotential 3) : ℕ∞) = 2 at ht
  rw [three_paperSlit_zero_index_two h0 h1] at ht
  have hh : 2 + finiteCopyWeakNullity (pairFiniteDomain (paperSlitCharacterDomain α 0))
      (surfacePotential 3) = 2 := by exact_mod_cast ht
  omega

lemma three_paperSlit_nontrivial_total_ne_three {α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) {j : ℕ} (hj : j < 3) (hj0 : j ≠ 0) :
    finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α j))
      (surfacePotential 3) ≠ 3 := by
  intro ht
  have hn := three_slitNeumann_index_add_nullity hj
  change finiteCopyIndexNullity (pairFiniteDomain (paperSlitNeumannCharacterDomain j))
    (surfacePotential 3) = _ at hn
  have hn3 : finiteCopyIndexNullity (pairFiniteDomain (paperSlitNeumannCharacterDomain j))
      (surfacePotential 3) = 3 := by simpa only [if_neg hj0] using hn
  obtain ⟨u, hne, hN, _⟩ := pair_common_zero_of_index_interval
    (paperSlitCharacterDomain α j) (paperSlitNeumannCharacterDomain j)
    (surfacePotential 3) (paperSlitCharacter_le_Neumann α j) 2 ht
    (by rw [three_slitNeumann_index_two hj]; norm_num) (by rw [hn3]; norm_num)
  let v : paperSlitNeumannCharacterDomain j :=
    ⟨u, paperSlitCharacter_le_Neumann α j u.property⟩
  have hv : v.val = 0 := by
    interval_cases j
    · contradiction
    · exact paperSlitNeumann_one_phase_kernel_zero h0 h1 v hN u.property.1
    · exact paperSlitNeumann_two_phase_kernel_zero h0 h1 v hN u.property.1
  exact hne (Subtype.ext hv)

lemma three_paperSlit_nontrivial_index_add_nullity_le_two {α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) {j : ℕ} (hj : j < 3) (hj0 : j ≠ 0) :
    finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α j))
      (surfacePotential 3) ≤ 2 := by
  have hb := three_paperSlit_nontrivial_index_add_nullity_le_three α hj hj0
  have hn := three_paperSlit_nontrivial_total_ne_three h0 h1 hj hj0
  generalize finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α j))
    (surfacePotential 3) = x at *
  lift x to ℕ using (ne_top_of_le_ne_top (by simp) hb) with n
  have hb' : n ≤ 3 := by exact_mod_cast hb
  have hn' : n ≠ 3 := by exact_mod_cast hn
  have hh : n ≤ 2 := by omega
  exact_mod_cast hh

end KsIndex.Spectral
