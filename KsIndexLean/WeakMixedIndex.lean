module

public import KsIndexLean.WeakHemisphereIndex
public import KsIndexLean.SeamLowerMixed
public import KsIndexLean.GramDip

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.SingleDisk KsIndex.SingleDiskBridge

/-- The proved core screw congruence transfers index equality to full weak domains.
This does not assert a nullity transport. -/
lemma oppositeMixed_weak_index {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    diskWeakIndex (mixedCharacterDomain k r false true) (surfacePotential k) =
      diskWeakIndex (mixedCharacterDomain k r true false) (surfacePotential k) := by
  rw [mixedCharacter_weak_index_eq_seamNat hk, mixedCharacter_weak_index_eq_seamNat hk]
  exact seamNat_mixed hk r

lemma mixedND_weak_index_one {k r : ℕ} (hk : 3 ≤ k) (hr : r < k) :
    diskWeakIndex (mixedCharacterDomain k r true false) (surfacePotential k) = 1 := by
  rw [mixedCharacter_weak_index_eq_seamNat (by omega)]
  by_cases hz : r = 0
  · subst r
    exact seamNat_true_false_zero hk (c := 1 / 2) (by norm_num) le_rfl
  · exact KsIndex.SeamLowerMixed.seamNat_mixed_eq_one hk (by omega) (by omega)

lemma mixedDN_weak_index_one {k r : ℕ} (hk : 3 ≤ k) (hr : r < k) :
    diskWeakIndex (mixedCharacterDomain k r false true) (surfacePotential k) = 1 := by
  rw [oppositeMixed_weak_index (by omega), mixedND_weak_index_one hk hr]

lemma three_slitDirichlet_index_one {j : ℕ} (hj : j < 3) :
    pairWeakIndex (paperSlitDirichletCharacterDomain j) (surfacePotential 3) = 1 := by
  rw [three_slitDirichlet_index_reduction, mixedND_weak_index_one (by decide) hj]

lemma three_slitNeumann_index_two {j : ℕ} (hj : j < 3) :
    pairWeakIndex (paperSlitNeumannCharacterDomain j) (surfacePotential 3) = 2 := by
  rw [three_slitNeumann_index_reduction hj, mixedDN_weak_index_one (by decide) hj]
  norm_num

lemma pairWeakIndex_mono (D F : Submodule ℂ DiskPairH1)
    (V : BoundedRealPotential) (h : D ≤ F) : pairWeakIndex D V ≤ pairWeakIndex F V := by
  have hz : (finiteH1Jacobi (pairFiniteDomain F) V 0 0).re = 0 := by
    change (finiteJacobiForm (pairFiniteDomain F) V 0 0).re = 0
    exact congrArg
      (fun f : finiteH1Domain (pairFiniteDomain F) →L[ℂ] ℂ => (f 0).re)
      ((finiteJacobiForm (pairFiniteDomain F) V).toLinearMap.map_zero)
  exact KsIndex.NegativeDensity.negativeIndex_pullback_le
    (fun u : finiteH1Domain (pairFiniteDomain F) => (finiteH1Jacobi (pairFiniteDomain F) V u u).re)
    hz (finiteH1Inclusion (pairFiniteDomain_mono h))

/-- The actual weak phase problem has between one and two negative directions
in each of the three characters. No rationality or spectral dimension assumption. -/
lemma three_paperSlit_phase_index_bounds (α : ℝ) {j : ℕ} (hj : j < 3) :
    1 ≤ pairWeakIndex (paperSlitCharacterDomain α j) (surfacePotential 3) ∧
      pairWeakIndex (paperSlitCharacterDomain α j) (surfacePotential 3) ≤ 2 := by
  constructor
  · rw [← three_slitDirichlet_index_one hj]
    exact pairWeakIndex_mono _ _ _ (paperSlitDirichletCharacter_le_phase α j)
  · rw [← three_slitNeumann_index_two hj]
    exact pairWeakIndex_mono _ _ _ (paperSlitCharacter_le_Neumann α j)

end KsIndex.Spectral
