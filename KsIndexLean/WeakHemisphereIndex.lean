module

public import KsIndexLean.SlitReflectionIndex
public import KsIndexLean.D5IndexTransport
public import KsIndexLean.SeamNat
public import KsIndexLean.SeamPureD

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.SingleDisk KsIndex.SingleDiskBridge

/-- The core index theorem transfers to the full weak hemisphere. -/
lemma mixedCharacter_weak_index_eq_seamNat {k : ℕ} (hk : 2 ≤ k)
    (r : ℕ) (b1 b0 : Bool) :
    diskWeakIndex (mixedCharacterDomain k r b1 b0) (surfacePotential k) =
      seamNat k b1 b0 r :=
  (seamNat_eq_negativeIndex hk r b1 b0).symm

lemma pureDirichlet_weak_index_zero {k : ℕ} (hk : 3 ≤ k) (r : ℕ) :
    diskWeakIndex (mixedCharacterDomain k r false false) (surfacePotential k) = 0 := by
  rw [mixedCharacter_weak_index_eq_seamNat (by omega)]
  exact seamNat_pureD hk r

lemma pureNeumann_weak_index {k r : ℕ} (hk : 3 ≤ k) (hr : r < k) :
    diskWeakIndex (mixedCharacterDomain k r true true) (surfacePotential k) =
      neumannCount k (r : ZMod k) + (if (r : ZMod k) = 0 then 1 else 0) := by
  rw [mixedCharacter_weak_index_eq_seamNat (by omega)]
  exact seamNat_eq hk hr

lemma three_pureNeumann_weak_index {j : ℕ} (hj : j < 3) :
    diskWeakIndex (mixedCharacterDomain 3 j true true) (surfacePotential 3) = 1 := by
  rw [pureNeumann_weak_index (by decide) hj]
  interval_cases j
  · simp [neumannCount_zero (by decide : 3 ≤ 3)]
  · simp [neumannCount_one (by decide : 3 ≤ 3)]
  · rw [neumannCount_eq (by decide : 3 ≤ 3)]
    have hv : (2 : ZMod 3).val = 2 := by decide
    have hz : (2 : ZMod 3) ≠ 0 := by decide
    norm_num [hv, hz]

/-- The pure Neumann contribution is one in each character; this reduction leaves
the mixed hemisphere index explicit. -/
lemma three_slitNeumann_index_reduction {j : ℕ} (hj : j < 3) :
    pairWeakIndex (paperSlitNeumannCharacterDomain j) (surfacePotential 3) =
      1 + diskWeakIndex (mixedCharacterDomain 3 j false true) (surfacePotential 3) := by
  rw [paperSlitNeumannCharacter_index_mixed, three_pureNeumann_weak_index hj]

lemma three_slitDirichlet_index_reduction (j : ℕ) :
    pairWeakIndex (paperSlitDirichletCharacterDomain j) (surfacePotential 3) =
      diskWeakIndex (mixedCharacterDomain 3 j true false) (surfacePotential 3) := by
  rw [paperSlitDirichletCharacter_index_mixed, pureDirichlet_weak_index_zero (by decide), add_zero]

end KsIndex.Spectral
