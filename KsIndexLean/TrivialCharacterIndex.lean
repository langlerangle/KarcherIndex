module

public import KsIndexLean.ZeroPhaseReflectionIndex
public import KsIndexLean.SlitThirdEigenvalue

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.NegativeDensity

/-- The original smooth trivial-rotation sector has index two at every
nonzero sampled translation phase. The sharp slit bracketing theorem includes
its equality-case exclusion, rather than merely an upper bound. -/
theorem paperSmooth_nonzeroPhase_trivial_index (m n : ℕ) [NeZero m]
    (hn : 0 < n) (hnm : n < m) :
    KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m n 0) = 2 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have h0 : (0 : ℝ) < (n : ℝ) / m := div_pos (by exact_mod_cast hn) hm
  have h1 : (n : ℝ) / m < 1 := (div_lt_one hm).mpr (by exact_mod_cast hnm)
  exact (paperSmoothSector_index_eq_slit m n 0).trans
    ((pairWeakIndex_eq_pair_negativeIndex (paperSlitCharacterDomain ((n : ℝ) / m) 0)
      (surfacePotential 3)).symm.trans (three_paperSlit_zero_index_two h0 h1))

/-- Fin-indexed spelling for the existing translation-sector decomposition. -/
theorem paperSmooth_sampled_trivial_index (m : ℕ) [NeZero m] (n : Fin m) :
    KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m n.val 0) =
      if n.val = 0 then 1 else 2 := by
  split_ifs with h
  · rw [h]
    exact paperSmooth_zeroPhase_sector_index m (by decide : 0 < 3)
  · exact paperSmooth_nonzeroPhase_trivial_index m n.val (Nat.pos_of_ne_zero h) n.isLt

/-- The nonzero translation phases contribute two each in rotation character zero. -/
theorem paperSmooth_nonzeroPhase_trivial_sum (m : ℕ) [NeZero m] :
    (∑ n ∈ Finset.Ico 1 m, KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m)
      (paperSmoothJointSector m n 0)) = (2 * (m - 1) : ℕ) := by
  have h : ∀ n ∈ Finset.Ico 1 m,
      KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m n 0) = 2 := by
    intro n hn
    exact paperSmooth_nonzeroPhase_trivial_index m n (Finset.mem_Ico.mp hn).1
      (Finset.mem_Ico.mp hn).2
  rw [Finset.sum_congr rfl h, Finset.sum_const, Nat.card_Ico]
  simp [nsmul_eq_mul, Nat.cast_mul, mul_comm]

end KsIndex.Spectral
