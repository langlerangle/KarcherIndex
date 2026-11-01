module

public import KsIndexLean.TrivialCharacterIndex
public import KsIndexLean.StaircaseArithmetic

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.NegativeDensity

/-- Separate the proved zero-phase contribution from the actual interior
joint sectors. No circle adapter is assumed for this identity. -/
theorem indSurface_three_phase_sum (m : ℕ) [NeZero m] :
    Surface.indSurface 3 m = 3 + ∑ n ∈ Finset.Ico 1 m,
      ∑ j : Fin 3, KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m)
        (paperSmoothJointSector m n j.val) := by
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [SurfaceSym.indSurface_eq_sum_sectors (by decide : 2 ≤ 3), Finset.sum_comm]
  change (∑ n : Fin m, ∑ j : Fin 3, KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m)
    (paperSmoothJointSector m n.val j.val)) = _
  rw [Fin.sum_univ_eq_sum_range (fun n => ∑ j : Fin 3,
    KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m n j.val)),
    ← Finset.sum_range_add_sum_Ico _ hm]
  simp only [Finset.sum_range_one, paperSmooth_zeroPhase_total_index]

/-- Separate the nontrivial-character contributions from the constant
contributions on the original smooth carrier. -/
theorem indSurface_three_unresolved_sum (m : ℕ) [NeZero m] :
    Surface.indSurface 3 m = 3 + ∑ n ∈ Finset.Ico 1 m,
      (2 + KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m n 1) +
        KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m n 2)) := by
  rw [indSurface_three_phase_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one]
  rw [paperSmooth_nonzeroPhase_trivial_index m n
    (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2]
  rfl

/-- Assemble the index from supplied nontrivial-character sector counts. -/
theorem indSurface_three_eq_model_of_sector_counts (m : ℕ) [NeZero m]
    (hcounts : ∀ n, 0 < n → n < m → ∀ j, j = 1 ∨ j = 2 →
      KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m n j) =
        (KsIndex.Staircase.phaseCount ((n : ℝ) / m) : ℕ∞)) :
    Surface.indSurface 3 m = (KsIndex.Staircase.modelIndex m : ℕ∞) := by
  rw [indSurface_three_unresolved_sum]
  unfold KsIndex.Staircase.modelIndex
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have h0 := (Finset.mem_Ico.mp hn).1
  have h1 := (Finset.mem_Ico.mp hn).2
  rw [hcounts n h0 h1 1 (Or.inl rfl), hcounts n h0 h1 2 (Or.inr rfl)]
  rw [two_mul]
  ac_rfl

/-- Closed index formula conditional on the two sector counts. -/
theorem indSurface_three_floor_of_sector_counts (m : ℕ) [NeZero m]
    (hcounts : ∀ n, 0 < n → n < m → ∀ j, j = 1 ∨ j = 2 →
      KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m n j) =
        (KsIndex.Staircase.phaseCount ((n : ℝ) / m) : ℕ∞)) :
    Surface.indSurface 3 m =
      ((6 * m - 4 * ⌊(m : ℝ) * KsIndex.Staircase.alphaStar⌋₊ - 3 : ℕ) : ℕ∞) := by
  rw [indSurface_three_eq_model_of_sector_counts m hcounts,
    KsIndex.Staircase.modelIndex_eq_floor m (Nat.pos_of_ne_zero (NeZero.ne m))]

/-- Assemble the index from the actual pair-H1 slit counts, using
`paperSmoothSector_index_eq_slit` to transport the smooth-sector index. -/
theorem indSurface_three_eq_model_of_slit_counts (m : ℕ) [NeZero m]
    (hslit : ∀ n, 0 < n → n < m → ∀ j, j = 1 ∨ j = 2 →
      negativeIndex (fun u : paperSlitCharacterDomain ((n : ℝ) / m) j =>
        (weakJacobi (surfacePotential 3) u.val.1 u.val.1 +
          weakJacobi (surfacePotential 3) u.val.2 u.val.2).re) =
        (KsIndex.Staircase.phaseCount ((n : ℝ) / m) : ℕ∞)) :
    Surface.indSurface 3 m = (KsIndex.Staircase.modelIndex m : ℕ∞) := by
  apply indSurface_three_eq_model_of_sector_counts
  intro n hn hnm j hj
  exact (paperSmoothSector_index_eq_slit m n j).trans (hslit n hn hnm j hj)

/-- The same explicit adapter input yields the closed formula, including
sampled threshold endpoints through the existing open-band arithmetic. -/
theorem indSurface_three_floor_of_slit_counts (m : ℕ) [NeZero m]
    (hslit : ∀ n, 0 < n → n < m → ∀ j, j = 1 ∨ j = 2 →
      negativeIndex (fun u : paperSlitCharacterDomain ((n : ℝ) / m) j =>
        (weakJacobi (surfacePotential 3) u.val.1 u.val.1 +
          weakJacobi (surfacePotential 3) u.val.2 u.val.2).re) =
        (KsIndex.Staircase.phaseCount ((n : ℝ) / m) : ℕ∞)) :
    Surface.indSurface 3 m =
      ((6 * m - 4 * ⌊(m : ℝ) * KsIndex.Staircase.alphaStar⌋₊ - 3 : ℕ) : ℕ∞) := by
  rw [indSurface_three_eq_model_of_slit_counts m hslit,
    KsIndex.Staircase.modelIndex_eq_floor m (Nat.pos_of_ne_zero (NeZero.ne m))]

/-- With one period there are no interior phases, so no adapter is needed. -/
theorem indSurface_three_one_eq_three : Surface.indSurface 3 1 = 3 := by
  rw [indSurface_three_unresolved_sum]
  simp

end KsIndex.Spectral
