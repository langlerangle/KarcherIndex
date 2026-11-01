module

public import KsIndexLean.K3IndexAssembly
public import KsIndexLean.PaperSlitIndexAssembly
public import KsIndexLean.SectorPhase

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.NegativeDensity

/-- Actual slit-pair index at an interior phase, for either nontrivial character. -/
theorem paperSlit_index_eq_phaseCount (α : ℝ) (h0 : 0 < α) (h1 : α < 1)
    {j : ℕ} (hj : KsIndex.PaperSlitAdapter.SectorClass j) :
    negativeIndex (fun u : paperSlitCharacterDomain α j =>
      (weakJacobi (surfacePotential 3) u.val.1 u.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 u.val.2).re) =
      (KsIndex.Staircase.phaseCount α : ℕ∞) :=
  (KsIndex.PaperSlitAdapter.paperSlit_index_eq_sectorClass α h0 h1 hj).trans
    (KsIndex.SectorPhase.sector_index_eq_phaseCount α h0 h1)

/-- The actual sampled slit sectors discharge the conditional index assembly. -/
lemma paperSlit_sampled_index_eq_phaseCount (m : ℕ) [NeZero m]
    (n : ℕ) (hn : 0 < n) (hnm : n < m) (j : ℕ) (hj : j = 1 ∨ j = 2) :
    negativeIndex (fun u : paperSlitCharacterDomain ((n : ℝ) / m) j =>
      (weakJacobi (surfacePotential 3) u.val.1 u.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 u.val.2).re) =
      (KsIndex.Staircase.phaseCount ((n : ℝ) / m) : ℕ∞) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  apply paperSlit_index_eq_phaseCount _ (div_pos (by exact_mod_cast hn) hm)
    ((div_lt_one hm).mpr (by exact_mod_cast hnm))
  rcases hj with rfl | rfl <;> norm_num [KsIndex.PaperSlitAdapter.SectorClass]

/-- Unconditional index formula for the formal disk-chain surface carrier at k=3.
The equality with the geometric EW quotient index is supplied downstream by
`geometricIndex_eq_model` in `KarcherGeometricInvariants`. -/
theorem indSurface_three_eq_model (m : ℕ) [NeZero m] :
    Surface.indSurface 3 m = (KsIndex.Staircase.modelIndex m : ℕ∞) :=
  indSurface_three_eq_model_of_slit_counts m (paperSlit_sampled_index_eq_phaseCount m)

/-- Closed index formula, including sampled threshold endpoints with their strict
negative-index convention. No nonresonance assumption is imposed. -/
theorem indSurface_three_eq_floor (m : ℕ) [NeZero m] :
    Surface.indSurface 3 m =
      ((6 * m - 4 * ⌊(m : ℝ) * KsIndex.Staircase.alphaStar⌋₊ - 3 : ℕ) : ℕ∞) :=
  indSurface_three_floor_of_slit_counts m (paperSlit_sampled_index_eq_phaseCount m)

end KsIndex.Spectral
