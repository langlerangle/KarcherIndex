module

public import KsIndexLean.SectorL2Unitary
public import KsIndexLean.InvolutionSpectralSplit

@[expose] public section


noncomputable section
namespace KsIndex.SectorIndex
open KsIndex.Sector KsIndex.SectorForm KsIndex.InvariantHermitian

abbrev sectorNegativeSpace (α : ℝ) (X : Submodule ℂ Domς) [FiniteDimensional ℂ X] :=
  negativeSpectralSpace (sectorL2HullOperator α X)

def sectorNegativeInvolution (α : ℝ) (X : Submodule ℂ Domς) [FiniteDimensional ℂ X] :
    Module.End ℂ (sectorNegativeSpace α X) :=
  negativeSpectralInvolution (sectorL2HullOperator α X) (sectorL2HullInvolution α X)
    (sectorL2HullOperator_commutes α X)

lemma sectorNegativeSpace_negative (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] (u : sectorNegativeSpace α X) (hu : u ≠ 0) :
    NQform α ((sectorHullL2Equiv α X).symm u.val).val.val < 0 := by
  rw [← sectorL2HullOperator_energy]
  apply negativeSpectralSpace_negative _ (sectorL2HullOperator_symmetric α X) u.property
  exact fun h => hu (Subtype.ext h)

/-- The original trial space has an injective, energy-preserving map into L² hull coordinates. -/
def sectorTrialL2Map (α : ℝ) (X : Submodule ℂ Domς) : X →ₗ[ℂ] sectorL2Hull α X :=
  (sectorHullL2Equiv α X).toLinearMap.comp (intoHull (sectorInvolution α) X)

lemma sectorTrialL2Map_injective (α : ℝ) (X : Submodule ℂ Domς) :
    Function.Injective (sectorTrialL2Map α X) :=
  (sectorHullL2Equiv α X).injective.comp (intoHull_injective _ _)

lemma sectorTrialL2Map_energy (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] (u : X) :
    (inner ℂ (sectorTrialL2Map α X u)
      (sectorL2HullOperator α X (sectorTrialL2Map α X u))).re = NQform α u.val.val := by
  rw [sectorL2HullOperator_energy]
  simp only [sectorTrialL2Map, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

lemma sectorTrial_finrank_le_negativeSpace (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X]
    (hX : ∀ u : X, u ≠ 0 → NQform α u.val.val < 0) :
    Module.finrank ℂ X ≤ Module.finrank ℂ (sectorNegativeSpace α X) := by
  let f := sectorTrialL2Map α X
  have hY : ∀ u : LinearMap.range f, u ≠ 0 →
      (inner ℂ u.val (sectorL2HullOperator α X u.val)).re < 0 := by
    intro u hu
    obtain ⟨x, hx⟩ := u.property
    have hx0 : x ≠ 0 := by
      intro hz
      apply hu
      apply Subtype.ext
      change u.val = 0
      rw [← hx, hz, map_zero]
    rw [← hx, sectorTrialL2Map_energy]
    exact hX x hx0
  have hd := negative_trial_finrank_le_negativeSpectralSpace (sectorL2HullOperator α X)
    (sectorL2HullOperator_symmetric α X) (LinearMap.range f) hY
  rwa [LinearMap.finrank_range_of_inj (sectorTrialL2Map_injective α X)] at hd

lemma sectorNegativeSpace_finrank_split (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] :
    Module.finrank ℂ (sectorNegativeSpace α X) =
      Module.finrank ℂ (Module.End.eigenspace (sectorNegativeInvolution α X) 1) +
      Module.finrank ℂ (Module.End.eigenspace (sectorNegativeInvolution α X) (-1)) :=
  involution_finrank_split _ (negativeSpectralInvolution_involutive _ _ _
    (sectorL2HullInvolution_involutive α X))

lemma sectorTrial_finrank_le_spectral_blocks (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X]
    (hX : ∀ u : X, u ≠ 0 → NQform α u.val.val < 0) :
    Module.finrank ℂ X ≤
      Module.finrank ℂ (Module.End.eigenspace (sectorNegativeInvolution α X) 1) +
      Module.finrank ℂ (Module.End.eigenspace (sectorNegativeInvolution α X) (-1)) := by
  rw [← sectorNegativeSpace_finrank_split]
  exact sectorTrial_finrank_le_negativeSpace α X hX

end KsIndex.SectorIndex
