module

public import KsIndexLean.SectorNegativeSpectralSpace
public import KsIndexLean.FormIndexDensity

@[expose] public section


noncomputable section
namespace KsIndex.SectorIndex
open KsIndex.SectorReduce KsIndex.Sector KsIndex.SectorForm KsIndex.InvariantHermitian KsIndex.FormIndex
open KsIndex.NegativeDensity

/-- Recover the actual graph-domain coefficient function from its L² hull image. -/
def sectorHullCoefficients (α : ℝ) (X : Submodule ℂ Domς) :
    sectorL2Hull α X →ₗ[ℂ] (Idx → ℂ) :=
  Domς.subtype.comp ((sectorInvariantHull α X).subtype.comp
    (sectorHullL2Equiv α X).symm.toLinearMap)

lemma sectorHullCoefficients_injective (α : ℝ) (X : Submodule ℂ Domς) :
    Function.Injective (sectorHullCoefficients α X) :=
  Subtype.val_injective.comp (Subtype.val_injective.comp (sectorHullL2Equiv α X).symm.injective)

lemma sectorHullCoefficients_involution (α : ℝ) (X : Submodule ℂ Domς)
    (u : sectorL2Hull α X) :
    sectorHullCoefficients α X (sectorL2HullInvolution α X u) =
      rop α (sectorHullCoefficients α X u) := by
  change ((sectorHullL2Equiv α X).symm (sectorHullL2Equiv α X
    (sectorHullInvolution α X ((sectorHullL2Equiv α X).symm u)))).val.val = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

def sectorSpectralBlockMap (α : ℝ) (X : Submodule ℂ Domς) [FiniteDimensional ℂ X]
    (μ : ℂ) : Module.End.eigenspace (sectorNegativeInvolution α X) μ →ₗ[ℂ] (Idx → ℂ) :=
  (sectorHullCoefficients α X).comp ((sectorNegativeSpace α X).subtype.comp
    (Module.End.eigenspace (sectorNegativeInvolution α X) μ).subtype)

lemma sectorSpectralBlockMap_injective (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] (μ : ℂ) : Function.Injective (sectorSpectralBlockMap α X μ) :=
  (sectorHullCoefficients_injective α X).comp (Subtype.val_injective.comp Subtype.val_injective)

lemma sectorSpectralBlockMap_eigen (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] (μ : ℂ)
    (u : Module.End.eigenspace (sectorNegativeInvolution α X) μ) :
    rop α (sectorSpectralBlockMap α X μ u) = μ • sectorSpectralBlockMap α X μ u := by
  have h := congrArg (fun v : sectorNegativeSpace α X => sectorHullCoefficients α X v.val)
    (Module.End.mem_eigenspace_iff.mp u.property)
  change sectorHullCoefficients α X (sectorL2HullInvolution α X u.val.val) =
    sectorHullCoefficients α X (μ • u.val.val) at h
  rwa [sectorHullCoefficients_involution, map_smul] at h

lemma sectorSpectralBlock_finrank_le (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] (μ : ℂ) (D : Submodule ℂ (Idx → ℂ))
    (hD : ∀ u, sectorSpectralBlockMap α X μ u ∈ D) :
    (Module.finrank ℂ (Module.End.eigenspace (sectorNegativeInvolution α X) μ) : ℕ∞) ≤
      formIndex (NQform α) D := by
  let f := sectorSpectralBlockMap α X μ
  have hneg : NegOn (NQform α) D (LinearMap.range f) := by
    constructor
    · rintro v ⟨u, rfl⟩
      exact hD u
    · rintro v ⟨u, rfl⟩ hv
      apply sectorNegativeSpace_negative α X u.val
      intro hz
      have hu : u = 0 := Subtype.ext hz
      exact hv (by rw [hu, map_zero])
  rw [← LinearMap.finrank_range_of_inj (sectorSpectralBlockMap_injective α X μ)]
  exact le_iSup_of_le (LinearMap.range f) (le_iSup_of_le hneg
    (le_iSup_of_le (inferInstance : FiniteDimensional ℂ (LinearMap.range f)) le_rfl))

/-- The spectral plus block lies in Dcot and the minus block lies in Dtan. -/
lemma sectorTrial_finrank_le_block_indices (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X]
    (hX : ∀ u : X, u ≠ 0 → NQform α u.val.val < 0) :
    (Module.finrank ℂ X : ℕ∞) ≤
      formIndex (NQform α) (Dtan α) + formIndex (NQform α) (Dcot α) := by
  have hp := sectorSpectralBlock_finrank_le α X 1 (Dcot α) (by
    intro u
    refine ⟨((sectorHullL2Equiv α X).symm u.val.val).val.property, ?_⟩
    simpa only [one_smul] using sectorSpectralBlockMap_eigen α X 1 u)
  have hm := sectorSpectralBlock_finrank_le α X (-1) (Dtan α) (by
    intro u
    refine ⟨((sectorHullL2Equiv α X).symm u.val.val).val.property, ?_⟩
    simpa only [neg_one_smul] using sectorSpectralBlockMap_eigen α X (-1) u)
  have hd := sectorTrial_finrank_le_spectral_blocks α X hX
  have hd' : (Module.finrank ℂ X : ℕ∞) ≤
      (Module.finrank ℂ (Module.End.eigenspace (sectorNegativeInvolution α X) 1) : ℕ∞) +
      (Module.finrank ℂ (Module.End.eigenspace (sectorNegativeInvolution α X) (-1)) : ℕ∞) := by
    exact_mod_cast hd
  exact hd'.trans ((add_le_add hp hm).trans_eq (add_comm _ _))

/-- Paper-route subadditivity, using a finite invariant hull and its negative spectrum.
No rank-one bound on either block is needed. -/
theorem formIndex_le_blocks_spectral (α : ℝ) :
    formIndex (NQform α) Domς ≤
      formIndex (NQform α) (Dtan α) + formIndex (NQform α) (Dcot α) := by
  rw [formIndex_eq_negativeIndex]
  unfold negativeIndex
  refine iSup_le fun X => iSup_le fun hX => iSup_le fun hfin => ?_
  let := hfin
  exact sectorTrial_finrank_le_block_indices α X (fun u hu =>
    hX u.val u.property (fun hz => hu (Subtype.ext hz)))

/-- The paper's spectral proof of block index additivity, valid for every phase. -/
theorem formIndex_blocks_eq_spectral (α : ℝ) :
    formIndex (NQform α) Domς =
      formIndex (NQform α) (Dtan α) + formIndex (NQform α) (Dcot α) :=
  le_antisymm (formIndex_le_blocks_spectral α) (formIndex_Dtan_add_Dcot_le α)

/-- Circle-index transport using the spectral companion rather than rank-one subadditivity. -/
theorem formIndex_NQform_Domς_spectral (α : ℝ)
    (hαT : (1 : ℝ) + Real.cos (α * Real.pi) ≠ 0)
    (hαC : (1 : ℝ) - Real.cos (α * Real.pi) ≠ 0) :
    formIndex (NQform α) Domς = Statements.ind (coefT α) + Statements.ind (coefC α) := by
  rw [formIndex_blocks_eq_spectral, formIndex_NQform_Dtan α hαT,
    formIndex_NQform_Dcot α hαC]

end KsIndex.SectorIndex
