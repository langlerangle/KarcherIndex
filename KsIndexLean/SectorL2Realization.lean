module

public import KsIndexLean.SectorInvariantHull
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section


noncomputable section
namespace KsIndex.SectorIndex
open KsIndex.Sector KsIndex.SectorForm KsIndex.InvariantHermitian

/-- Unweighted physical Fourier coefficients: the paper's coefficient L² space. -/
abbrev SectorHilbert := lp (fun _ : Idx => ℂ) 2

lemma sector_mem_lp {u : Idx → ℂ} (hu : SectorL2 u) : Memℓp u 2 := by
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using Summable.sum (fun i : Idx => ‖u i‖ ^ 2) hu.1 hu.2

/-- The graph domain embeds injectively in coefficient L². -/
def sectorL2Embedding : Domς →ₗ[ℂ] SectorHilbert where
  toFun u := ⟨u.val, sector_mem_lp (sectorL2_of_mem_Domς u.property)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma sectorL2Embedding_apply (u : Domς) (i : Idx) :
    sectorL2Embedding u i = u.val i := rfl

lemma sectorL2Embedding_injective : Function.Injective sectorL2Embedding := by
  intro u v h
  apply Subtype.ext
  exact congrArg (fun z : SectorHilbert => (z : Idx → ℂ)) h

lemma sectorL2Embedding_norm_sq (u : Domς) :
    ‖sectorL2Embedding u‖ ^ 2 = normSqS u.val := by
  have h := lp.hasSum_norm (show (0 : ℝ) < (2 : ENNReal).toReal by norm_num)
    (sectorL2Embedding u)
  have hu := sectorL2_of_mem_Domς u.property
  have hs := Summable.tsum_sum (f := fun i : Idx => ‖u.val i‖ ^ 2) hu.1 hu.2
  have he : ‖sectorL2Embedding u‖ ^ 2 = ∑' i : Idx, ‖u.val i‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, sectorL2Embedding_apply] using h.tsum_eq.symm
  exact he.trans hs

/-- The invariant hull realized as a subspace of coefficient L². It is
finite-dimensional when the trial space `X` is finite-dimensional. -/
def sectorL2Hull (α : ℝ) (X : Submodule ℂ Domς) : Submodule ℂ SectorHilbert :=
  LinearMap.range (sectorL2Embedding.comp (sectorInvariantHull α X).subtype)

def sectorHullL2Equiv (α : ℝ) (X : Submodule ℂ Domς) :
    sectorInvariantHull α X ≃ₗ[ℂ] sectorL2Hull α X :=
  LinearEquiv.ofInjective _ (sectorL2Embedding_injective.comp Subtype.val_injective)

instance sectorL2Hull_finite (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] : FiniteDimensional ℂ (sectorL2Hull α X) :=
  (sectorHullL2Equiv α X).finiteDimensional

/-- The coefficient-normalized sector form, transported to the L² hull. -/
def sectorL2HullForm (α : ℝ) (X : Submodule ℂ Domς) :
    sectorL2Hull α X →ₗ⋆[ℂ] sectorL2Hull α X →ₗ[ℂ] ℂ where
  toFun u := {
    toFun := fun v => NBform α ((sectorHullL2Equiv α X).symm u).val.val
      ((sectorHullL2Equiv α X).symm v).val.val
    map_add' := fun v w => by
      simpa using NBform_add_right α ((sectorHullL2Equiv α X).symm u).val.property
        ((sectorHullL2Equiv α X).symm v).val.property
        ((sectorHullL2Equiv α X).symm w).val.property
    map_smul' := fun c v => by simp [NBform_smul_right] }
  map_add' u v := by
    ext w
    simpa using NBform_add_left α ((sectorHullL2Equiv α X).symm u).val.property
      ((sectorHullL2Equiv α X).symm v).val.property
      ((sectorHullL2Equiv α X).symm w).val.property
  map_smul' c u := by ext v; simp [NBform_smul_left]

/-- Riesz realizes the restricted paper form on the finite coefficient hull.
Continuity of each functional follows from finite dimensionality. -/
def sectorL2HullOperator (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] : Module.End ℂ (sectorL2Hull α X) :=
  (InnerProductSpace.toDual ℂ (sectorL2Hull α X)).symm.toLinearEquiv.toLinearMap.comp
    ((LinearMap.toContinuousLinearMap :
      (sectorL2Hull α X →ₗ[ℂ] ℂ) ≃ₗ[ℂ] sectorL2Hull α X →L[ℂ] ℂ).toLinearMap.comp
        (sectorL2HullForm α X))

lemma sectorL2HullOperator_represents_left (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] (u v : sectorL2Hull α X) :
    inner ℂ (sectorL2HullOperator α X u) v = sectorL2HullForm α X u v := by
  exact InnerProductSpace.toDual_symm_apply

lemma sectorL2HullOperator_represents (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] (u v : sectorL2Hull α X) :
    inner ℂ u (sectorL2HullOperator α X v) = sectorL2HullForm α X u v := by
  rw [← inner_conj_symm, sectorL2HullOperator_represents_left]
  change (starRingEnd ℂ) (NBform α _ _) = NBform α _ _
  rw [NBform_conj_symm, starRingEnd_self_apply]

lemma sectorL2HullOperator_symmetric (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] : (sectorL2HullOperator α X).IsSymmetric := by
  intro u v
  exact (sectorL2HullOperator_represents_left α X u v).trans
    (sectorL2HullOperator_represents α X u v).symm

/-- Exact diagonal energy, with no rescaling of the coefficient L² metric. -/
lemma sectorL2HullOperator_energy (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] (u : sectorL2Hull α X) :
    (inner ℂ u (sectorL2HullOperator α X u)).re =
      NQform α ((sectorHullL2Equiv α X).symm u).val.val := by
  rw [sectorL2HullOperator_represents]
  change (NBform α _ _).re = _
  rw [NBform_self, Complex.ofReal_re]

/-- The representing operator is canonical despite the use of Riesz choice. -/
lemma sectorL2HullOperator_unique (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X] (T : Module.End ℂ (sectorL2Hull α X))
    (hT : ∀ u v, inner ℂ u (T v) = sectorL2HullForm α X u v) :
    T = sectorL2HullOperator α X := by
  apply LinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  rw [hT, sectorL2HullOperator_represents]

end KsIndex.SectorIndex
