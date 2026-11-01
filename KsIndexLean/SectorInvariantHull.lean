module

public import KsIndexLean.InvariantHermitianHull
public import KsIndexLean.SectorIndex

@[expose] public section


noncomputable section
namespace KsIndex.SectorIndex
open KsIndex.CircleQ KsIndex.Sector KsIndex.SectorForm KsIndex.FormIndex
open KsIndex.InvariantHermitian

/-- The paper's involution as an endomorphism of its ACTUAL graph domain. -/
def sectorInvolution (α : ℝ) : Module.End ℂ Domς where
  toFun u := ⟨rop α u.val, rop_mem_Domς α u.property⟩
  map_add' u v := Subtype.ext (rop_add α (sectorL2_of_mem_Domς u.property)
    (sectorL2_of_mem_Domς v.property))
  map_smul' c u := Subtype.ext (rop_smul α c u.val)

lemma sectorInvolution_involutive (α : ℝ) : Function.Involutive (sectorInvolution α) := by
  intro u
  exact Subtype.ext (rop_involutive α (sectorL2_of_mem_Domς u.property))

/-- Exactly X + R_alpha X from the paper, not a maximal-negative-space substitute. -/
abbrev sectorInvariantHull (α : ℝ) (X : Submodule ℂ Domς) :=
  invariantHull (sectorInvolution α) X

def sectorHullInvolution (α : ℝ) (X : Submodule ℂ Domς) :
    Module.End ℂ (sectorInvariantHull α X) :=
  hullInvolution (sectorInvolution α) (sectorInvolution_involutive α) X

lemma sectorHullInvolution_involutive (α : ℝ) (X : Submodule ℂ Domς) :
    Function.Involutive (sectorHullInvolution α X) :=
  hullInvolution_involutive _ _ _

/-- The restricted Hermitian form retains the involution symmetry on the hull. -/
lemma sectorHull_form_invariant (α : ℝ) (X : Submodule ℂ Domς)
    (u v : sectorInvariantHull α X) :
    NBform α (sectorHullInvolution α X u).val.val (sectorHullInvolution α X v).val.val =
      NBform α u.val.val v.val.val :=
  NBform_rop α (sectorL2_of_mem_Domς u.val.property) (sectorL2_of_mem_Domς v.val.property)

/-- Every negative trial space embeds in its finite invariant hull, with
its dimension and negativity retained. -/
lemma sector_trial_into_hull (α : ℝ) (X : Submodule ℂ Domς)
    [FiniteDimensional ℂ X]
    (hX : ∀ u : X, u ≠ 0 → NQform α u.val.val < 0) :
    ∃ Y : Submodule ℂ (sectorInvariantHull α X),
      FiniteDimensional ℂ Y ∧ Module.finrank ℂ Y = Module.finrank ℂ X ∧
      ∀ u : Y, u ≠ 0 → NQform α u.val.val.val < 0 := by
  let f := intoHull (sectorInvolution α) X
  refine ⟨LinearMap.range f, inferInstance, LinearMap.finrank_range_of_inj
    (intoHull_injective _ _), ?_⟩
  intro u hu
  obtain ⟨x, hx⟩ := u.property
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    have hz : u.val = 0 := hx.symm.trans (map_zero f)
    exact hu (Subtype.ext hz)
  have he : u.val.val.val = x.val.val := congrArg (fun z => z.val.val) hx.symm
  rw [he]
  exact hX x hx0

end KsIndex.SectorIndex
