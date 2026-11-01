module

public import KsIndexLean.PaperSectorParameters
public import KsIndexLean.PaperSlitCharacterCoordinates
public import KsIndexLean.IndexCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.NegativeDensity

/-- Repackage an intersection as a subspace of the first subspace. -/
def intersectionNestedEquiv {E : Type*} [AddCommGroup E] [Module ℂ E]
    (D C : Submodule ℂ E) : ↥(D ⊓ C) ≃ₗ[ℂ] C.comap D.subtype where
  toFun u := ⟨⟨u.val, u.property.1⟩, u.property.2⟩
  invFun u := ⟨u.val.val, u.val.property, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Flatten the phase/character intersection without changing the chart field. -/
def paperSphereCharacterFlatten (α : ℝ) (j : ℕ) :
    PaperSphereSector α j ≃ₗ[ℂ] paperSphericalPhaseCharacter α j :=
  intersectionNestedEquiv _ _

/-- Actual weak chain-to-slit coordinates, with the paper's unchanged character. -/
def paperChainSlitEquiv (m n j : ℕ) [NeZero m] :
    PaperChainSector m n j ≃ₗ[ℂ] paperSlitCharacterDomain ((n : ℝ) / m) j :=
  ((paperRationalSectorEquiv m n j).toLinearEquiv.trans
    (paperSphereCharacterFlatten ((n : ℝ) / m) j)).trans
      (paperSlitCharacterSphereEquiv ((n : ℝ) / m) j).symm

/-- The equivalence extracts upper/lower = copy1/copy0; no character conjugation. -/
lemma paperChainSlitEquiv_coordinates (m n j : ℕ) [NeZero m]
    (u : PaperChainSector m n j) :
    (paperChainSlitEquiv m n j u).val =
      (chainChartCoordinatesCLM 3 m u.val.val 1,
       chainChartCoordinatesCLM 3 m u.val.val 0) := by
  have hc0 : paperPhase ((n : ℝ) / m) ≠ 0 := Complex.exp_ne_zero _
  let v : paperSlitCharacterDomain ((n : ℝ) / m) j :=
    ⟨(chainPhasePairLinearMap 3 m (paperPhase ((n : ℝ) / m)) u.val).val,
      (chainPhasePairLinearMap 3 m (paperPhase ((n : ℝ) / m)) u.val).property,
      (chainPhase_character_iff_pair 3 m _ _ (paperRotation_root 3 (by decide)) _
        u.val).mp u.property⟩
  have he : paperChainSlitEquiv m n j u = v := by
    apply (paperSlitCharacterSphereEquiv ((n : ℝ) / m) j).injective
    change (paperSlitCharacterSphereEquiv ((n : ℝ) / m) j)
      ((paperSlitCharacterSphereEquiv ((n : ℝ) / m) j).symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    apply Subtype.ext
    apply sphereDiskCoordinates_injective (isOpen_boundaryArc 3 1)
    change sphereDiskCoordinatesCLM (isOpen_boundaryArc 3 1)
      (chainPhaseSphereLinearIsometryEquiv 3 m _ (paperRationalPhase_root m n) u.val).val =
      sphereDiskCoordinatesCLM (isOpen_boundaryArc 3 1)
        (upperLowerSlitToSphere 3 (paperPhase ((n : ℝ) / m)) hc0
          (chainPhasePairLinearMap 3 m _ u.val)).val
    rw [chainPhaseSphere_equiv_agrees 3 m _ (paperRationalPhase_root m n) hc0]
    exact (chainPhaseToSphere_coordinates 3 m _ hc0 u.val).trans
      (upperLowerSlitToSphere_coordinates 3 _ hc0
        (chainPhasePairLinearMap 3 m _ u.val)).symm
  rw [he]
  rfl

/-- Exact polarized Jacobi form identity; the chain has m periods. -/
lemma paperChainSlitEquiv_jacobi (m n j : ℕ) [NeZero m]
    (V : BoundedRealPotential) (u v : PaperChainSector m n j) :
    chainChartJacobi 3 m V u.val.val v.val.val = (m : ℂ) *
      (weakJacobi V (paperChainSlitEquiv m n j u).val.1
        (paperChainSlitEquiv m n j v).val.1 +
       weakJacobi V (paperChainSlitEquiv m n j u).val.2
        (paperChainSlitEquiv m n j v).val.2) := by
  rw [paperChainSlitEquiv_coordinates, paperChainSlitEquiv_coordinates]
  exact chainPhase_jacobi_factor 3 m _ (paperRationalPhase_root m n) V u.val v.val

/-- Positive form scaling and a genuine equivalence preserve the weak-sector index.
This does not assert smooth Surface.Dom density or bounded Jacobi regularity. -/
lemma paperChainSlitEquiv_negativeIndex (m n j : ℕ) [NeZero m]
    (V : BoundedRealPotential) :
    negativeIndex (fun u : PaperChainSector m n j =>
      (chainChartJacobi 3 m V u.val.val u.val.val).re) =
    negativeIndex (fun u : paperSlitCharacterDomain ((n : ℝ) / m) j =>
      (weakJacobi V u.val.1 u.val.1 + weakJacobi V u.val.2 u.val.2).re) := by
  let Q : paperSlitCharacterDomain ((n : ℝ) / m) j → ℝ := fun u =>
    (weakJacobi V u.val.1 u.val.1 + weakJacobi V u.val.2 u.val.2).re
  have hform (u : PaperChainSector m n j) :
      (chainChartJacobi 3 m V u.val.val u.val.val).re =
        (m : ℝ) * Q (paperChainSlitEquiv m n j u) := by
    rw [paperChainSlitEquiv_jacobi]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Q]
  have hQ : Q 0 = 0 := by
    have hz : weakJacobi V 0 0 = 0 := by
      have h := weakJacobi_add_left V 0 0 0
      simp only [add_zero] at h
      linear_combination -h
    change (weakJacobi V 0 0 + weakJacobi V 0 0).re = 0
    rw [hz, add_zero, Complex.zero_re]
  rw [show (fun u : PaperChainSector m n j =>
      (chainChartJacobi 3 m V u.val.val u.val.val).re) =
      (fun u => (m : ℝ) * Q (paperChainSlitEquiv m n j u)) from funext hform]
  exact (negativeIndex_pos_mul _ (m : ℝ)
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))).trans
      (negativeIndex_linearEquiv (paperChainSlitEquiv m n j) Q hQ)

end KsIndex.Spectral
