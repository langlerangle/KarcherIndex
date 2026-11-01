module

public import KsIndexLean.PaperSmoothJointApproximation
public import KsIndexLean.PaperSmoothSectorIndex

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.NegativeDensity

lemma sesq_linear_pullback {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {B : F → F → ℂ}
    (hB : Sesq B) (L : E →ₗ[ℂ] F) (hL : Continuous L) :
    Sesq (fun u v => B (L u) (L v)) where
  addL u v w := by rw [map_add, hB.addL]
  addR u v w := by rw [map_add, hB.addR]
  smulL c u v := by rw [map_smul, hB.smulL]
  smulR c u v := by rw [map_smul, hB.smulR]
  conj u v := hB.conj _ _
  continuous := hB.continuous.comp ((hL.comp continuous_fst).prodMk (hL.comp continuous_snd))

lemma chainChart_jacobi_sesq (k m : ℕ) [NeZero m] (V : BoundedRealPotential) :
    Sesq (chainChartJacobi k m V) where
  addL := chainChartJacobi_add_left k m V
  addR := chainChartJacobi_add_right k m V
  smulL := chainChartJacobi_smul_left k m V
  smulR := chainChartJacobi_smul_right k m V
  conj u v := (chainChartJacobi_conj k m V v u).symm
  continuous := continuous_chainChartJacobi k m V

lemma paperChainSector_jacobi_sesq (m n j : ℕ) [NeZero m]
    (V : BoundedRealPotential) :
    Sesq (fun u v : PaperChainSector m n j => chainChartJacobi 3 m V u.val.val v.val.val) :=
  sesq_linear_pullback (sesq_linear_pullback (chainChart_jacobi_sesq 3 m V)
    (chainChartPhaseDomain 3 m (paperPhase ((n : ℝ) / m))).subtype continuous_subtype_val)
    (chainPhaseCharacterDomain 3 m (paperPhase ((n : ℝ) / m))
      (-(2 * Real.pi) / 3) (paperRotation_root 3 (by decide))
      (KsIndex.FormIndex.zeta 3 ^ j)).subtype continuous_subtype_val

/-- The arbitrary-m original smooth joint-sector index equals its weak realization.
Density transfers finite negative frames; it does not assert kernel regularity. -/
theorem paperSmoothSector_index_eq (m n j : ℕ) [NeZero m] :
    KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m n j) =
      negativeIndex (fun u : PaperChainSector m n j =>
        (chainChartJacobi 3 m (surfacePotential 3) u.val.val u.val.val).re) := by
  rw [KsIndex.FormIndex.formIndex_eq_negativeIndex]
  have h := negativeIndex_pullback_of_denseRange
    (paperChainSector_jacobi_sesq m n j (surfacePotential 3))
    (paperSmoothToChainSector m n j) (paperSmoothToChainSector_denseRange m n j)
  simpa only [paperSmoothToChainSector_form] using h

/-- Composition with the upper/lower slit coordinates, retaining the paper's
translation phase and unchanged rotation-character label. -/
theorem paperSmoothSector_index_eq_slit (m n j : ℕ) [NeZero m] :
    KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m n j) =
      negativeIndex (fun u : paperSlitCharacterDomain ((n : ℝ) / m) j =>
        (weakJacobi (surfacePotential 3) u.val.1 u.val.1 +
         weakJacobi (surfacePotential 3) u.val.2 u.val.2).re) :=
  (paperSmoothSector_index_eq m n j).trans
    (paperChainSlitEquiv_negativeIndex m n j (surfacePotential 3))

end KsIndex.Spectral
