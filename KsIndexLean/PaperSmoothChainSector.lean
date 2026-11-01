module

public import KsIndexLean.CcSmoothChainForms
public import KsIndexLean.PaperChainSlitCoordinates
public import KsIndexLean.NaturalCoreCharacter

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- The k = 3 smooth domain intersected with the rotation and shift eigenspaces
used in the `SurfaceSym` index sum. -/
def paperSmoothJointSector (m n j : ℕ) :
    Submodule ℂ (ZMod (2 * m) × ℂ → ℂ) :=
  (SurfaceForm.Dom 3 m ⊓ Module.End.eigenspace
    (SurfaceSym.rotE m (SurfaceSym.rotUnit 3)) (KsIndex.FormIndex.zeta 3 ^ j)) ⊓
    Module.End.eigenspace (SurfaceSym.shiftE m) (KsIndex.FormIndex.zeta m ^ n)

lemma paperRationalPhase_eq_zeta (m n : ℕ) :
    paperPhase ((n : ℝ) / m) = KsIndex.FormIndex.zeta m ^ n := by
  rw [paperCharacter_exp]
  unfold paperPhase
  congr 1
  push_cast
  ring

def paperSmoothUnderlying (m n j : ℕ) :
    paperSmoothJointSector m n j →ₗ[ℂ] SurfaceForm.Dom 3 m :=
  Submodule.inclusion (fun _ h => h.1.1)

lemma paperSmoothToChain_phase (m n j : ℕ) [NeZero m]
    (u : paperSmoothJointSector m n j) :
    domToChainChart 3 m (paperSmoothUnderlying m n j u) ∈
      chainChartPhaseDomain 3 m (paperPhase ((n : ℝ) / m)) := by
  rw [mem_chainChartPhaseDomain_iff_coordinates]
  intro q
  let f := domCcSmoothEquiv 3 m (paperSmoothUnderlying m n j u)
  change chainChartCoordinatesCLM 3 m (ccSmoothToChainChart 3 m f) (q + 2) =
    paperPhase ((n : ℝ) / m) • chainChartCoordinatesCLM 3 m (ccSmoothToChainChart 3 m f) q
  rw [ccSmoothToChainChart_coordinates]
  apply valueCLM_injective
  rw [map_smul]
  apply Lp.ext
  filter_upwards [ccSmoothCopy_value_ae f (q + 2), ccSmoothCopy_value_ae f q,
    Lp.coeFn_smul (paperPhase ((n : ℝ) / m)) (valueCLM (ccSmoothCopy f q))]
    with z hq hz hc
  rw [hc, Pi.smul_apply, hq, hz, paperRationalPhase_eq_zeta]
  exact congrFun (Module.End.mem_eigenspace_iff.mp u.property.2) (q, z)

lemma paperSmoothToChain_character (m n j : ℕ) [NeZero m]
    (u : paperSmoothJointSector m n j) :
    domToChainChart 3 m (paperSmoothUnderlying m n j u) ∈
      chainChartCharacterDomain 3 m (-(2 * Real.pi) / 3)
        (paperRotation_root 3 (by decide)) (KsIndex.FormIndex.zeta 3 ^ j) := by
  rw [mem_chainChartCharacterDomain_iff_coordinates]
  intro q
  let f := domCcSmoothEquiv 3 m (paperSmoothUnderlying m n j u)
  change diskRotation _ (chainChartCoordinatesCLM 3 m (ccSmoothToChainChart 3 m f) q) =
    (KsIndex.FormIndex.zeta 3 ^ j) •
      chainChartCoordinatesCLM 3 m (ccSmoothToChainChart 3 m f) q
  rw [ccSmoothToChainChart_coordinates]
  apply (mem_weakCharacterDomain _ _ _).mp
  apply weakCharacter_of_value_eq _ _ _ (ccSmoothCopy_value_ae f q)
  intro z
  have h := congrFun (Module.End.mem_eigenspace_iff.mp u.property.1.2) (q, z)
  change u.val (q, planeRotation (-(2 * Real.pi) / 3) z) =
    (KsIndex.FormIndex.zeta 3 ^ j) * u.val (q, z)
  simpa only [Nat.cast_ofNat, SurfaceSym.rotE_apply, SurfaceSym.rotUnit, Circle.coe_exp,
    Pi.smul_apply, smul_eq_mul, planeRotation_apply] using h

/-- Restrict a linear map to two target subspaces, using a generic carrier to
keep the concrete chart instances out of the linearity proofs. -/
def nestedSectorMap {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (L : E →ₗ[ℂ] F) (D C : Submodule ℂ F)
    (hD : ∀ u, L u ∈ D) (hC : ∀ u, L u ∈ C) : E →ₗ[ℂ] C.comap D.subtype where
  toFun u := ⟨⟨L u, hD u⟩, hC u⟩
  map_add' u v := Subtype.ext (Subtype.ext (L.map_add u v))
  map_smul' c u := Subtype.ext (Subtype.ext (L.map_smul c u))

/-- Restriction to the genuine weak joint sector, without assuming density. -/
def paperSmoothToChainSector (m n j : ℕ) [NeZero m] :
    paperSmoothJointSector m n j →ₗ[ℂ] PaperChainSector m n j :=
  nestedSectorMap ((domToChainChart 3 m).comp (paperSmoothUnderlying m n j))
    (chainChartPhaseDomain 3 m (paperPhase ((n : ℝ) / m)))
    (chainChartCharacterDomain 3 m (-(2 * Real.pi) / 3)
      (paperRotation_root 3 (by decide)) (KsIndex.FormIndex.zeta 3 ^ j))
    (paperSmoothToChain_phase m n j) (paperSmoothToChain_character m n j)

lemma paperSmoothToChainSector_form (m n j : ℕ) [NeZero m]
    (u : paperSmoothJointSector m n j) :
    (chainChartJacobi 3 m (surfacePotential 3)
      (paperSmoothToChainSector m n j u).val.val
      (paperSmoothToChainSector m n j u).val.val).re = SurfaceForm.Qs 3 m u.val :=
  domToChainChart_form (by decide) (paperSmoothUnderlying m n j u)

end KsIndex.Spectral
