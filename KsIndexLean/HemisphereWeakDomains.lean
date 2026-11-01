module

public import KsIndexLean.HemisphereWeakCarrier
public import KsIndexLean.SphericalWeakRotationValue
public import KsIndexLean.GeneralDirichletPositivity

@[expose] public section


/-! Boundary and rotation domains on the actual single lower hemisphere. -/
noncomputable section
open Set MeasureTheory Filter
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex

/-- A disk weak domain in the actual stereographic hemisphere carrier. -/
def hemisphereDomain (D : Submodule ℂ ComplexH1) : Submodule ℂ HemisphereChartSpace :=
  D.comap hemisphereCoordinates.toLinearEquiv.toLinearMap

/-- Full domain correspondence, including every admissible test function. -/
def hemisphereDomainEquiv (D : Submodule ℂ ComplexH1) : D ≃ₗ[ℂ] hemisphereDomain D where
  toFun u := ⟨hemisphereCoordinates.symm u.val,by
    change hemisphereCoordinates (hemisphereCoordinates.symm u.val) ∈ D
    simpa only [LinearIsometryEquiv.apply_symm_apply] using u.property⟩
  invFun u := ⟨hemisphereCoordinates u.val,u.property⟩
  left_inv u := Subtype.ext (hemisphereCoordinates.apply_symm_apply u.val)
  right_inv u := Subtype.ext (hemisphereCoordinates.symm_apply_apply u.val)
  map_add' u v := Subtype.ext (hemisphereCoordinates.symm.map_add u.val v.val)
  map_smul' a u := Subtype.ext (hemisphereCoordinates.symm.map_smul a u.val)

/-- Zero equatorial trace, expressed in its boundary circle coordinate. -/
def hemisphereDirichletDomain : Submodule ℂ HemisphereChartSpace :=
  hemisphereDomain (zeroTraceDomain Set.univ)

/-- The weak rotation condition is exactly the actual spherical rotation
condition almost everywhere for lower-hemisphere area. -/
lemma hemisphere_character_iff (θ : ℝ) (c : ℂ) (u : HemisphereChartSpace) :
    hemisphereCoordinates u ∈ weakCharacterDomain θ c ↔
      (fun p => hemisphereValue u (rotateSphere θ p))
        =ᵐ[(volume : Measure Ambient).toSphere.restrict {p : Sphere | p.val 2 < 0}]
      (fun p => c * hemisphereValue u p) := by
  rw [hemisphere_ae_eq_iff]
  simp only [hemisphereValue,rotateSphere_sphereChart,sphereWeakValue_pullback]
  constructor
  · intro h
    have he := (mem_weakCharacterDomain θ c _).mp h
    have hf : valueCLM (diskRotation θ (hemisphereCoordinates u)) =
        c • valueCLM (hemisphereCoordinates u) := by rw [he,map_smul]
    filter_upwards [diskRotation_value_ae θ (hemisphereCoordinates u),
      Lp.coeFn_smul c (valueCLM (hemisphereCoordinates u))] with z hr hs
    have hv := congrArg (fun f : L2C => f z) hf
    exact hr.symm.trans (hv.trans hs)
  · intro h
    apply (mem_weakCharacterDomain θ c _).mpr
    apply valueCLM_injective
    rw [map_smul]
    apply Lp.ext
    filter_upwards [diskRotation_value_ae θ (hemisphereCoordinates u),
      Lp.coeFn_smul c (valueCLM (hemisphereCoordinates u)),h] with z hr hs hz
    rw [hr,hs]
    exact hz

/-- Pure D/N character domain on one lower hemisphere. -/
def hemisphereCharacterDomain (k j : ℕ) (b : Bool) : Submodule ℂ HemisphereChartSpace :=
  hemisphereDomain (mixedCharacterDomain k j b b)

lemma mem_hemisphereCharacterDomain {k : ℕ} (hk : 1 ≤ k) (j : ℕ) (b : Bool)
    (u : HemisphereChartSpace) :
    u ∈ hemisphereCharacterDomain k j b ↔
      (if b then True else u ∈ hemisphereDirichletDomain) ∧
      (fun p => hemisphereValue u (rotateSphere (-(2 * Real.pi) / k) p))
        =ᵐ[(volume : Measure Ambient).toSphere.restrict {p : Sphere | p.val 2 < 0}]
      (fun p => zeta k ^ j * hemisphereValue u p) := by
  rw [← hemisphere_character_iff]
  cases b
  · change hemisphereCoordinates u ∈ mixedCharacterDomain k j false false ↔ _
    rw [mixedDD_eq_fullDirichletCharacter hk j]
    rfl
  · change hemisphereCoordinates u ∈ mixedCharacterDomain k j true true ↔ _
    simp only [mixedCharacterDomain,Submodule.mem_inf,mixedTraceDomain_NN,Submodule.mem_top,
      true_and,ite_true]

end KsIndex.Spherical
