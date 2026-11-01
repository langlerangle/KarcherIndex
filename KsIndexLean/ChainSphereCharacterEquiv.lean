module

public import KsIndexLean.ChainSphereCharacter

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

variable (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
  (θ : ℝ) (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ)

def characterToSphere (q : chainPhaseCharacterDomain k m c θ hθ d) :
    sphericalPhaseCharacterDomain k c⁻¹ θ hθ d :=
  ⟨(chainPhaseSphereLinearIsometryEquiv k m c hc q.val).val,
    ⟨(chainPhaseSphereLinearIsometryEquiv k m c hc q.val).property,
      (chainPhase_character_iff_sphere k m c hc θ hθ d q.val).mp q.property⟩⟩

lemma character_inverse_mem (q : sphericalPhaseCharacterDomain k c⁻¹ θ hθ d) :
    ((chainPhaseSphereLinearIsometryEquiv k m c hc).symm
      (⟨q.val, q.property.1⟩ : SphericalSlitPhaseSpace k c⁻¹)).val ∈
        chainChartCharacterDomain k m θ hθ d := by
  apply (chainPhase_character_iff_sphere k m c hc θ hθ d _).mpr
  have he := (chainPhaseSphereLinearIsometryEquiv k m c hc).apply_symm_apply
    (⟨q.val, q.property.1⟩ : SphericalSlitPhaseSpace k c⁻¹)
  have hv := congrArg (fun x : SphericalSlitPhaseSpace k c⁻¹ => x.val) he
  exact hv.symm ▸ q.property.2

def characterToChain (q : sphericalPhaseCharacterDomain k c⁻¹ θ hθ d) :
    chainPhaseCharacterDomain k m c θ hθ d :=
  ⟨(chainPhaseSphereLinearIsometryEquiv k m c hc).symm ⟨q.val, q.property.1⟩,
    character_inverse_mem k m c hc θ hθ d q⟩

lemma characterToChain_toSphere (q : chainPhaseCharacterDomain k m c θ hθ d) :
    characterToChain k m c hc θ hθ d (characterToSphere k m c hc θ hθ d q) = q := by
  apply Subtype.ext
  exact (chainPhaseSphereLinearIsometryEquiv k m c hc).symm_apply_apply q.val

lemma characterToSphere_toChain (q : sphericalPhaseCharacterDomain k c⁻¹ θ hθ d) :
    characterToSphere k m c hc θ hθ d (characterToChain k m c hc θ hθ d q) = q := by
  apply Subtype.ext
  exact congrArg (fun x : SphericalSlitPhaseSpace k c⁻¹ => x.val)
    ((chainPhaseSphereLinearIsometryEquiv k m c hc).apply_symm_apply
      (⟨q.val, q.property.1⟩ : SphericalSlitPhaseSpace k c⁻¹))

lemma characterToSphere_add (q r : chainPhaseCharacterDomain k m c θ hθ d) :
    characterToSphere k m c hc θ hθ d (q + r) =
      characterToSphere k m c hc θ hθ d q + characterToSphere k m c hc θ hθ d r := by
  apply Subtype.ext
  exact congrArg (fun x : SphericalSlitPhaseSpace k c⁻¹ => x.val)
    ((chainPhaseSphereLinearIsometryEquiv k m c hc).map_add q.val r.val)

lemma characterToSphere_smul (a : ℂ) (q : chainPhaseCharacterDomain k m c θ hθ d) :
    characterToSphere k m c hc θ hθ d (a • q) =
      a • characterToSphere k m c hc θ hθ d q := by
  apply Subtype.ext
  exact congrArg (fun x : SphericalSlitPhaseSpace k c⁻¹ => x.val)
    ((chainPhaseSphereLinearIsometryEquiv k m c hc).map_smul a q.val)

lemma characterToSphere_norm (q : chainPhaseCharacterDomain k m c θ hθ d) :
    ‖characterToSphere k m c hc θ hθ d q‖ = ‖q‖ :=
  (chainPhaseSphereLinearIsometryEquiv k m c hc).norm_map q.val

/-- The joint phase/rotation-character equivalence, assembled from checked component lemmas. -/
def chainPhaseCharacterSphereLinearIsometryEquiv :
    chainPhaseCharacterDomain k m c θ hθ d ≃ₗᵢ[ℂ]
      sphericalPhaseCharacterDomain k c⁻¹ θ hθ d where
  toFun := characterToSphere k m c hc θ hθ d
  invFun := characterToChain k m c hc θ hθ d
  left_inv := characterToChain_toSphere k m c hc θ hθ d
  right_inv := characterToSphere_toChain k m c hc θ hθ d
  map_add' := characterToSphere_add k m c hc θ hθ d
  map_smul' := characterToSphere_smul k m c hc θ hθ d
  norm_map' := characterToSphere_norm k m c hc θ hθ d

end KsIndex.Trace
