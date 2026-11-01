module

public import KsIndexLean.CharacterRestrictionEquiv
public import KsIndexLean.SlitThirdEigenvalue
public import KsIndexLean.PaperSlitSpectralCoordinates
public import KsIndexLean.PaperSmoothSector
public import KsIndexLean.SphericalPhaseRotation

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

def slitSphericalCharacter (k : ℕ) (c : ℂ) (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ) :
    Submodule ℂ (SphericalSlitPhaseSpace k c⁻¹) :=
  (sphereChartCharacterDomain (isOpen_boundaryArc k 1) θ
    (circleRotate_boundaryArc_preimage k 1 θ hθ) d).comap
      (sphericalPhaseDomain k c⁻¹).subtype

/-- Character membership is the corresponding predicate on the underlying chart value. -/
lemma mem_slitSphericalCharacter (k : ℕ) (c : ℂ) (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ)
    (q : SphericalSlitPhaseSpace k c⁻¹) :
    q ∈ slitSphericalCharacter k c θ hθ d ↔
      q.val ∈ sphereChartCharacterDomain (isOpen_boundaryArc k 1) θ
        (circleRotate_boundaryArc_preimage k 1 θ hθ) d := Iff.rfl

abbrev paperSphericalPhaseCharacter (α : ℝ) (j : ℕ) :=
  slitSphericalCharacter 3 (Complex.exp ((2 * Real.pi * α) * Complex.I))
    (-(2 * Real.pi) / 3) (paperRotation_root 3 (by decide)) (KsIndex.FormIndex.zeta 3 ^ j)

lemma upperLower_character_iff (k : ℕ) (c : ℂ) (hc : c ≠ 0)
    (θ : ℝ) (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ)
    (u : slitTraceDomain k c) :
    u.val ∈ pairCharacterDomain θ d ↔
      (upperLowerSlitToSphere k c hc u).val ∈
        sphereChartCharacterDomain (isOpen_boundaryArc k 1) θ
          (circleRotate_boundaryArc_preimage k 1 θ hθ) d := by
  rw [mem_sphereChartCharacterDomain_iff_pair]
  have he := upperLowerSlitToSphere_coordinates k c hc u
  rw [he]
  change (_ ∈ weakCharacterDomain _ _ ∧ _ ∈ weakCharacterDomain _ _) ↔
    (_ ∈ weakCharacterDomain _ _ ∧ _ ∈ weakCharacterDomain _ _)
  exact and_comm

/-- The disk-to-sphere equivalence preserves the character predicate. -/
lemma upperLower_mem_slitSphericalCharacter (k : ℕ) (c : ℂ) (hc : c ≠ 0)
    (θ : ℝ) (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ)
    (u : slitTraceDomain k c) : u.val ∈ pairCharacterDomain θ d ↔
      upperLowerSlitToSphere k c hc u ∈ slitSphericalCharacter k c θ hθ d := by
  rw [mem_slitSphericalCharacter]
  exact upperLower_character_iff k c hc θ hθ d u

def slitCharacterSphereEquiv (k : ℕ) (c : ℂ) (hc : c ≠ 0)
    (θ : ℝ) (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ) :
    ↥(slitTraceDomain k c ⊓ pairCharacterDomain θ d) ≃ₗ[ℂ]
      slitSphericalCharacter k c θ hθ d :=
  characterRestrictionEquiv _ _ _ (upperLowerSlitToSphere k c hc).toLinearEquiv
    (upperLower_mem_slitSphericalCharacter k c hc θ hθ d)

def paperSlitCharacterSphereEquiv (α : ℝ) (j : ℕ) :
    paperSlitCharacterDomain α j ≃ₗ[ℂ] paperSphericalPhaseCharacter α j :=
  slitCharacterSphereEquiv 3 _ (Complex.exp_ne_zero _) _
    (paperRotation_root 3 (by decide)) _

lemma slitCharacterSphere_jacobi (k : ℕ) (c : ℂ) (hc : c ≠ 0)
    (θ : ℝ) (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ)
    (V : BoundedRealPotential) (u v : ↥(slitTraceDomain k c ⊓ pairCharacterDomain θ d)) :
    sphereChartJacobi (isOpen_boundaryArc k 1) V
      (slitCharacterSphereEquiv k c hc θ hθ d u).val.val
      (slitCharacterSphereEquiv k c hc θ hθ d v).val.val =
    weakJacobi V u.val.1 v.val.1 + weakJacobi V u.val.2 v.val.2 :=
  upperLowerSlitToSphere_jacobi k c hc V ⟨u, u.property.1⟩ ⟨v, v.property.1⟩

lemma paperSlitCharacterSphere_jacobi (α : ℝ) (j : ℕ) (V : BoundedRealPotential)
    (u v : paperSlitCharacterDomain α j) :
    sphereChartJacobi (isOpen_boundaryArc 3 1) V
      (paperSlitCharacterSphereEquiv α j u).val.val
      (paperSlitCharacterSphereEquiv α j v).val.val =
    weakJacobi V u.val.1 v.val.1 + weakJacobi V u.val.2 v.val.2 :=
  slitCharacterSphere_jacobi 3 _ (Complex.exp_ne_zero _) _
    (paperRotation_root 3 (by decide)) _ V u v

end KsIndex.Spectral
