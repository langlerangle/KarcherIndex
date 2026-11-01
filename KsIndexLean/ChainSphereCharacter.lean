module

public import KsIndexLean.SphericalPhaseRotation
public import KsIndexLean.ChainPhaseCharacter

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- The orientation-correct phase equivalence preserves the actual rotation character. -/
lemma chainPhase_character_iff_sphere (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (θ : ℝ) (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ)
    (q : chainChartPhaseDomain k m c) :
    q.val ∈ chainChartCharacterDomain k m θ hθ d ↔
      (chainPhaseSphereLinearIsometryEquiv k m c hc q).val ∈
        sphereChartCharacterDomain (isOpen_boundaryArc k 1) θ
          (circleRotate_boundaryArc_preimage k 1 θ hθ) d := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne m)] at hc
    exact zero_ne_one hc
  rw [chainPhase_character_iff_pair, mem_sphereChartCharacterDomain_iff_pair,
    chainPhaseSphere_equiv_agrees k m c hc hc0, chainPhaseToSphere_coordinates]
  change (_ ∈ weakCharacterDomain θ d ∧ _ ∈ weakCharacterDomain θ d) ↔
    (_ ∈ weakCharacterDomain θ d ∧ _ ∈ weakCharacterDomain θ d)
  exact and_comm

/-- Rotation-character restriction inside the cyclic translation-phase domain. -/
def chainPhaseCharacterDomain (k m : ℕ) [NeZero m] (c : ℂ) (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ) :
    Submodule ℂ (chainChartPhaseDomain k m c) :=
  (chainChartCharacterDomain k m θ hθ d).comap (chainChartPhaseDomain k m c).subtype

/-- Joint phase and rotation-character conditions on the spherical Neumann carrier. -/
def sphericalPhaseCharacterDomain (k : ℕ) (c : ℂ) (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ) :
    Submodule ℂ (SphericalSlitNeumannSpace k) :=
  sphericalPhaseDomain k c ⊓ sphereChartCharacterDomain (isOpen_boundaryArc k 1) θ
    (circleRotate_boundaryArc_preimage k 1 θ hθ) d

end KsIndex.Trace
