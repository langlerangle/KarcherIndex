module

public import KsIndexLean.ChainSphereCharacterEquiv

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

lemma chainPhaseCharacterSphere_dirichlet (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (θ : ℝ) (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ)
    (q r : chainPhaseCharacterDomain k m c θ hθ d) :
    chainChartDirichlet k m q.val.val r.val.val = (m : ℂ) *
      sphereChartDirichlet (isOpen_boundaryArc k 1)
        (chainPhaseCharacterSphereLinearIsometryEquiv k m c hc θ hθ d q).val
        (chainPhaseCharacterSphereLinearIsometryEquiv k m c hc θ hθ d r).val :=
  chainPhaseSphere_dirichlet k m c hc q.val r.val

lemma chainPhaseCharacterSphere_jacobi (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (θ : ℝ) (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ)
    (V : BoundedRealPotential) (q r : chainPhaseCharacterDomain k m c θ hθ d) :
    chainChartJacobi k m V q.val.val r.val.val = (m : ℂ) *
      sphereChartJacobi (isOpen_boundaryArc k 1) V
        (chainPhaseCharacterSphereLinearIsometryEquiv k m c hc θ hθ d q).val
        (chainPhaseCharacterSphereLinearIsometryEquiv k m c hc θ hθ d r).val :=
  chainPhaseSphere_jacobi k m c hc V q.val r.val

end KsIndex.Trace
