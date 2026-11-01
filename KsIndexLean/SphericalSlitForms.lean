module

public import KsIndexLean.SphericalSlitLinear

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- The Dirichlet inclusion into every phase domain preserves the inherited norm. -/
def sphericalDirichletToPhaseLI (k : ℕ) (c : ℂ) :
    SphericalSlitDirichletSpace k →ₗᵢ[ℂ] SphericalSlitPhaseSpace k c where
  toFun := sphericalDirichletToPhase k c
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  norm_map' _ := rfl

/-- Forgetting the slit phase is the isometric subspace inclusion. -/
def sphericalPhaseToNeumannLI (k : ℕ) (c : ℂ) :
    SphericalSlitPhaseSpace k c →ₗᵢ[ℂ] SphericalSlitNeumannSpace k where
  toFun := sphericalPhaseToNeumann k c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

lemma slitPhaseLinearIsometryEquiv_symm_val (k : ℕ) (c : ℂ) (p : slitTraceDomain k c) :
    ((slitPhaseLinearIsometryEquiv k c).symm p).val = (slitPhaseEquiv k c p).val := rfl

lemma slitDirichletLinearIsometryEquiv_symm_val (k : ℕ) (p : slitDirichletDomain k) :
    ((slitDirichletLinearIsometryEquiv k).symm p).val = (slitDirichletEquiv k p).val := rfl

lemma slitNeumannLinearIsometryEquiv_symm_apply (k : ℕ) (p : slitNeumannDomain k) :
    (slitNeumannLinearIsometryEquiv k).symm p = slitNeumannEquiv k p := rfl

/-- The phase equivalence preserves the Dirichlet form on precisely its phase domain. -/
lemma slitPhase_dirichlet (k : ℕ) (c : ℂ) (p r : slitTraceDomain k c) :
    sphereChartDirichlet (isOpen_boundaryArc k 1)
      ((slitPhaseLinearIsometryEquiv k c).symm p).val
      ((slitPhaseLinearIsometryEquiv k c).symm r).val =
    dirichlet p.val.1 r.val.1 + dirichlet p.val.2 r.val.2 :=
  sphereChartDirichlet_matchingPair (isOpen_boundaryArc k 1)
    (slitMatchingPair k c p) (slitMatchingPair k c r)

lemma slitPhase_jacobi (k : ℕ) (c : ℂ) (V : BoundedRealPotential) (p r : slitTraceDomain k c) :
    sphereChartJacobi (isOpen_boundaryArc k 1) V
      ((slitPhaseLinearIsometryEquiv k c).symm p).val
      ((slitPhaseLinearIsometryEquiv k c).symm r).val =
    weakJacobi V p.val.1 r.val.1 + weakJacobi V p.val.2 r.val.2 :=
  sphereChartJacobi_matchingPair (isOpen_boundaryArc k 1) V
    (slitMatchingPair k c p) (slitMatchingPair k c r)

lemma slitDirichlet_dirichlet (k : ℕ) (p r : slitDirichletDomain k) :
    sphereChartDirichlet (isOpen_boundaryArc k 1)
      ((slitDirichletLinearIsometryEquiv k).symm p).val
      ((slitDirichletLinearIsometryEquiv k).symm r).val =
    dirichlet p.val.1 r.val.1 + dirichlet p.val.2 r.val.2 :=
  sphereChartDirichlet_matchingPair (isOpen_boundaryArc k 1)
    (dirichletMatchingPair k p) (dirichletMatchingPair k r)

lemma slitDirichlet_jacobi (k : ℕ) (V : BoundedRealPotential) (p r : slitDirichletDomain k) :
    sphereChartJacobi (isOpen_boundaryArc k 1) V
      ((slitDirichletLinearIsometryEquiv k).symm p).val
      ((slitDirichletLinearIsometryEquiv k).symm r).val =
    weakJacobi V p.val.1 r.val.1 + weakJacobi V p.val.2 r.val.2 :=
  sphereChartJacobi_matchingPair (isOpen_boundaryArc k 1) V
    (dirichletMatchingPair k p) (dirichletMatchingPair k r)

lemma slitNeumann_dirichlet (k : ℕ) (p r : slitNeumannDomain k) :
    sphereChartDirichlet (isOpen_boundaryArc k 1)
      ((slitNeumannLinearIsometryEquiv k).symm p)
      ((slitNeumannLinearIsometryEquiv k).symm r) =
    dirichlet p.val.1 r.val.1 + dirichlet p.val.2 r.val.2 :=
  sphereChartDirichlet_matchingPair (isOpen_boundaryArc k 1)
    (neumannMatchingEquiv k p) (neumannMatchingEquiv k r)

lemma slitNeumann_jacobi (k : ℕ) (V : BoundedRealPotential) (p r : slitNeumannDomain k) :
    sphereChartJacobi (isOpen_boundaryArc k 1) V
      ((slitNeumannLinearIsometryEquiv k).symm p)
      ((slitNeumannLinearIsometryEquiv k).symm r) =
    weakJacobi V p.val.1 r.val.1 + weakJacobi V p.val.2 r.val.2 :=
  sphereChartJacobi_matchingPair (isOpen_boundaryArc k 1) V
    (neumannMatchingEquiv k p) (neumannMatchingEquiv k r)

end KsIndex.Spherical
