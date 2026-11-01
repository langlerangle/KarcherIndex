module

public import KsIndexLean.CircleSobolevL2
public import KsIndexLean.PaperSlitIntertwiner
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section


/-! # The sign-multiplier graph domain on the circle

The domain consists of half-order Sobolev functions whose product with
`sgn(cos 3θ)` also has half-order regularity. The product is defined through
its circle `L²` realization.

`sigmaGraph` realizes this domain as a closed subspace of the square-sum
product of two half-order spaces. Its inherited norm satisfies
`‖(u, ςu)‖² = ‖u‖² + ‖ςu‖²`, and the resulting space is Hilbert.
`memDomSigma_iff_exists_graph` and `graphFst_injective` identify the graph
with the function domain through the first projection.

These results give the completeness assertion accompanying the paper's
`sgnmul_norm` display, using the repository's equivalent Sobolev norm
convention: squared half-order weights are `1+|n|`, rather than the paper's
`√(1+n²)`. The failure of closedness in the original half-order
space is proved separately in `CircleSigmaWitness`.
-/

noncomputable section
open MeasureTheory
namespace KsIndex.CircleSobolev
open KsIndex.Trace

/-- The half-order realization `H^{1/2} → L²` (the `s = 1/2` instance of `toL2`). -/
abbrev toL2Half : Space (1 / 2 : ℝ) →L[ℂ] Lp ℂ 2 circleMeasure :=
  toL2 (by norm_num : (0:ℝ) ≤ 1/2)

/-- Paper membership in `H^{1/2}_ς(S¹)` (tex 4036–4046): `u ∈ H^{1/2}` such that `ς·u`
is (realized by) an `H^{1/2}` element. -/
def MemDomSigma (u : Space (1 / 2 : ℝ)) : Prop :=
  sigmaMul (toL2Half u) ∈ Set.range toL2Half

/-- The ambient product carrying the square-sum norm (`WithLp 2`), so that the norm of a
pair `(u, ςu)` has the graph norm for the repository's Sobolev convention.
This norm is equivalent to the paper's graph norm. -/
abbrev SigmaGraphAmbient := WithLp 2 (Space (1 / 2 : ℝ) × Space (1 / 2 : ℝ))

/-- First projection from the square-sum product, as a CLM. -/
def graphFstCLM : SigmaGraphAmbient →L[ℂ] Space (1 / 2 : ℝ) :=
  (ContinuousLinearMap.fst ℂ _ _).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap

/-- Second projection from the square-sum product, as a CLM. -/
def graphSndCLM : SigmaGraphAmbient →L[ℂ] Space (1 / 2 : ℝ) :=
  (ContinuousLinearMap.snd ℂ _ _).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap

@[simp] lemma graphFstCLM_apply (p : SigmaGraphAmbient) : graphFstCLM p = p.fst := rfl

@[simp] lemma graphSndCLM_apply (p : SigmaGraphAmbient) : graphSndCLM p = p.snd := rfl

/-- The defect map `(u, v) ↦ ς·u − v` on `L²` realizations, whose kernel is the graph. -/
def sigmaDefectCLM : SigmaGraphAmbient →L[ℂ] Lp ℂ 2 circleMeasure :=
  sigmaMulCLM.comp (toL2Half.comp graphFstCLM) - toL2Half.comp graphSndCLM

/-- The graph of `ς` inside the square-sum product: pairs `(u, v)` whose `L²`
realizations satisfy `ς·u = v`.  Defined as the kernel of a continuous linear map, which
gives closedness for free — the analytic content is the boundedness of `sigmaMulCLM`
(`‖ς‖_{L²→L²} ≤ 1`) and of the inclusions `toL2Half`. -/
def sigmaGraph : Submodule ℂ SigmaGraphAmbient :=
  sigmaDefectCLM.ker

theorem mem_sigmaGraph_iff {p : SigmaGraphAmbient} :
    p ∈ sigmaGraph ↔ sigmaMul (toL2Half p.fst) = toL2Half p.snd := by
  rw [sigmaGraph, LinearMap.mem_ker]
  simp only [sigmaDefectCLM, ContinuousLinearMap.toLinearMap_sub, LinearMap.sub_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, graphFstCLM_apply,
    graphSndCLM_apply]
  rw [sub_eq_zero]
  rfl

/-- The graph is closed in the square-sum product. -/
theorem sigmaGraph_isClosed : IsClosed (sigmaGraph : Set SigmaGraphAmbient) :=
  ContinuousLinearMap.isClosed_ker sigmaDefectCLM

/-- tex 4036–4046, completeness: the graph domain is complete in the graph norm. -/
theorem sigmaGraph_completeSpace : CompleteSpace ↥sigmaGraph :=
  completeSpace_coe_iff_isComplete.mpr sigmaGraph_isClosed.isComplete

instance : CompleteSpace ↥sigmaGraph := sigmaGraph_completeSpace

/-- The graph domain inherits the inner product inducing the graph norm: together with
`sigmaGraph_completeSpace` this is the paper's "Hilbert space under the graph norm". -/
example : InnerProductSpace ℂ ↥sigmaGraph := inferInstance

/-- The graph norm is the square sum of the two component norms. This has the
form of the paper's `sgnmul_norm` display, with the repository's equivalent
Sobolev norms on the components. -/
theorem sigmaGraph_norm_sq (q : ↥sigmaGraph) :
    ‖q‖ ^ 2 = ‖(q : SigmaGraphAmbient).fst‖ ^ 2 + ‖(q : SigmaGraphAmbient).snd‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (q : SigmaGraphAmbient)

/-- The `H^{1/2}` representative of `ς·u`, for `u` in the paper domain. -/
def sigmaLift (u : Space (1 / 2 : ℝ)) (hu : MemDomSigma u) : Space (1 / 2 : ℝ) :=
  hu.choose

@[simp] theorem toL2Half_sigmaLift {u : Space (1 / 2 : ℝ)} (hu : MemDomSigma u) :
    toL2Half (sigmaLift u hu) = sigmaMul (toL2Half u) :=
  hu.choose_spec

/-- The representative is unique (the realization is injective). -/
theorem sigmaLift_unique {u v : Space (1 / 2 : ℝ)} (hu : MemDomSigma u)
    (hv : toL2Half v = sigmaMul (toL2Half u)) : v = sigmaLift u hu :=
  toL2_injective _ (by rw [hv, toL2Half_sigmaLift])

/-- The graph element over a domain member: the pair `(u, ςu)`. -/
def domPair (u : Space (1 / 2 : ℝ)) (hu : MemDomSigma u) : ↥sigmaGraph :=
  ⟨WithLp.toLp 2 (u, sigmaLift u hu), by
    rw [mem_sigmaGraph_iff]
    simp⟩

@[simp] theorem domPair_fst (u : Space (1 / 2 : ℝ)) (hu : MemDomSigma u) :
    (domPair u hu : SigmaGraphAmbient).fst = u := rfl

@[simp] theorem domPair_snd (u : Space (1 / 2 : ℝ)) (hu : MemDomSigma u) :
    (domPair u hu : SigmaGraphAmbient).snd = sigmaLift u hu := rfl

/-- The square-sum graph-norm identity corresponding to the paper's
`sgnmul_norm` display. Both norms on the right use the repository's
half-order weight `1+|n|`; the paper uses the equivalent weight `√(1+n²)`. -/
theorem domPair_norm_sq (u : Space (1 / 2 : ℝ)) (hu : MemDomSigma u) :
    ‖domPair u hu‖ ^ 2 = ‖u‖ ^ 2 + ‖sigmaLift u hu‖ ^ 2 := by
  rw [sigmaGraph_norm_sq, domPair_fst, domPair_snd]

/-- The first projection is injective on the graph: the completed space is carried
faithfully onto the paper's function domain. -/
theorem graphFst_injective :
    Function.Injective fun q : ↥sigmaGraph => (q : SigmaGraphAmbient).fst := by
  intro q r h
  have h' : (q : SigmaGraphAmbient).fst = (r : SigmaGraphAmbient).fst := h
  have hq := mem_sigmaGraph_iff.mp q.property
  have hr := mem_sigmaGraph_iff.mp r.property
  have hsnd : (q : SigmaGraphAmbient).snd = (r : SigmaGraphAmbient).snd := by
    apply toL2_injective (by norm_num : (0:ℝ) ≤ 1/2)
    rw [← hq, ← hr, h']
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  exact Prod.ext h' hsnd

/-- The first projection carries the graph exactly onto the paper domain. -/
theorem memDomSigma_iff_exists_graph (u : Space (1 / 2 : ℝ)) :
    MemDomSigma u ↔ ∃ q : ↥sigmaGraph, (q : SigmaGraphAmbient).fst = u := by
  constructor
  · intro hu
    exact ⟨domPair u hu, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(q : SigmaGraphAmbient).snd, (mem_sigmaGraph_iff.mp q.property).symm⟩

end KsIndex.CircleSobolev
