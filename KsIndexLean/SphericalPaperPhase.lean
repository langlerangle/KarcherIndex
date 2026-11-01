module

public import KsIndexLean.SphericalSlitForms

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Swapping an upper/lower pair converts c to its reciprocal in lower/upper order. -/
def slitPhaseSwapLinearIsometryEquiv (k : ℕ) (c : ℂ) (hc : c ≠ 0) :
    slitTraceDomain k c ≃ₗᵢ[ℂ] slitTraceDomain k c⁻¹ where
  toFun p := ⟨(p.val.2, p.val.1), by
    obtain ⟨h1, h0⟩ := (mem_slitTraceDomain k c p.val).mp p.property
    rw [mem_slitTraceDomain]
    refine ⟨h1.symm, ?_⟩
    change _ = c⁻¹ • arcTrace (boundaryArc k 0) p.val.1
    rw [h0, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  invFun q := ⟨(q.val.2, q.val.1), by
    obtain ⟨h1, h0⟩ := (mem_slitTraceDomain k c⁻¹ q.val).mp q.property
    rw [mem_slitTraceDomain]
    refine ⟨h1.symm, ?_⟩
    change _ = c • arcTrace (boundaryArc k 0) q.val.1
    rw [h0, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' p := max_comm ‖p.val.2‖ ‖p.val.1‖

/-- The target has lower/upper chart order, while the source has upper/lower disk order. -/
def upperLowerSlitToSphere (k : ℕ) (c : ℂ) (hc : c ≠ 0) :
    slitTraceDomain k c ≃ₗᵢ[ℂ] SphericalSlitPhaseSpace k c⁻¹ :=
  (slitPhaseSwapLinearIsometryEquiv k c hc).trans
    (slitPhaseLinearIsometryEquiv k c⁻¹).symm

lemma upperLowerSlitToSphere_coordinates (k : ℕ) (c : ℂ) (hc : c ≠ 0)
    (p : slitTraceDomain k c) :
    sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) (upperLowerSlitToSphere k c hc p).val =
      (p.val.2, p.val.1) := by
  exact congrArg Subtype.val (chartDiskPair_join (isOpen_boundaryArc k 1)
    (slitMatchingPair k c⁻¹ (slitPhaseSwapLinearIsometryEquiv k c hc p)))

/-- The upper trace is the second recovered chart trace. -/
lemma sphericalPhase_reciprocal_upper (k : ℕ) (c : ℂ) (hc : c ≠ 0)
    (q : SphericalSlitPhaseSpace k c⁻¹) :
    secondChartTrace (isOpen_boundaryArc k 1) (boundaryArc k 0) q.val =
      c • firstChartTrace (isOpen_boundaryArc k 1) (boundaryArc k 0) q.val := by
  rw [q.property, smul_smul, mul_inv_cancel₀ hc, one_smul]

lemma upperLowerSlitToSphere_dirichlet (k : ℕ) (c : ℂ) (hc : c ≠ 0)
    (p r : slitTraceDomain k c) :
    sphereChartDirichlet (isOpen_boundaryArc k 1)
      (upperLowerSlitToSphere k c hc p).val (upperLowerSlitToSphere k c hc r).val =
      dirichlet p.val.1 r.val.1 + dirichlet p.val.2 r.val.2 := by
  simp only [sphereChartDirichlet, upperLowerSlitToSphere_coordinates]
  exact add_comm _ _

lemma upperLowerSlitToSphere_jacobi (k : ℕ) (c : ℂ) (hc : c ≠ 0)
    (V : BoundedRealPotential) (p r : slitTraceDomain k c) :
    sphereChartJacobi (isOpen_boundaryArc k 1) V
      (upperLowerSlitToSphere k c hc p).val (upperLowerSlitToSphere k c hc r).val =
      weakJacobi V p.val.1 r.val.1 + weakJacobi V p.val.2 r.val.2 := by
  simp only [sphereChartJacobi, upperLowerSlitToSphere_coordinates]
  exact add_comm _ _

/-- The paper's H1_[alpha] uses upper = exp(2*pi*i*alpha) * lower. -/
abbrev PaperSphericalPhaseSpace (α : ℝ) :=
  SphericalSlitPhaseSpace 3 (Complex.exp ((2 * Real.pi * α) * Complex.I))⁻¹

def paperSlitSphereLinearIsometryEquiv (α : ℝ) :
    paperSlitDomain α ≃ₗᵢ[ℂ] PaperSphericalPhaseSpace α :=
  upperLowerSlitToSphere 3 _ (Complex.exp_ne_zero _)

lemma paperSphericalPhase_upper (α : ℝ) (q : PaperSphericalPhaseSpace α) :
    secondChartTrace (isOpen_boundaryArc 3 1) (boundaryArc 3 0) q.val =
      Complex.exp ((2 * Real.pi * α) * Complex.I) •
        firstChartTrace (isOpen_boundaryArc 3 1) (boundaryArc 3 0) q.val :=
  sphericalPhase_reciprocal_upper 3 _ (Complex.exp_ne_zero _) q

end KsIndex.Spherical
