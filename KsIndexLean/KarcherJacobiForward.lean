module

public import KsIndexLean.KarcherCopyJacobi
public import KsIndexLean.KarcherSmoothFunctionTransport

@[expose] public section


/-! Encoding actual bounded geometric Jacobi fields as model Jacobi fields. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma boundedGeometricJacobi_encoding_mem
    (G : R.boundedGeometricJacobi (m := m)) :
    encodeDiskFunction (R.diskFunctionPullback G.val) ∈ Surface.BoundedJacobi k m := by
  obtain ⟨hsm, ⟨C, hC⟩, hJ⟩ := G.property
  refine ⟨(R.contMDiff_iff_isSmooth_encoding G.val).mp hsm, ?_, ?_,
    encodeDiskFunction_punctureZero _, encodeDiskFunction_seamVal _⟩
  · refine ⟨max C 0, ?_⟩
    intro n z
    unfold encodeDiskFunction
    split_ifs with hz
    · exact (hC _).trans (le_max_left _ _)
    · simp
  · apply (R.encoding_isJacobiField_iff_openCopies G.val hsm).mpr
    intro n w hw
    have he := (R.isGeometricJacobi_iff G.val).mp hJ
    exact congrFun he (R.orderedDiskPoint n w)

/-- Canonical complex-linear encoding of actual bounded smooth geometric
solutions into the paper's normalized disk-chain solution space. -/
def geometricJacobiToModel : R.boundedGeometricJacobi (m := m) →ₗ[ℂ] Surface.BoundedJacobi k m where
  toFun G := ⟨encodeDiskFunction (R.diskFunctionPullback G.val), R.boundedGeometricJacobi_encoding_mem G⟩
  map_add' := by
    intro G H
    apply Subtype.ext
    funext n z
    change encodeDiskFunction _ n z = _
    simp only [Submodule.coe_add, Pi.add_apply]
    dsimp only [encodeDiskFunction]
    split_ifs <;> simp
  map_smul' := by
    intro c G
    apply Subtype.ext
    funext n z
    change encodeDiskFunction _ n z = _
    simp only [Submodule.coe_smul, Pi.smul_apply]
    dsimp only [encodeDiskFunction]
    split_ifs <;> simp

/-- Descending the forward encoding recovers the original actual function. -/
lemma boundedJacobiFunction_geometricJacobiToModel
    (G : R.boundedGeometricJacobi (m := m)) :
    R.boundedJacobiFunction (R.geometricJacobiToModel G) = G.val := by
  change R.diskFunctionDescend
    (restrictSeamFamily (encodeDiskFunction (R.diskFunctionPullback G.val)) _) = G.val
  rw [restrict_encodeDiskFunction]
  exact R.diskFunctionEquiv.left_inv G.val

lemma geometricJacobiToModel_injective : Function.Injective (R.geometricJacobiToModel (m := m)) := by
  intro G H he
  apply Subtype.ext
  have hh := congrArg R.boundedJacobiFunction he
  simpa only [R.boundedJacobiFunction_geometricJacobiToModel] using hh

end KsIndex.KarcherData.PaperHalfPeriodRealization
