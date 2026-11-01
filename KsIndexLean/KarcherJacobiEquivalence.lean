module

public import KsIndexLean.KarcherJacobiReverse
public import KsIndexLean.KarcherJointCharacters
public import KsIndexLean.KarcherConjugationEncoding
public import KsIndexLean.KarcherHeightReflectionEncoding

@[expose] public section


/-! Bounded geometric Jacobi fields and normalized model fields are linearly
equivalent, with the same translation, rotation and reflection characters. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- The actual quotient and the disk-chain model have equivalent complex
spaces of bounded smooth Jacobi fields. -/
def geometricJacobiEquiv : R.boundedGeometricJacobi (m := m) ≃ₗ[ℂ] Surface.BoundedJacobi k m where
  toLinearMap := R.geometricJacobiToModel
  invFun u := ⟨R.boundedJacobiFunction u, R.boundedJacobiFunction_isBoundedGeometricJacobi u⟩
  left_inv G := Subtype.ext (R.boundedJacobiFunction_geometricJacobiToModel G)
  right_inv u := Subtype.ext (R.encode_boundedJacobiFunction u)

@[simp] lemma geometricJacobiEquiv_apply
    (G : R.boundedGeometricJacobi (m := m)) :
    (R.geometricJacobiEquiv G).val = encodeDiskFunction (R.diskFunctionPullback G.val) := rfl

@[simp] lemma geometricJacobiEquiv_symm_apply
    (u : Surface.BoundedJacobi k m) :
    (R.geometricJacobiEquiv.symm u).val = R.boundedJacobiFunction u := rfl

lemma geometricJacobiEquiv_translation_character
    (G : R.boundedGeometricJacobi (m := m)) (c : ℂ) :
    (∀ q, G.val (HeightLift.periodDeck m 1 q) = c * G.val q) ↔
      ∀ n z, SurfaceSym.shiftF (R.geometricJacobiEquiv G).val n z =
        c * (R.geometricJacobiEquiv G).val n z :=
  R.translation_eigenvalue_iff G.val c

lemma geometricJacobiEquiv_rotation_character
    (G : R.boundedGeometricJacobi (m := m)) (c : ℂ) :
    (∀ q, G.val (R.periodRotation m q) = c * G.val q) ↔
      ∀ n z, SurfaceSym.rotF (SurfaceSym.rotUnit k : ℂ) (R.geometricJacobiEquiv G).val n z =
        c * (R.geometricJacobiEquiv G).val n z :=
  R.rotation_eigenvalue_iff G.val c

lemma geometricJacobiEquiv_conjugation_character
    (G : R.boundedGeometricJacobi (m := m)) (c : ℂ) :
    (∀ q, G.val (R.periodConjugation m q) = c * G.val q) ↔
      ∀ n z, (R.geometricJacobiEquiv G).val n ((starRingEnd ℂ) z) =
        c * (R.geometricJacobiEquiv G).val n z := by
  have he := R.encoding_scalar_relation_iff (G.val ∘ R.periodConjugation m) G.val c
  rw [R.encode_conjugation_pullback] at he
  exact he

lemma geometricJacobiEquiv_heightReflection_character
    (G : R.boundedGeometricJacobi (m := m)) (c : ℂ) :
    (∀ q, G.val (R.periodHeightReflection m q) = c * G.val q) ↔
      ∀ n z, (R.geometricJacobiEquiv G).val (-n-1) z =
        c * (R.geometricJacobiEquiv G).val n z := by
  have he := R.encoding_scalar_relation_iff (G.val ∘ R.periodHeightReflection m) G.val c
  rw [R.encode_heightReflection_pullback] at he
  exact he

/-- Every model joint-character field has a unique actual geometric preimage
with the same two characters. -/
lemma geometricJacobiEquiv_joint_preimage
    (u : Surface.BoundedJacobi k m) (c d : ℂ)
    (ht : ∀ n z, SurfaceSym.shiftF u.val n z = c * u.val n z)
    (hr : ∀ n z, SurfaceSym.rotF (SurfaceSym.rotUnit k : ℂ) u.val n z = d * u.val n z) :
    ∃! G : R.boundedGeometricJacobi (m := m),
      R.geometricJacobiEquiv G = u ∧
      (∀ q, G.val (HeightLift.periodDeck m 1 q) = c * G.val q) ∧
      (∀ q, G.val (R.periodRotation m q) = d * G.val q) := by
  refine ⟨R.geometricJacobiEquiv.symm u, ⟨R.geometricJacobiEquiv.apply_symm_apply u, ?_, ?_⟩, ?_⟩
  · apply (R.geometricJacobiEquiv_translation_character _ c).mpr
    simpa only [LinearEquiv.apply_symm_apply] using ht
  · apply (R.geometricJacobiEquiv_rotation_character _ d).mpr
    simpa only [LinearEquiv.apply_symm_apply] using hr
  · intro G hG
    exact R.geometricJacobiEquiv.injective (hG.1.trans (R.geometricJacobiEquiv.apply_symm_apply u).symm)

end KsIndex.KarcherData.PaperHalfPeriodRealization
