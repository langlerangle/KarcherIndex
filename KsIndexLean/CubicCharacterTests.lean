module

public import KsIndexLean.DiskRotationForms

@[expose] public section


noncomputable section
namespace KsIndex.Trace

section Algebra
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Weighted sum of three iterates. Under the order-three hypotheses below,
this gives a character test; normalization is unnecessary for the test-extension argument. -/
def cubicCharacterTest (T : E →ₗ[ℂ] E) (c : ℂ) (v : E) : E :=
  c ^ 2 • v + c • T v + T (T v)

lemma cubicCharacterTest_mem (T : E →ₗ[ℂ] E) (c : ℂ) (D : Submodule ℂ E)
    (hT : ∀ v ∈ D, T v ∈ D) {v : E} (hv : v ∈ D) :
    cubicCharacterTest T c v ∈ D :=
  D.add_mem (D.add_mem (D.smul_mem _ hv) (D.smul_mem _ (hT v hv)))
    (hT (T v) (hT v hv))

lemma cubicCharacterTest_eigen (T : E →ₗ[ℂ] E) (c : ℂ)
    (hc : c ^ 3 = 1) (hT : ∀ v, T (T (T v)) = v) (v : E) :
    T (cubicCharacterTest T c v) = c • cubicCharacterTest T c v := by
  simp only [cubicCharacterTest, map_add, map_smul, hT, smul_add, smul_smul]
  have h : c * c ^ 2 = 1 := by
    calc
      c * c ^ 2 = c ^ 3 := by ring
      _ = 1 := hc
  rw [h, one_smul]
  simp only [pow_two]
  abel

lemma cubicCharacterTest_pairing (T : E →ₗ[ℂ] E) (c : ℂ) (L : E →ₗ[ℂ] ℂ)
    (hL : ∀ v, L (T v) = c * L v) (v : E) :
    L (cubicCharacterTest T c v) = (3 * c ^ 2) * L v := by
  simp only [cubicCharacterTest, map_add, map_smul, smul_eq_mul, hL]
  ring

/-- A character-covariant functional vanishing on character tests vanishes on
all tests in an invariant domain. -/
lemma cubicCharacter_tests_suffice (T : E →ₗ[ℂ] E) (c : ℂ) (D : Submodule ℂ E)
    (hc : c ^ 3 = 1) (hT : ∀ v, T (T (T v)) = v)
    (hD : ∀ v ∈ D, T v ∈ D) (L : E →ₗ[ℂ] ℂ)
    (hL : ∀ v, L (T v) = c * L v)
    (hzero : ∀ v ∈ D, T v = c • v → L v = 0) :
    ∀ v ∈ D, L v = 0 := by
  intro v hv
  have hz := hzero _ (cubicCharacterTest_mem T c D hD hv)
    (cubicCharacterTest_eigen T c hc hT v)
  rw [cubicCharacterTest_pairing T c L hL] at hz
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero _ hc0))

end Algebra
open KsIndex.WeakH1

lemma surfaceJacobi_character_test_rotation (k : ℕ) (θ : ℝ) (c : ℂ)
    (hc : ‖c‖ = 1) (u : ComplexH1) (hu : diskRotation θ u = c • u)
    (v : ComplexH1) :
    weakJacobi (surfacePotential k) u (diskRotation θ v) =
      c * weakJacobi (surfacePotential k) u v := by
  have h := surfaceJacobi_diskRotation k θ u v
  rw [hu, weakJacobi_smul_left] at h
  have hc' : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  calc
    _ = (c * (starRingEnd ℂ) c) * weakJacobi (surfacePotential k) u (diskRotation θ v) := by rw [hc', one_mul]
    _ = c * weakJacobi (surfacePotential k) u v := by rw [mul_assoc, h]

/-- Extension of character-restricted weak tests on a rotation-invariant domain.
The order-three action and domain preservation are explicit hypotheses. -/
lemma surfaceJacobi_cubic_tests_suffice (k : ℕ) (θ : ℝ) (c : ℂ)
    (hc : c ^ 3 = 1) (hcn : ‖c‖ = 1)
    (hT : ∀ v : ComplexH1, diskRotation θ (diskRotation θ (diskRotation θ v)) = v)
    (D : Submodule ℂ ComplexH1) (hD : ∀ v ∈ D, diskRotation θ v ∈ D)
    (u : ComplexH1) (hu : diskRotation θ u = c • u)
    (hzero : ∀ v ∈ D, diskRotation θ v = c • v → weakJacobi (surfacePotential k) u v = 0) :
    ∀ v ∈ D, weakJacobi (surfacePotential k) u v = 0 := by
  let L : ComplexH1 →ₗ[ℂ] ℂ :=
    { toFun := weakJacobi (surfacePotential k) u
      map_add' := weakJacobi_add_right (surfacePotential k) u
      map_smul' := fun a v => weakJacobi_smul_right (surfacePotential k) a u v }
  exact cubicCharacter_tests_suffice (diskRotation θ).toLinearMap c D hc hT hD L
    (surfaceJacobi_character_test_rotation k θ c hcn u hu) hzero

end KsIndex.Trace
