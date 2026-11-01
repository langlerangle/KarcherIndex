module

public import KsIndexLean.SlitCharacterNullities

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Reflection transports the full weak kernel equation, not merely its
dimension. Each reflected component can be tested independently. -/
lemma pair_reflection_kernel_iff (D : Submodule ℂ DiskPairH1)
    (A B : Submodule ℂ ComplexH1) (V : BoundedRealPotential)
    (e : D ≃ₗ[ℂ] A × B)
    (h : ∀ u v : A × B,
      weakJacobi V (e.symm u).val.1 (e.symm v).val.1 +
      weakJacobi V (e.symm u).val.2 (e.symm v).val.2 =
        2 * (weakJacobi V u.1.val v.1.val + weakJacobi V u.2.val v.2.val))
    (u : D) :
    (∀ v : D, weakJacobi V u.val.1 v.val.1 + weakJacobi V u.val.2 v.val.2 = 0) ↔
      (∀ a : A, weakJacobi V (e u).1 a = 0) ∧
      (∀ b : B, weakJacobi V (e u).2 b = 0) := by
  have he (v : A × B) :
      weakJacobi V u.val.1 (e.symm v).val.1 +
      weakJacobi V u.val.2 (e.symm v).val.2 =
        2 * (weakJacobi V (e u).1 v.1 + weakJacobi V (e u).2 v.2) := by
    simpa only [e.symm_apply_apply] using h (e u) v
  have hz (x : ComplexH1) : weakJacobi V x 0 = 0 := (diskJacobiForm V x).map_zero
  constructor
  · intro hu
    constructor
    · intro a
      have hh := (he (a, 0)).symm.trans (hu (e.symm (a, 0)))
      simpa [hz] using hh
    · intro b
      have hh := (he (0, b)).symm.trans (hu (e.symm (0, b)))
      simpa [hz] using hh
  · rintro ⟨ha, hb⟩ v
    have hh := he (e v)
    have hha := ha (e v).1
    have hhb := hb (e v).2
    simp only [hha, hhb, add_zero, mul_zero] at hh
    simpa only [e.symm_apply_apply] using hh

lemma paperSlitNeumann_kernel_reflection_iff (j : ℕ)
    (u : paperSlitNeumannCharacterDomain j) :
    (∀ v : paperSlitNeumannCharacterDomain j,
      weakJacobi (surfacePotential 3) u.val.1 v.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 v.val.2 = 0) ↔
      (∀ a : paperHemisphereCharacter j, weakJacobi (surfacePotential 3)
        ((paperSlitNeumannCharacterReflectionEquiv j) u).1 a = 0) ∧
      (∀ b : paperNeumannOddCharacter j, weakJacobi (surfacePotential 3)
        ((paperSlitNeumannCharacterReflectionEquiv j) u).2 b = 0) :=
  pair_reflection_kernel_iff _ _ _ _ _ (paperSlitNeumannCharacterReflection_jacobi j _) u

lemma paperSlitDirichlet_kernel_reflection_iff (j : ℕ)
    (u : paperSlitDirichletCharacterDomain j) :
    (∀ v : paperSlitDirichletCharacterDomain j,
      weakJacobi (surfacePotential 3) u.val.1 v.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 v.val.2 = 0) ↔
      (∀ a : paperDirichletEvenCharacter j, weakJacobi (surfacePotential 3)
        ((paperSlitDirichletCharacterReflectionEquiv j) u).1 a = 0) ∧
      (∀ b : paperDirichletOddCharacter j, weakJacobi (surfacePotential 3)
        ((paperSlitDirichletCharacterReflectionEquiv j) u).2 b = 0) :=
  pair_reflection_kernel_iff _ _ _ _ _ (paperSlitDirichletCharacterReflection_jacobi j _) u

end KsIndex.Spectral
