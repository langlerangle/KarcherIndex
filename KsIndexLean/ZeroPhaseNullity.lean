module

/-
# Zero-phase nullity per character

For k = 3 and each j < 3, the zero-phase pair form has nullity one.
The proof transports the form along `paperZeroPhaseReflectionEquiv j`
to the product of the Neumann and Dirichlet character domains.
`paperZeroPhaseReflection_jacobi` identifies the pair form with twice
the sum of the two domain forms. The nonzero factor does not change
nullity, and the radical of the sum is the product of the radicals.

The pure-sector nullities are [j ≠ 0] and [j = 0], respectively, so their
sum is one. The result uses the same `sesqNullity` pair functional as
`paperSlit_nullity_eq_sectorClass` for interior phases.
-/
public import KsIndexLean.ZeroPhaseReflectionIndex
public import KsIndexLean.PureSectorValues
public import KsIndexLean.PositiveBlockCounts
public import KsIndexLean.JacobiRadicalRealization

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Trace KsIndex.DtnBridge

/-- A product of submodules, as a module, is the product of the modules. -/
def submoduleProdEquiv {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : Submodule R M) (q : Submodule R N) :
    (p.prod q) ≃ₗ[R] p × q where
  toFun x := (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
  invFun y := ⟨(y.1.val, y.2.val), ⟨y.1.property, y.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option maxHeartbeats 1600000 in
-- The product-radical membership (h3) requires expensive nested-subtype
-- `isDefEq` (prod ∘ formRadical ∘ domainJacobiForm on submodule carriers);
-- bump to let it complete.
/-- The zero-phase pair-form nullity is one for each of the three characters. -/
theorem paperSlit_zeroPhase_nullity {j : ℕ} (hj : j < 3) :
    sesqNullity (fun u v : paperSlitCharacterDomain 0 j =>
        weakJacobi (surfacePotential 3) u.val.1 v.val.1
      + weakJacobi (surfacePotential 3) u.val.2 v.val.2) = 1 := by
  classical
  -- step 1: transport along the reflection product decomposition
  have h1 : sesqNullity (fun u v : paperSlitCharacterDomain 0 j =>
        weakJacobi (surfacePotential 3) u.val.1 v.val.1
      + weakJacobi (surfacePotential 3) u.val.2 v.val.2)
      = sesqNullity (fun u v : ↥(mixedCharacterDomain 3 j true true)
            × ↥(mixedCharacterDomain 3 j false false) =>
          2 * (weakJacobi (surfacePotential 3) u.1.val v.1.val
            + weakJacobi (surfacePotential 3) u.2.val v.2.val)) :=
    sesqNullity_congr (paperZeroPhaseReflectionEquiv j).symm
      (fun u v : ↥(mixedCharacterDomain 3 j true true)
          × ↥(mixedCharacterDomain 3 j false false) =>
        2 * (weakJacobi (surfacePotential 3) u.1.val v.1.val
          + weakJacobi (surfacePotential 3) u.2.val v.2.val))
      (fun u v : paperSlitCharacterDomain 0 j =>
        weakJacobi (surfacePotential 3) u.val.1 v.val.1
      + weakJacobi (surfacePotential 3) u.val.2 v.val.2)
      (fun u v => paperZeroPhaseReflection_jacobi j (surfacePotential 3) u v)
  -- step 2: strip the factor 2
  have h2 : sesqNullity (fun u v : ↥(mixedCharacterDomain 3 j true true)
          × ↥(mixedCharacterDomain 3 j false false) =>
        2 * (weakJacobi (surfacePotential 3) u.1.val v.1.val
          + weakJacobi (surfacePotential 3) u.2.val v.2.val))
      = sesqNullity (fun u v : ↥(mixedCharacterDomain 3 j true true)
            × ↥(mixedCharacterDomain 3 j false false) =>
          weakJacobi (surfacePotential 3) u.1.val v.1.val
        + weakJacobi (surfacePotential 3) u.2.val v.2.val) :=
    sesqNullity_nonzero_mul _ 2 two_ne_zero
  -- step 3: the radical of the sum form is the product of the radicals
  have hfNN : FiniteDimensional ℂ
      (formRadical (domainJacobiForm (mixedCharacterDomain 3 j true true)
        (surfacePotential 3))) :=
    diskRadical_finiteDimensional (mixedCharacterDomain 3 j true true)
      (surfacePotential 3)
  have hfDD : FiniteDimensional ℂ
      (formRadical (domainJacobiForm (mixedCharacterDomain 3 j false false)
        (surfacePotential 3))) :=
    diskRadical_finiteDimensional (mixedCharacterDomain 3 j false false)
      (surfacePotential 3)
  have hKfin : FiniteDimensional ℂ
      ((formRadical (domainJacobiForm (mixedCharacterDomain 3 j true true)
          (surfacePotential 3))).prod
        (formRadical (domainJacobiForm (mixedCharacterDomain 3 j false false)
          (surfacePotential 3)))) :=
    (submoduleProdEquiv _ _).symm.finiteDimensional
  have h3 : sesqNullity (fun u v : ↥(mixedCharacterDomain 3 j true true)
          × ↥(mixedCharacterDomain 3 j false false) =>
        weakJacobi (surfacePotential 3) u.1.val v.1.val
      + weakJacobi (surfacePotential 3) u.2.val v.2.val)
      = (Module.finrank ℂ
          ((formRadical (domainJacobiForm (mixedCharacterDomain 3 j true true)
              (surfacePotential 3))).prod
            (formRadical (domainJacobiForm (mixedCharacterDomain 3 j false false)
              (surfacePotential 3)))) : ℕ∞) := by
    apply sesqNullity_eq_finrank_radical
    intro u
    rw [Submodule.mem_prod,
      mem_formRadical (domainJacobiForm (mixedCharacterDomain 3 j true true)
        (surfacePotential 3)),
      mem_formRadical (domainJacobiForm (mixedCharacterDomain 3 j false false)
        (surfacePotential 3))]
    constructor
    · rintro ⟨hu1, hu2⟩ w
      have e1 := hu1 w.1
      have e2 := hu2 w.2
      rw [domainJacobiForm_apply] at e1 e2
      rw [e1, e2, add_zero]
    · intro hu
      constructor
      · intro w
        have h0 := hu (w, 0)
        have hz : weakJacobi (surfacePotential 3) u.2.val
            ((0 : ↥(mixedCharacterDomain 3 j false false)) : ComplexH1) = 0 := by
          have hmap := (domainJacobiForm (mixedCharacterDomain 3 j false false)
            (surfacePotential 3) u.2).map_zero
          rwa [domainJacobiForm_apply] at hmap
        rw [domainJacobiForm_apply]
        simp only at h0
        rw [hz, add_zero] at h0
        exact h0
      · intro w
        have h0 := hu (0, w)
        have hz : weakJacobi (surfacePotential 3) u.1.val
            ((0 : ↥(mixedCharacterDomain 3 j true true)) : ComplexH1) = 0 := by
          have hmap := (domainJacobiForm (mixedCharacterDomain 3 j true true)
            (surfacePotential 3) u.1).map_zero
          rwa [domainJacobiForm_apply] at hmap
        rw [domainJacobiForm_apply]
        simp only at h0
        rw [hz, zero_add] at h0
        exact h0
  -- step 4: finrank of the product = the two pure-sector counts
  have h4 : Module.finrank ℂ
      ((formRadical (domainJacobiForm (mixedCharacterDomain 3 j true true)
          (surfacePotential 3))).prod
        (formRadical (domainJacobiForm (mixedCharacterDomain 3 j false false)
          (surfacePotential 3))))
      = diskWeakNullity (mixedCharacterDomain 3 j true true) (surfacePotential 3)
        + diskWeakNullity (mixedCharacterDomain 3 j false false)
            (surfacePotential 3) := by
    rw [(submoduleProdEquiv _ _).finrank_eq, Module.finrank_prod]
    rfl
  -- step 5: the table values
  rw [h1, h2, h3, h4,
    pureSector_neumann_nullity j hj, pureSector_dirichlet_nullity j hj]
  rcases eq_or_ne j 0 with h | h <;> simp [h]

end KsIndex.Spectral
