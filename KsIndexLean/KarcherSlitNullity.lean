module

public import KsIndexLean.KarcherJacobiEquivalence
public import KsIndexLean.PaperRadicalFiberSurjective

@[expose] public section

/-! Actual geometric joint-character Jacobi fields and the spherical slit kernel.
The translation and rotation characters are identified on the EW quotient itself. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.NullityDecomp KsIndex.Spectral
variable {m : ℕ} [Fact (2 ≤ 3)] [NeZero m] (R : PaperHalfPeriodRealization 3)

/-- Uncurried canonical encoding of actual bounded geometric Jacobi fields. -/
def geometricFiberEncoding : R.boundedGeometricJacobi (m := m) →ₗ[ℂ]
    (ZMod (2 * m) × ℂ → ℂ) :=
  (uncurryE m).toLinearMap.comp
    ((BoundedJacobi 3 m).subtype.comp R.geometricJacobiEquiv.toLinearMap)

/-- The geometric subspace corresponding to a joint translation/rotation fiber. -/
def geometricJointFiber (n j : ℕ) : Submodule ℂ (R.boundedGeometricJacobi (m := m)) :=
  (isotypicFiber 3 m j n).comap (R.geometricFiberEncoding (m := m))

lemma mem_geometricJointFiber (n j : ℕ) (G : R.boundedGeometricJacobi (m := m)) :
    G ∈ R.geometricJointFiber (m := m) n j ↔
      (∀ q, G.val (HeightLift.periodDeck m 1 q) = FormIndex.zeta m ^ n * G.val q) ∧
      (∀ q, G.val (R.periodRotation m q) = FormIndex.zeta 3 ^ j * G.val q) := by
  rw [R.geometricJacobiEquiv_translation_character,
    R.geometricJacobiEquiv_rotation_character]
  change ((R.geometricFiberEncoding G ∈ BoundedJacobiE 3 m ∧
    R.geometricFiberEncoding G ∈ Module.End.eigenspace (rotE m (rotUnit 3 : ℂ))
      (FormIndex.zeta 3 ^ j)) ∧
    R.geometricFiberEncoding G ∈ Module.End.eigenspace (shiftE m) (FormIndex.zeta m ^ n)) ↔ _
  have hb : R.geometricFiberEncoding G ∈ BoundedJacobiE 3 m := by
    rw [mem_boundedJacobiE]
    exact (R.geometricJacobiEquiv G).property
  simp only [hb, true_and, Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨hr, ht⟩
    exact ⟨fun a z => congrFun ht (a,z), fun a z => congrFun hr (a,z)⟩
  · rintro ⟨ht, hr⟩
    exact ⟨funext (fun p => hr p.1 p.2), funext (fun p => ht p.1 p.2)⟩

def geometricJointFiberToModel (n j : ℕ) :
    R.geometricJointFiber (m := m) n j →ₗ[ℂ] isotypicFiber 3 m j n :=
  (R.geometricFiberEncoding (m := m).comp
    (R.geometricJointFiber (m := m) n j).subtype).codRestrict _
    (fun u => u.property)

lemma geometricJointFiberToModel_bijective (n j : ℕ) :
    Function.Bijective (R.geometricJointFiberToModel (m := m) n j) := by
  constructor
  · intro u v h
    apply Subtype.ext
    apply R.geometricJacobiEquiv.injective
    apply Subtype.ext
    apply (uncurryE m).injective
    exact congrArg Subtype.val h
  · intro w
    have hw : (uncurryE m).symm w.val ∈ BoundedJacobi 3 m :=
      mem_boundedJacobiE.mp w.property.1.1
    let v : BoundedJacobi 3 m := ⟨(uncurryE m).symm w.val, hw⟩
    let g := R.geometricJacobiEquiv.symm v
    have he : R.geometricFiberEncoding (m := m) g = w.val := by
      change uncurryE m (R.geometricJacobiEquiv (R.geometricJacobiEquiv.symm v)).val = _
      rw [LinearEquiv.apply_symm_apply]
      exact (uncurryE m).apply_symm_apply w.val
    refine ⟨⟨g, ?_⟩, ?_⟩
    · change R.geometricFiberEncoding (m := m) g ∈ isotypicFiber 3 m j n
      rw [he]
      exact w.property
    · exact Subtype.ext he

/-- The actual geometric joint fiber is equivalent to the spherical weak kernel. -/
def geometricJointFiberSphereEquiv (n j : ℕ) :
    R.geometricJointFiber (m := m) n j ≃ₗ[ℂ]
      paperSphericalCharacterRadical ((n : ℝ) / m) j (WeakH1.surfacePotential 3) :=
  (LinearEquiv.ofBijective (R.geometricJointFiberToModel (m := m) n j)
    (R.geometricJointFiberToModel_bijective (m := m) n j)).trans
      (PaperSlitTransport.fiberSphereRadicalEquiv m n j)

theorem geometricJointFiber_finrank_eq_sphere (n j : ℕ) :
    Module.finrank ℂ (R.geometricJointFiber (m := m) n j) =
      Module.finrank ℂ
        (paperSphericalCharacterRadical ((n : ℝ) / m) j (WeakH1.surfacePotential 3)) :=
  (R.geometricJointFiberSphereEquiv (m := m) n j).finrank_eq
end KsIndex.KarcherData.PaperHalfPeriodRealization
