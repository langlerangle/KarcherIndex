module

public import KsIndexLean.KarcherGeometricInvariants
public import KsIndexLean.KarcherSectorDescent
public import KsIndexLean.PaperSmoothSectorIndexEquality
public import KsIndexLean.PaperSlitCharacterInvariants

@[expose] public section

/-! Compact smooth joint-character sectors on the actual EW quotient and
index transport to the spherical slit form by surjective descent. -/
noncomputable section
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.Spectral KsIndex.FormIndex
variable {m : ℕ} [h : Fact (2 ≤ 3)] [NeZero m] (R : PaperHalfPeriodRealization 3)
local instance sectorQuotientCharted : ChartedSpace ℂ
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint 3) R.C) m) :=
  HeightLift.periodChartedSpace R.hC m

def geometricTestDescent : (ZMod (2 * m) × ℂ → ℂ) →ₗ[ℂ]
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint 3) R.C) m → ℂ) :=
  R.modelTestFunction.comp (uncurryE m).symm.toLinearMap

/-- The image of the compact smooth joint sector on the actual geometric quotient. -/
def geometricSmoothJointSector (n j : ℕ) :=
  (paperSmoothJointSector m n j).map (R.geometricTestDescent (m := m))

lemma mem_geometricSmoothJointSector (n j : ℕ) (f : HeightLift.PeriodQuotient
    (extendedEWMap h.out (reflectionBasepoint 3) R.C) m → ℂ) :
    f ∈ R.geometricSmoothJointSector (m := m) n j ↔
      ((ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f) ∧
      (∀ q, f (HeightLift.periodDeck m 1 q) = zeta m ^ n * f q) ∧
      (∀ q, f (R.periodRotation m q) = zeta 3 ^ j * f q)) := by
  rw [R.compactSmooth_sector_iff_descent]
  constructor
  · rintro ⟨u, hu, rfl⟩
    let v : CcSmooth 3 m := ⟨(uncurryE m).symm u, SurfaceForm.mem_Dom.mp hu.1.1⟩
    refine ⟨v, ?_, ?_, rfl⟩
    · intro a z
      exact congrFun (Module.End.mem_eigenspace_iff.mp hu.2) (a,z)
    · intro a z
      exact congrFun (Module.End.mem_eigenspace_iff.mp hu.1.2) (a,z)
  · rintro ⟨v, ht, hr, he⟩
    refine ⟨uncurryE m v.val, ?_, ?_⟩
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact ⟨v.val, v.property, rfl⟩
      · apply Module.End.mem_eigenspace_iff.mpr
        exact funext (fun p => hr p.1 p.2)
      · apply Module.End.mem_eigenspace_iff.mpr
        exact funext (fun p => ht p.1 p.2)
    · exact he

lemma geometricSmoothJointSector_index_eq_model (n j : ℕ) :
    formIndex R.quotientJacobiQ (R.geometricSmoothJointSector (m := m) n j) =
      formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m n j) := by
  have hmap : ∀ u ∈ paperSmoothJointSector m n j,
      R.geometricTestDescent u ∈ R.geometricSmoothJointSector (m := m) n j :=
    fun u hu => ⟨u, hu, rfl⟩
  have hsurj : ∀ f ∈ R.geometricSmoothJointSector (m := m) n j,
      ∃ u ∈ paperSmoothJointSector m n j, R.geometricTestDescent u = f := by
    intro f hf
    exact hf
  have hform : ∀ u ∈ paperSmoothJointSector m n j,
      SurfaceForm.Qs 3 m u = R.quotientJacobiQ (R.geometricTestDescent u) := by
    intro u hu
    let v : CcSmooth 3 m := ⟨(uncurryE m).symm u, SurfaceForm.mem_Dom.mp hu.1.1⟩
    have hs := R.modelTestFunction_compactSmooth v
    change Surface.jacobiQ 3 m v.val = R.quotientJacobiQ (R.modelTestFunction v.val)
    rw [R.compactSmooth_quotientJacobiQ_eq_model _ hs.1 hs.2, R.modelTestFunction_modelForm]
  have hz := hform 0 (Submodule.zero_mem _)
  rw [map_zero] at hz
  have h0 : R.quotientJacobiQ (0 : HeightLift.PeriodQuotient
      (extendedEWMap h.out (reflectionBasepoint 3) R.C) m → ℂ) = 0 := by
    rw [← hz]
    simp [SurfaceForm.Qs, Surface.jacobiQ, Surface.gradSq, Surface.dirichletG, Surface.potentialG]
  exact (formIndex_transport_surj (R.geometricTestDescent (m := m)) hmap hsurj hform h0).symm

/-- The actual geometric joint-sector index equals the spherical slit index. -/
theorem geometricSmoothJointSector_index_eq_sphere (n j : ℕ) :
    formIndex R.quotientJacobiQ (R.geometricSmoothJointSector (m := m) n j) =
      NegativeDensity.negativeIndex (fun u : paperSphericalPhaseCharacter
          ((n : ℝ) / m) j =>
        (Spherical.sphereChartJacobi (Trace.isOpen_boundaryArc 3 1)
          (WeakH1.surfacePotential 3) u.val.val u.val.val).re) := by
  rw [R.geometricSmoothJointSector_index_eq_model, paperSmoothSector_index_eq_slit]
  let e := paperSlitCharacterSphereEquiv ((n : ℝ) / m) j
  let Q := fun u : paperSphericalPhaseCharacter ((n : ℝ) / m) j =>
    (Spherical.sphereChartJacobi (Trace.isOpen_boundaryArc 3 1)
      (WeakH1.surfacePotential 3) u.val.val u.val.val).re
  have hz : Q 0 = 0 := by
    have he := paperSlitCharacterSphere_jacobi ((n : ℝ) / m) j
      (WeakH1.surfacePotential 3) 0 0
    have hzero : paperSlitCharacterSphereEquiv ((n : ℝ) / m) j 0 = 0 :=
      map_zero (paperSlitCharacterSphereEquiv ((n : ℝ) / m) j)
    rw [hzero] at he
    have hw : WeakH1.weakJacobi (WeakH1.surfacePotential 3) 0 0 = 0 := by
      have hh := WeakH1.weakJacobi_add_left (WeakH1.surfacePotential 3) 0 0 0
      simp only [add_zero] at hh
      linear_combination -hh
    change (Spherical.sphereChartJacobi _ _ _ _).re = 0
    rw [he]
    change (WeakH1.weakJacobi _ 0 0 + WeakH1.weakJacobi _ 0 0).re = 0
    rw [hw, add_zero, Complex.zero_re]
  have he := NegativeDensity.negativeIndex_linearEquiv
    (E := Trace.paperSlitCharacterDomain ((n : ℝ) / m) j)
    (F := paperSphericalPhaseCharacter ((n : ℝ) / m) j) e Q hz
  simpa only [e, Q, paperSlitCharacterSphere_jacobi] using he

end KsIndex.KarcherData.PaperHalfPeriodRealization
