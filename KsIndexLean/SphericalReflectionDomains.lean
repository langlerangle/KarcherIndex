module

public import KsIndexLean.SphericalWeakReflection

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Reflection reverses the ordered slit phase. -/
lemma sphereChartReflection_phase (k : ℕ) (c : ℂ) (hc : c ≠ 0)
    (q : SphericalSlitPhaseSpace k c) :
    sphereChartReflectionEquiv (isOpen_boundaryArc k 1) q.val ∈ sphericalPhaseDomain k c⁻¹ := by
  change arcTrace (boundaryArc k 0) (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
    (sphereChartReflectionEquiv _ q.val)).1 = c⁻¹ • arcTrace (boundaryArc k 0)
      (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) (sphereChartReflectionEquiv _ q.val)).2
  rw [sphereChartReflection_coordinates]
  have hq : arcTrace (boundaryArc k 0) (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) q.val).1 =
      c • arcTrace (boundaryArc k 0) (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) q.val).2 :=
    q.property
  rw [hq, smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma sphereChartReflection_dirichlet (k : ℕ) (q : SphericalSlitDirichletSpace k) :
    sphereChartReflectionEquiv (isOpen_boundaryArc k 1) q.val ∈ sphericalDirichletDomain k := by
  change arcTrace (boundaryArc k 0) (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
    (sphereChartReflectionEquiv _ q.val)).1 = 0 ∧ arcTrace (boundaryArc k 0)
      (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) (sphereChartReflectionEquiv _ q.val)).2 = 0
  rw [sphereChartReflection_coordinates]
  exact ⟨q.property.2, q.property.1⟩

/-- Equatorial reflection preserves the same rotation character, without conjugating it. -/
lemma sphereChartReflection_character_iff {A : Set Circle₁} (hA : IsOpen A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (d : ℂ) (q : SphereChartSpace A hA) :
    sphereChartReflectionEquiv hA q ∈ sphereChartCharacterDomain hA θ hθ d ↔
      q ∈ sphereChartCharacterDomain hA θ hθ d := by
  rw [mem_sphereChartCharacterDomain_iff_pair, mem_sphereChartCharacterDomain_iff_pair,
    sphereChartReflection_coordinates]
  change (_ ∈ weakCharacterDomain θ d ∧ _ ∈ weakCharacterDomain θ d) ↔
    (_ ∈ weakCharacterDomain θ d ∧ _ ∈ weakCharacterDomain θ d)
  exact and_comm

end KsIndex.Spherical
