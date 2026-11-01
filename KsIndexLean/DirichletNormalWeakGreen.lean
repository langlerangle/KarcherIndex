module

public import KsIndexLean.DiskAngularSeparation

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- Full weak Green identity for every Dirichlet weak eigenfunction, with
normal flux constructed from its proved finite Fourier support. Neither
smoothness of the eigenfunction nor density of a chosen test class is assumed. -/
theorem sphericalEigen_dirichlet_normal_weak_green
    (k : ℕ) (lam : ℝ) (u : ComplexH1) (ht : u ∈ zeroTraceDomain Set.univ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (v : ComplexH1) :
    weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u v =
      inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ (dirichletNormalPolynomial k lam u ht hu))
        (diskTraceCLM v) := by
  let V := sphericalEigenPotential (surfacePotential k) lam
  let F := ContinuousMap.toLp 2 circleMeasure ℂ (dirichletNormalPolynomial k lam u ht hu)
  let L : ComplexH1 →L[ℂ] ℂ :=
    { toFun := fun w => weakJacobi V u w - inner ℂ F (diskTraceCLM w)
      map_add' := by
        intro a b
        simp only [weakJacobi_add_right, map_add, inner_add_right]
        ring
      map_smul' := by
        intro c w
        simp only [weakJacobi_smul_right, map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]
        ring
      cont := (continuous_weakJacobi_fixed_left V u).sub
        (continuous_const.inner diskTraceCLM.continuous) }
  have hz : L v = 0 := finiteFourierTraceTests_annihilator L (by
    rintro w ⟨s, c, hw⟩
    exact sub_eq_zero.mpr (sphericalEigen_normal_pairing_finite_trace k lam u ht hu s c w hw)) v
  exact sub_eq_zero.mp hz

end KsIndex.Trace
