module

public import KsIndexLean.NegativeDirectionKernelExtension
public import KsIndexLean.NeumannCharacterKernels
public import KsIndexLean.WeakMixedIndex
public import KsIndexLean.SlitHorizontalExclusion

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Index-one saturation extends the actual weak Jacobi equation from a
smaller disk domain to a larger disk domain. -/
lemma disk_kernel_extends_of_index_one
    (A B : Submodule ℂ ComplexH1) (hAB : A ≤ B) (V : BoundedRealPotential)
    (hA : diskWeakIndex A V ≠ 0) (hB : diskWeakIndex B V ≤ 1)
    (u : A) (hu : ∀ v : A, weakJacobi V u v = 0) :
    ∀ v : B, weakJacobi V u v = 0 := by
  let : InnerProductSpace ℂ B := diskDomain_innerProductSpace B
  obtain ⟨e, he⟩ := exists_negative_of_index_ne_zero (fun x : A => (weakJacobi V x x).re) hA
  let D : Submodule ℂ B := A.comap B.subtype
  have h := restricted_kernel_extends_of_index_le_one (domainJacobiForm B V)
    (fun x y => weakJacobi_conj V x y) hB D (⟨e, hAB e.property⟩ : B)
    e.property he (⟨u, hAB u.property⟩ : B) u.property
    (fun v hv => hu ⟨v, hv⟩)
  exact h

lemma paperNeumannOdd_kernel_extends {j : ℕ} (hj : j < 3)
    (u : paperNeumannOddCharacter j)
    (hu : ∀ v : paperNeumannOddCharacter j, weakJacobi (surfacePotential 3) u v = 0) :
    ∀ v : paperHemisphereCharacter j, weakJacobi (surfacePotential 3) u v = 0 := by
  apply disk_kernel_extends_of_index_one (paperNeumannOddCharacter j)
    (paperHemisphereCharacter j) inf_le_right (surfacePotential 3) _ _ u hu
  · rw [paperNeumannOddCharacter_eq_DN, mixedDN_weak_index_one (by decide) hj]
    exact one_ne_zero
  · rw [paperHemisphereCharacter_eq_NN, three_pureNeumann_weak_index hj]

lemma paperDirichletEven_kernel_extends {j : ℕ} (hj : j < 3)
    (u : paperDirichletEvenCharacter j)
    (hu : ∀ v : paperDirichletEvenCharacter j, weakJacobi (surfacePotential 3) u v = 0) :
    ∀ v : paperHemisphereCharacter j, weakJacobi (surfacePotential 3) u v = 0 := by
  apply disk_kernel_extends_of_index_one (paperDirichletEvenCharacter j)
    (paperHemisphereCharacter j) inf_le_right (surfacePotential 3) _ _ u hu
  · rw [paperDirichletEvenCharacter_eq_ND, mixedND_weak_index_one (by decide) hj]
    exact one_ne_zero
  · rw [paperHemisphereCharacter_eq_NN, three_pureNeumann_weak_index hj]

lemma boundaryArc_three_one_measure_pos :
    0 < circleMeasure (boundaryArc 3 1) := by
  have hp : circleRotate Real.pi ⁻¹' boundaryArc 3 1 = boundaryArc 3 0 := by
    ext w
    simp only [Set.mem_preimage, mem_boundaryArc]
    change (-1 : ℝ) ^ 1 * ((Complex.exp (Real.pi * Complex.I) * (w : ℂ)) ^ 3).re < 0 ↔ _
    simp only [Complex.exp_pi_mul_I, neg_one_mul, pow_one, pow_zero, one_mul]
    have hn : (-(w : ℂ)) ^ 3 = -((w : ℂ) ^ 3) := by ring
    rw [hn, Complex.neg_re]
    simp only [neg_neg]
  have hm := (measurePreserving_circleRotate Real.pi).measure_preimage
    ((measurableSet_boundaryArc 3 1).nullMeasurableSet)
  rw [hp] at hm
  rw [← hm]
  exact boundaryArc_three_zero_measure_pos

lemma horizontalThree_arc1_trace_ne_zero :
    arcTrace (boundaryArc 3 1) horizontalThreeH1 ≠ 0 :=
  arcTrace_ne_zero_of_ae_nonzero _ _ (ne_of_gt boundaryArc_three_one_measure_pos)
    horizontalThreeH1_trace_ne_zero_ae

lemma horizontalThreeConj_arc1_trace_ne_zero :
    arcTrace (boundaryArc 3 1) horizontalThreeConjH1 ≠ 0 :=
  arcTrace_ne_zero_of_ae_nonzero _ _ (ne_of_gt boundaryArc_three_one_measure_pos)
    horizontalThreeConjH1_trace_ne_zero_ae

/-- A Neumann character kernel vector with zero trace on an arc where both
horizontal modes are nonzero must vanish. -/
lemma paperHemisphere_kernel_zero_of_arc {j : ℕ} (hj : j < 3)
    (A : Set Circle₁)
    (hp : arcTrace A horizontalThreeH1 ≠ 0)
    (hm : arcTrace A horizontalThreeConjH1 ≠ 0)
    (u : paperHemisphereCharacter j)
    (hu : ∀ v : paperHemisphereCharacter j, weakJacobi (surfacePotential 3) u v = 0)
    (ht : arcTrace A u = 0) : (u : ComplexH1) = 0 := by
  interval_cases j
  · exact paperHemisphere_zero_kernel u hu
  · obtain ⟨c, hc⟩ := (paperHemisphere_one_kernel_iff u).mp hu
    rw [hc, map_smul] at ht
    have hz : c = 0 := (smul_eq_zero.mp ht).resolve_right hp
    simp [hc, hz]
  · obtain ⟨c, hc⟩ := (paperHemisphere_two_kernel_iff u).mp hu
    rw [hc, map_smul] at ht
    have hz : c = 0 := (smul_eq_zero.mp ht).resolve_right hm
    simp [hc, hz]

lemma paperNeumannOdd_kernel_zero {j : ℕ} (hj : j < 3)
    (u : paperNeumannOddCharacter j)
    (hu : ∀ v : paperNeumannOddCharacter j, weakJacobi (surfacePotential 3) u v = 0) :
    (u : ComplexH1) = 0 :=
  paperHemisphere_kernel_zero_of_arc hj (boundaryArc 3 1)
    horizontalThree_arc1_trace_ne_zero horizontalThreeConj_arc1_trace_ne_zero
    ⟨u, u.property.2⟩ (paperNeumannOdd_kernel_extends hj u hu) u.property.1

lemma paperDirichletEven_kernel_zero {j : ℕ} (hj : j < 3)
    (u : paperDirichletEvenCharacter j)
    (hu : ∀ v : paperDirichletEvenCharacter j, weakJacobi (surfacePotential 3) u v = 0) :
    (u : ComplexH1) = 0 :=
  paperHemisphere_kernel_zero_of_arc hj (boundaryArc 3 0)
    horizontalThree_arc0_trace_ne_zero horizontalThreeConj_arc0_trace_ne_zero
    ⟨u, u.property.2⟩ (paperDirichletEven_kernel_extends hj u hu) u.property.1

lemma paperNeumannOdd_radical_zero {j : ℕ} (hj : j < 3) :
    formRadical (domainJacobiForm (paperNeumannOddCharacter j) (surfacePotential 3)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro u hu
  change u = 0
  apply Subtype.ext
  exact paperNeumannOdd_kernel_zero hj u (fun v => (mem_formRadical _ u).mp hu v)

lemma paperNeumannOdd_nullity_zero {j : ℕ} (hj : j < 3) :
    diskWeakNullity (paperNeumannOddCharacter j) (surfacePotential 3) = 0 := by
  unfold diskWeakNullity
  rw [paperNeumannOdd_radical_zero hj]
  exact finrank_bot ℂ _

lemma paperDirichletEven_radical_zero {j : ℕ} (hj : j < 3) :
    formRadical (domainJacobiForm (paperDirichletEvenCharacter j) (surfacePotential 3)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro u hu
  change u = 0
  apply Subtype.ext
  exact paperDirichletEven_kernel_zero hj u (fun v => (mem_formRadical _ u).mp hu v)

lemma paperDirichletEven_nullity_zero {j : ℕ} (hj : j < 3) :
    diskWeakNullity (paperDirichletEvenCharacter j) (surfacePotential 3) = 0 := by
  unfold diskWeakNullity
  rw [paperDirichletEven_radical_zero hj]
  exact finrank_bot ℂ _

end KsIndex.Spectral
