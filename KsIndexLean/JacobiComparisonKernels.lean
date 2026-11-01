module

public import KsIndexLean.JacobiWeakCharacters
public import KsIndexLean.FullBoundaryMatching

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Dirichlet slit tests have matching full boundary traces: on the unslit arc
by transmission, and on the slit because both traces vanish. -/
lemma slitDirichlet_difference_zeroTrace {k : ℕ} (hk : 1 ≤ k)
    (v : slitDirichletDomain k) : v.val.1 - v.val.2 ∈ zeroTraceDomain Set.univ := by
  have h1 := (mem_transmissionDomain _ _ v.val).mp v.property.1.1
  rw [one_smul] at h1
  have h0a : arcTrace (boundaryArc k 0) v.val.1 = 0 := v.property.1.2
  have h0b : arcTrace (boundaryArc k 0) v.val.2 = 0 := v.property.2
  have hfull := (full_trace_eq_iff_arcs hk v.val.1 v.val.2).mpr ⟨h1, h0a.trans h0b.symm⟩
  change arcTrace Set.univ (v.val.1 - v.val.2) = 0
  rw [map_sub, hfull, sub_self]

/-- The antisymmetric vertical pair annihilates all slit Dirichlet tests,
including tests not restricted to its character. -/
lemma verticalThree_pair_Dirichlet_weak (v : slitDirichletDomain 3) :
    weakJacobi (surfacePotential 3) verticalThreeH1 v.val.1 +
      weakJacobi (surfacePotential 3) (-verticalThreeH1) v.val.2 = 0 := by
  have h := verticalThree_dirichlet_weak
    ⟨v.val.1 - v.val.2, slitDirichlet_difference_zeroTrace (by decide) v⟩
  change weakJacobi (surfacePotential 3) verticalThreeH1 (v.val.1 - v.val.2) = 0 at h
  simp only [sub_eq_add_neg, ← neg_one_smul ℂ v.val.2,
    weakJacobi_add_right, weakJacobi_smul_right] at h
  rw [← neg_one_smul ℂ verticalThreeH1, weakJacobi_smul_left, map_neg, map_one]
  exact h

lemma verticalThree_pair_Dirichlet_character_weak
    (v : KsIndex.Spectral.paperSlitDirichletCharacterDomain 0) :
    weakJacobi (surfacePotential 3) verticalThreeH1 v.val.1 +
      weakJacobi (surfacePotential 3) (-verticalThreeH1) v.val.2 = 0 :=
  verticalThree_pair_Dirichlet_weak ⟨v.val, v.property.1⟩

lemma horizontalThree_pair_weak (v : DiskPairH1) :
    weakJacobi (surfacePotential 3) horizontalThreeH1 v.1 +
      weakJacobi (surfacePotential 3) horizontalThreeH1 v.2 = 0 := by
  rw [horizontalThree_weak_neumann, horizontalThree_weak_neumann, add_zero]

lemma horizontalThreeConj_pair_weak (v : DiskPairH1) :
    weakJacobi (surfacePotential 3) horizontalThreeConjH1 v.1 +
      weakJacobi (surfacePotential 3) horizontalThreeConjH1 v.2 = 0 := by
  rw [horizontalThreeConj_weak_neumann, horizontalThreeConj_weak_neumann, add_zero]

lemma horizontalThreeH1_ne_zero : horizontalThreeH1 ≠ 0 := by
  intro h
  apply horizontalThree_arc0_trace_ne_zero
  rw [h, map_zero]

lemma horizontalThreeConjH1_ne_zero : horizontalThreeConjH1 ≠ 0 := by
  intro h
  apply horizontalThreeConj_arc0_trace_ne_zero
  rw [h, map_zero]

lemma verticalThreeH1_ne_zero : verticalThreeH1 ≠ 0 := by
  intro h
  have hn := verticalThree_phase_test_pairing_ne_zero (phase := 0) (by norm_num)
  apply hn
  rw [h, neg_zero]
  have hz (v : ComplexH1) : weakJacobi (surfacePotential 3) 0 v = 0 := by
    simpa only [zero_smul, map_zero, zero_mul] using
      (weakJacobi_smul_left (surfacePotential 3) (0 : ℂ) (0 : ComplexH1) v)
  rw [hz, hz, add_zero]

end KsIndex.Trace

namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1

/-- Transport an explicit nonzero weak pair solution into the Hilbert form
used by the ordered spectral realization. -/
lemma pair_nonzero_weak_kernel (D : Submodule ℂ DiskPairH1) (V : BoundedRealPotential)
    (u : D) (hu : u ≠ 0)
    (hQ : ∀ v : D, weakJacobi V u.val.1 v.val.1 + weakJacobi V u.val.2 v.val.2 = 0) :
    ∃ f : finiteH1Domain (pairFiniteDomain D), f ≠ 0 ∧
      ∀ g, finiteJacobiForm (pairFiniteDomain D) V f g = 0 := by
  let f := (pairHilbertCoordinates D).symm u
  refine ⟨f, ?_, ?_⟩
  · intro hz
    apply hu
    have he := congrArg (pairHilbertCoordinates D) hz
    simpa only [f, LinearEquiv.apply_symm_apply, map_zero] using he
  · intro g
    rw [finiteJacobiForm_apply, pairFiniteJacobi_eq]
    change weakJacobi V ((pairHilbertCoordinates D) ((pairHilbertCoordinates D).symm u)).val.1 _ +
      weakJacobi V ((pairHilbertCoordinates D) ((pairHilbertCoordinates D).symm u)).val.2 _ = 0
    rw [LinearEquiv.apply_symm_apply]
    exact hQ (pairHilbertCoordinates D g)

lemma paperDirichlet_zero_nontrivial_kernel :
    ∃ f : finiteH1Domain (pairFiniteDomain (paperSlitDirichletCharacterDomain 0)), f ≠ 0 ∧
      ∀ g, finiteJacobiForm (pairFiniteDomain (paperSlitDirichletCharacterDomain 0))
        (surfacePotential 3) f g = 0 := by
  apply pair_nonzero_weak_kernel _ _
    ⟨(verticalThreeH1, -verticalThreeH1), verticalThree_pair_Dirichlet_character⟩
  · intro h
    exact verticalThreeH1_ne_zero (congrArg (fun u => u.val.1) h)
  · exact verticalThree_pair_Dirichlet_character_weak

lemma paperNeumann_one_nontrivial_kernel :
    ∃ f : finiteH1Domain (pairFiniteDomain (paperSlitNeumannCharacterDomain 1)), f ≠ 0 ∧
      ∀ g, finiteJacobiForm (pairFiniteDomain (paperSlitNeumannCharacterDomain 1))
        (surfacePotential 3) f g = 0 := by
  apply pair_nonzero_weak_kernel _ _
    ⟨(horizontalThreeH1, horizontalThreeH1), horizontalThree_pair_Neumann_character⟩
  · intro h
    exact horizontalThreeH1_ne_zero (congrArg (fun u => u.val.1) h)
  · intro v
    exact horizontalThree_pair_weak v.val

lemma paperNeumann_two_nontrivial_kernel :
    ∃ f : finiteH1Domain (pairFiniteDomain (paperSlitNeumannCharacterDomain 2)), f ≠ 0 ∧
      ∀ g, finiteJacobiForm (pairFiniteDomain (paperSlitNeumannCharacterDomain 2))
        (surfacePotential 3) f g = 0 := by
  apply pair_nonzero_weak_kernel _ _
    ⟨(horizontalThreeConjH1, horizontalThreeConjH1), horizontalThreeConj_pair_Neumann_character⟩
  · intro h
    exact horizontalThreeConjH1_ne_zero (congrArg (fun u => u.val.1) h)
  · intro v
    exact horizontalThreeConj_pair_weak v.val

end KsIndex.Spectral
