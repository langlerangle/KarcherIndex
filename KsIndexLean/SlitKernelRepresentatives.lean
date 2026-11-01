module

public import KsIndexLean.SlitReflectionKernels

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1

lemma paperSlitDirichlet_reflection_reconstruct (j : ℕ)
    (x : paperDirichletEvenCharacter j × paperDirichletOddCharacter j) :
    ((paperSlitDirichletCharacterReflectionEquiv j).symm x).val =
      (x.1.val + x.2.val, x.1.val - x.2.val) := rfl

lemma paperDirichletOdd_zero_kernel_span (u : paperDirichletOddCharacter 0)
    (hu : ∀ v : paperDirichletOddCharacter 0, weakJacobi (surfacePotential 3) u v = 0) :
    ∃ c : ℂ, (u : ComplexH1) = c • verticalThreeH1 := by
  let v : fullDirichletCharacter 0 := ⟨u, by
    rw [← paperDirichletOddCharacter_eq_full]; exact u.property⟩
  apply (fullDirichletCharacter_zero_kernel_iff v).mp
  intro w
  exact hu ⟨w, by rw [paperDirichletOddCharacter_eq_full]; exact w.property⟩

private lemma vertical_pair_reconstruct (u : DiskPairH1) (c : ℂ)
    (hr : (0 + c • verticalThreeH1, 0 - c • verticalThreeH1) = u) :
    u = (c • verticalThreeH1, c • (-verticalThreeH1)) := by
  simpa only [zero_add, zero_sub, smul_neg] using hr.symm

lemma paperSlitDirichlet_zero_kernel_span (u : paperSlitDirichletCharacterDomain 0)
    (hu : ∀ v : paperSlitDirichletCharacterDomain 0,
      weakJacobi (surfacePotential 3) u.val.1 v.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 v.val.2 = 0) :
    ∃ c : ℂ, u.val = (c • verticalThreeH1, c • (-verticalThreeH1)) := by
  let e := paperSlitDirichletCharacterReflectionEquiv 0
  obtain ⟨ha, hb⟩ := (paperSlitDirichlet_kernel_reflection_iff 0 u).mp hu
  have hz := paperDirichletEven_kernel_zero (by decide : 0 < 3) (e u).1 ha
  obtain ⟨c, hc⟩ := paperDirichletOdd_zero_kernel_span (e u).2 hb
  have hr := congrArg Subtype.val (e.symm_apply_apply u)
  rw [paperSlitDirichlet_reflection_reconstruct] at hr
  rw [hz, hc] at hr
  exact ⟨c, vertical_pair_reconstruct u.val c hr⟩

lemma paperSlitNeumann_one_kernel_span (u : paperSlitNeumannCharacterDomain 1)
    (hu : ∀ v : paperSlitNeumannCharacterDomain 1,
      weakJacobi (surfacePotential 3) u.val.1 v.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 v.val.2 = 0) :
    ∃ c : ℂ, u.val = (c • horizontalThreeH1, c • horizontalThreeH1) := by
  let e := paperSlitNeumannCharacterReflectionEquiv 1
  obtain ⟨ha, hb⟩ := (paperSlitNeumann_kernel_reflection_iff 1 u).mp hu
  have hz := paperNeumannOdd_kernel_zero (by decide : 1 < 3) (e u).2 hb
  obtain ⟨c, hc⟩ := (paperHemisphere_one_kernel_iff (e u).1).mp ha
  have hr := congrArg Subtype.val (e.symm_apply_apply u)
  change ((e u).1.val + (e u).2.val, (e u).1.val - (e u).2.val) = u.val at hr
  rw [hz, hc] at hr
  exact ⟨c, by simpa only [add_zero, sub_zero] using hr.symm⟩

lemma paperSlitNeumann_two_kernel_span (u : paperSlitNeumannCharacterDomain 2)
    (hu : ∀ v : paperSlitNeumannCharacterDomain 2,
      weakJacobi (surfacePotential 3) u.val.1 v.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 v.val.2 = 0) :
    ∃ c : ℂ, u.val = (c • horizontalThreeConjH1, c • horizontalThreeConjH1) := by
  let e := paperSlitNeumannCharacterReflectionEquiv 2
  obtain ⟨ha, hb⟩ := (paperSlitNeumann_kernel_reflection_iff 2 u).mp hu
  have hz := paperNeumannOdd_kernel_zero (by decide : 2 < 3) (e u).2 hb
  obtain ⟨c, hc⟩ := (paperHemisphere_two_kernel_iff (e u).1).mp ha
  have hr := congrArg Subtype.val (e.symm_apply_apply u)
  change ((e u).1.val + (e u).2.val, (e u).1.val - (e u).2.val) = u.val at hr
  rw [hz, hc] at hr
  exact ⟨c, by simpa only [add_zero, sub_zero] using hr.symm⟩

/-- The Dirichlet zero-character kernel has no nonzero vector satisfying the
nontrivial phase weak equation. -/
lemma paperSlitDirichlet_zero_common_kernel_zero {α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (u : paperSlitDirichletCharacterDomain 0)
    (hu : ∀ v : paperSlitDirichletCharacterDomain 0,
      weakJacobi (surfacePotential 3) u.val.1 v.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 v.val.2 = 0)
    (hp : ∀ v ∈ paperSlitCharacterDomain α 0,
      weakJacobi (surfacePotential 3) u.val.1 v.1 +
        weakJacobi (surfacePotential 3) u.val.2 v.2 = 0) : u.val = 0 :=
  verticalThree_span_paper_weak_zero h0 h1 u.val
    (paperSlitDirichlet_zero_kernel_span u hu) hp

lemma paperSlitNeumann_one_phase_kernel_zero {α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (u : paperSlitNeumannCharacterDomain 1)
    (hu : ∀ v : paperSlitNeumannCharacterDomain 1,
      weakJacobi (surfacePotential 3) u.val.1 v.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 v.val.2 = 0)
    (hp : u.val ∈ paperSlitDomain α) : u.val = 0 := by
  obtain ⟨c, hc⟩ := paperSlitNeumann_one_kernel_span u hu
  rw [hc] at hp ⊢
  have hz := horizontalThree_paper_scalar_zero h0 h1 hp
  simp only [hz, zero_smul, Prod.mk_zero_zero]

lemma paperSlitNeumann_two_phase_kernel_zero {α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) (u : paperSlitNeumannCharacterDomain 2)
    (hu : ∀ v : paperSlitNeumannCharacterDomain 2,
      weakJacobi (surfacePotential 3) u.val.1 v.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 v.val.2 = 0)
    (hp : u.val ∈ paperSlitDomain α) : u.val = 0 := by
  obtain ⟨c, hc⟩ := paperSlitNeumann_two_kernel_span u hu
  rw [hc] at hp ⊢
  have hz := horizontalThreeConj_paper_scalar_zero h0 h1 hp
  simp only [hz, zero_smul, Prod.mk_zero_zero]

end KsIndex.Spectral
