module

public import KsIndexLean.SlitFluxTest

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- For a phase parameter in (0, 1), the exponential phase is not one.
No rationality hypothesis is needed. -/
lemma paperPhase_ne_one {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    Complex.exp ((2 * Real.pi * α) * Complex.I) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have he : ((2 * Real.pi * α : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    push_cast
    rw [hn]
    ring
  have hr : 2 * Real.pi * α = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast he
  have ha : α = (n : ℝ) := by nlinarith [Real.pi_pos]
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (ha ▸ h0)
  have hn1 : n < (1 : ℤ) := by exact_mod_cast (ha ▸ h1)
  omega

/-- Every scalar multiple of the vertical pair that satisfies the nontrivial
phase weak equation in character zero is the zero multiple. -/
lemma verticalThree_phase_weak_scalar_zero {phase a : ℂ} (hp : phase ≠ 1)
    (hker : ∀ v ∈ slitTraceDomain 3 phase ⊓ pairCharacterDomain (-(2 * Real.pi) / 3) 1,
      weakJacobi (surfacePotential 3) (a • verticalThreeH1) v.1 +
        weakJacobi (surfacePotential 3) (a • (-verticalThreeH1)) v.2 = 0) : a = 0 := by
  have h := hker (slitFluxTestPair phase)
    ⟨slitFluxTestPair_mem_phase phase, slitFluxTestPair_mem_character_zero phase⟩
  rw [weakJacobi_smul_left, weakJacobi_smul_left, ← mul_add] at h
  have ha := (mul_eq_zero.mp h).resolve_right (verticalThree_phase_test_pairing_ne_zero hp)
  exact (starRingEnd ℂ).injective (ha.trans (map_zero (starRingEnd ℂ)).symm)

lemma verticalThree_paper_weak_scalar_zero {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {a : ℂ}
    (hker : ∀ v ∈ paperSlitCharacterDomain α 0,
      weakJacobi (surfacePotential 3) (a • verticalThreeH1) v.1 +
        weakJacobi (surfacePotential 3) (a • (-verticalThreeH1)) v.2 = 0) : a = 0 := by
  apply verticalThree_phase_weak_scalar_zero (paperPhase_ne_one h0 h1)
  simpa only [paperSlitCharacterDomain, paperSlitDomain, pow_zero] using hker

/-- A pair in the vertical span that satisfies the nontrivial phase weak
equation is zero. Membership in the vertical span is an explicit hypothesis. -/
lemma verticalThree_span_paper_weak_zero {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (u : DiskPairH1) (hspan : ∃ a : ℂ, u = (a • verticalThreeH1, a • (-verticalThreeH1)))
    (hker : ∀ v ∈ paperSlitCharacterDomain α 0,
      weakJacobi (surfacePotential 3) u.1 v.1 + weakJacobi (surfacePotential 3) u.2 v.2 = 0) :
    u = 0 := by
  obtain ⟨a, rfl⟩ := hspan
  have ha := verticalThree_paper_weak_scalar_zero h0 h1 hker
  simp [ha]

end KsIndex.Trace
