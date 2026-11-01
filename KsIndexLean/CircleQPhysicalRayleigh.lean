module

public import KsIndexLean.CircleQPhysicalEigenvalue
public import KsIndexLean.CircleQPaperCoercivity

@[expose] public section


/-! For positive parameters, the threshold is the attained physical Rayleigh infimum. -/
noncomputable section
namespace KsIndex.CircleQ
open CircleSobolev Statements

/-- Rayleigh quotients on the actual nonzero positive physical graph domain. -/
def physicalRayleighValues (s : ℝ) : Set ℝ :=
  {r | ∃ (f : Space (1 / 2 : ℝ)) (hf : MemDomSigma f),
    f ∈ character (1 / 2 : ℝ) (-1) 6 ∧ f ≠ 0 ∧
      r = (physicalForm s (domPair f hf) (domPair f hf)).re / ‖toL2Half f‖ ^ 2}

lemma physical_mass_pos {f : Space (1 / 2 : ℝ)} (hf : f ≠ 0) :
    0 < ‖toL2Half f‖ ^ 2 := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  apply hf
  apply toL2_injective (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa using hz

/-- Every physical Rayleigh quotient is at least gamma. -/
theorem gam_le_physicalRayleigh {s r : ℝ} (hr : r ∈ physicalRayleighValues s) :
    gam s ≤ r := by
  obtain ⟨f, hf, hp, hne, rfl⟩ := hr
  apply (le_div_iff₀ (physical_mass_pos hne)).mpr
  obtain ⟨w, hw, hrec⟩ := exists_physical_reconstruction f hf hp
  subst f
  change gam s * ‖physicalTrace w hw‖ ^ 2 ≤
    (physicalForm s (physicalGraph w hw) (physicalGraph w hw)).re
  rw [physicalTrace_norm_sq, physicalForm_self_re]
  have h := mul_le_mul_of_nonneg_left (gam_mul_normSq_le (s := s) hw)
    (show 0 ≤ 2 * Real.pi by positivity)
  nlinarith

/-- A physical eigenvector at gamma attains the physical Rayleigh quotient. -/
theorem gam_mem_physicalRayleigh {s : ℝ} (hs : 0 < s) :
    gam s ∈ physicalRayleighValues s := by
  obtain ⟨f, hf, hp, hne, he⟩ := gam_isPhysicalEigenvalue hs
  refine ⟨f, hf, hp, hne, ?_⟩
  have h := congrArg Complex.re (he f hf hp)
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  have hdiag : (physicalForm s (domPair f hf) (domPair f hf)).re =
      gam s * ‖toL2Half f‖ ^ 2 := by
    simpa [pow_two, Complex.mul_re] using h
  rw [hdiag, mul_div_cancel_right₀ _ (ne_of_gt (physical_mass_pos hne))]

/-- For positive parameters, the physical Rayleigh infimum is attained. -/
theorem gam_isLeast_physicalRayleigh {s : ℝ} (hs : 0 < s) :
    IsLeast (physicalRayleighValues s) (gam s) :=
  ⟨gam_mem_physicalRayleigh hs, fun _ hr => gam_le_physicalRayleigh hr⟩

/-- Literal agreement with the paper's unnormalized quotient definition. -/
theorem gam_eq_physicalRayleigh_inf {s : ℝ} (hs : 0 < s) :
    gam s = sInf (physicalRayleighValues s) :=
  (gam_isLeast_physicalRayleigh hs).csInf_eq.symm

end KsIndex.CircleQ
