module

public import KsIndexLean.CircleQPhysicalForm
public import KsIndexLean.CircleSobolevPaperNorm

@[expose] public section


/-! The paper's coercivity estimate with its Sobolev weights and arclength mass. -/
noncomputable section
namespace KsIndex.CircleQ
open CircleSobolev Statements

lemma physicalTrace_norm_sq (w : ℤ → ℂ) (hw : MemDom w) :
    ‖physicalTrace w hw‖ ^ 2 = (2 * Real.pi) * normSq w := by
  have h := congrArg Complex.re (physicalTrace_inner w w hw hw)
  rw [inner_self_eq_norm_sq_to_K, massPair_self] at h
  simpa [pow_two, Complex.mul_re] using h

lemma physicalForm_self_re (s : ℝ) (w : ℤ → ℂ) (hw : MemDom w) :
    (physicalForm s (physicalGraph w hw) (physicalGraph w hw)).re =
      (2 * Real.pi) * Qform s w := by
  rw [physicalForm_eq_Bform, Bform_self]
  simp

/-- The displayed coercivity inequality uses the paper's smaller half-order
weight and its unnormalized arclength L² mass. -/
theorem paper_physical_coercivity (s : ℝ) (f : Space (1 / 2 : ℝ))
    (hf : MemDomSigma f) (hp : f ∈ character (1 / 2 : ℝ) (-1) 6) :
    min 1 (s ^ 2) * paperGraphNormSq (domPair f hf) ≤
      (physicalForm s (domPair f hf) (domPair f hf)).re +
        5 * (1 + s ^ 2) * ‖toL2Half f‖ ^ 2 := by
  obtain ⟨w, hw, hrec⟩ := exists_physical_reconstruction f hf hp
  subst f
  change min 1 (s ^ 2) * paperGraphNormSq (physicalGraph w hw) ≤
    (physicalForm s (physicalGraph w hw) (physicalGraph w hw)).re +
      5 * (1 + s ^ 2) * ‖physicalTrace w hw‖ ^ 2
  rw [physicalForm_self_re, physicalTrace_norm_sq]
  have hc := physicalGraph_coercivity s w hw
  have hm : 0 ≤ min 1 (s ^ 2) := le_min (by norm_num) (sq_nonneg s)
  have hR : 0 ≤ Qform s w + 5 * (1 + s ^ 2) * normSq w :=
    (mul_nonneg hm (sq_nonneg ‖physicalGraph w hw‖)).trans hc
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc
    _ ≤ min 1 (s ^ 2) * ‖physicalGraph w hw‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (paperGraphNormSq_le _) hm
    _ ≤ Qform s w + 5 * (1 + s ^ 2) * normSq w := hc
    _ ≤ (2 * Real.pi) * (Qform s w + 5 * (1 + s ^ 2) * normSq w) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpi) hR]
    _ = _ := by ring

end KsIndex.CircleQ
