module

public import KsIndexLean.CircleSupportedRepresentative
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section


/-! Closure of the allowed boundary arc family. -/
noncomputable section
open Set
namespace KsIndex.Trace

lemma boundaryArc_one_preimage_pow (k : ℕ) :
    boundaryArc k 1 = (fun w : Circle₁ => w ^ k) ⁻¹' boundaryArc 1 1 := by
  ext w
  simp only [mem_boundaryArc, mem_preimage, pow_one, neg_one_mul]
  rfl

/-- The nonzero circle power covering reduces arc closure to the right semicircle. -/
theorem closure_boundaryArc_one_preimage (k : ℕ) (hk : 0 < k) :
    closure (boundaryArc k 1) =
      (fun w : Circle₁ => w ^ k) ⁻¹' closure (boundaryArc 1 1) := by
  let : NeZero k := ⟨hk.ne'⟩
  have ho : IsOpenMap (fun w : Circle₁ => w ^ k) :=
    (Circle.isQuotientCoveringMap_npow k).isCoveringMap.isOpenMap
  rw [boundaryArc_one_preimage_pow]
  exact (ho.preimage_closure_eq_closure_preimage (by fun_prop) _).symm

/-- The closed right semicircle includes precisely the two endpoints of its open arc. -/
theorem closure_boundaryArc_one :
    closure (boundaryArc 1 1) = (boundaryArc 1 0)ᶜ := by
  apply subset_antisymm
  · apply closure_minimal _ (KsIndex.CircleSobolev.isClosed_boundaryArc_zero_compl 1)
    intro w hw
    simp only [mem_boundaryArc, pow_one, neg_one_mul] at hw
    rw [KsIndex.CircleSobolev.boundaryArc_zero_compl]
    simpa only [mem_ofPred_eq, pow_one] using (le_of_lt (neg_neg_iff_pos.mp hw))
  · intro w hw
    rw [KsIndex.CircleSobolev.boundaryArc_zero_compl] at hw
    have ha : |Complex.arg (w : ℂ)| ≤ Real.pi / 2 :=
      Complex.abs_arg_le_pi_div_two_iff.mpr (by simpa using hw)
    have hm : Complex.arg (w : ℂ) ∈ closure (Ioo (-Real.pi / 2) (Real.pi / 2)) := by
      rw [closure_Ioo (ne_of_lt (by linarith [Real.pi_pos] : -Real.pi / 2 < Real.pi / 2))]
      simpa only [mem_Icc, neg_div] using abs_le.mp ha
    have he := mem_closure_image Circle.exp.continuous.continuousAt hm
    rw [show Circle.exp (Complex.arg (w : ℂ)) = w from Circle.exp_arg w] at he
    apply closure_mono _ he
    rintro z ⟨t, ht, rfl⟩
    apply (mem_boundaryArc 1 1 (Circle.exp t)).mpr
    simp only [pow_one, neg_one_mul]
    rw [Circle.coe_exp, Complex.exp_mul_I]
    simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using (neg_neg_of_pos (Real.cos_pos_of_mem_Ioo (by simpa only [neg_div] using ht)))

/-- Exact equivalence of the paper's complementary-arc descriptions. -/
theorem closure_boundaryArc_one_eq_compl (k : ℕ) (hk : 0 < k) :
    closure (boundaryArc k 1) = (boundaryArc k 0)ᶜ := by
  rw [closure_boundaryArc_one_preimage k hk, closure_boundaryArc_one]
  ext w
  simp only [mem_preimage, mem_compl_iff, mem_boundaryArc, pow_zero, one_mul, pow_one]
  rfl

end KsIndex.Trace

namespace KsIndex.CircleSobolev
open KsIndex.Trace MeasureTheory

/-- The paper's supported representative and L² arc-vanishing definitions agree. -/
theorem mem_dnSpace_iff_supported (k : ℕ) (hk : 0 < k) (v : Space (1 / 2 : ℝ)) :
    v ∈ dnSpace k ↔ ∃ g : Circle₁ → ℂ,
      toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num) v =ᵐ[circleMeasure] g ∧
        tsupport g ⊆ closure (boundaryArc k 1) := by
  rw [closure_boundaryArc_one_eq_compl k hk]
  exact mem_dnSpace_iff_supported_compl k v

end KsIndex.CircleSobolev
