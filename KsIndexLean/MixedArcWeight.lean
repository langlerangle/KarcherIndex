module

public import KsIndexLean.WeightedNormalTest
public import KsIndexLean.MixedNeumannStrictBracketing
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- Positive on the indicated free arc, zero on the opposite arc. -/
def mixedArcWeight (k : ℕ) (freeOne : Bool) (z : ℂ) : ℝ :=
  expNegInvGlue (if freeOne then (z ^ k).re else -(z ^ k).re)

lemma mixedArcWeight_smooth (k : ℕ) (b : Bool) : ContDiff ℝ ∞ (mixedArcWeight k b) := by
  cases b
  · exact expNegInvGlue.contDiff.comp ((Complex.reCLM.contDiff.comp (contDiff_id.pow k)).neg)
  · exact expNegInvGlue.contDiff.comp (Complex.reCLM.contDiff.comp (contDiff_id.pow k))

lemma mixedArcWeight_nonneg (k : ℕ) (b : Bool) (z : ℂ) : 0 ≤ mixedArcWeight k b z :=
  expNegInvGlue.nonneg _

lemma mixedArcWeight_pos (k : ℕ) (b : Bool) (w : Circle₁)
    (hw : w ∈ boundaryArc k (if b then 1 else 0)) : 0 < mixedArcWeight k b w := by
  apply expNegInvGlue.pos_of_pos
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hw ⊢
  · have h := (mem_boundaryArc k 0 w).mp hw
    simp only [pow_zero, one_mul] at h
    exact neg_pos.mpr h
  · have h := (mem_boundaryArc k 1 w).mp hw
    simp only [pow_one, neg_one_mul] at h
    exact neg_neg_iff_pos.mp h

lemma mixedArcWeight_zero (k : ℕ) (b : Bool) (w : Circle₁)
    (hw : w ∈ boundaryArc k (if b then 0 else 1)) : mixedArcWeight k b w = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hw ⊢
  · have h := (mem_boundaryArc k 1 w).mp hw
    simpa only [pow_one, neg_one_mul] using h.le
  · have h := (mem_boundaryArc k 0 w).mp hw
    simpa only [pow_zero, one_mul] using h.le

lemma mixedArcWeight_test_mem (k : ℕ) (b : Bool) (G : ℂ → ℂ) (hG : ContDiff ℝ ∞ G) :
    globalSmoothH1 (fun z => (mixedArcWeight k b z : ℂ) * G z)
      ((Complex.ofRealCLM.contDiff.comp (mixedArcWeight_smooth k b)).mul hG) ∈
      mixedTraceDomain k b (!b) := by
  have hz : globalSmoothH1 (fun z => (mixedArcWeight k b z : ℂ) * G z)
      ((Complex.ofRealCLM.contDiff.comp (mixedArcWeight_smooth k b)).mul hG) ∈
      zeroTraceDomain (boundaryArc k (if b then 0 else 1)) := by
    rw [mem_zeroTraceDomain]
    have ht := (globalSmoothH1_trace (fun z => (mixedArcWeight k b z : ℂ) * G z)
      ((Complex.ofRealCLM.contDiff.comp (mixedArcWeight_smooth k b)).mul hG)).filter_mono
      (ae_mono (Measure.restrict_le_self (s := boundaryArc k (if b then 0 else 1))))
    filter_upwards [ht, ae_restrict_mem (measurableSet_boundaryArc k (if b then 0 else 1))] with w hw ha
    rw [hw, mixedArcWeight_zero k b w ha, Complex.ofReal_zero, zero_mul]
    rfl
  cases b <;> simpa only [mixedTraceDomain, naturalArcDomain, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true, inf_top_eq, top_inf_eq] using hz

end KsIndex.Trace
