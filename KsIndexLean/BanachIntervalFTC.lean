module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

/-- Absolute continuity transfers along a bound on every interval increment. -/
lemma absolutelyContinuous_of_dist_le {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {f : ℝ → X} {g : ℝ → Y} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hg ε hε
  refine ⟨δ, hδ, fun s hs hlen => lt_of_le_of_lt ?_ (hd s hs hlen)⟩
  exact Finset.sum_le_sum fun i hi => h _ (hs.1 i hi).1 _ (hs.1 i hi).2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A Bochner primitive is absolutely continuous, also for infinite-dimensional targets. -/
theorem banach_primitive_absolutelyContinuous {g : ℝ → E} {a b c : ℝ}
    (hg : IntervalIntegrable g volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, g t) a b := by
  apply absolutelyContinuous_of_dist_le
    (hg.norm.absolutelyContinuousOnInterval_intervalIntegral hc)
  intro x hx y hy
  have hcx : IntervalIntegrable g volume c x := hg.mono_set' (by grind [uIoc, uIcc])
  have hcy : IntervalIntegrable g volume c y := hg.mono_set' (by grind [uIoc, uIcc])
  rw [dist_eq_norm, Real.dist_eq,
    intervalIntegral.integral_interval_sub_left hcx hcy,
    intervalIntegral.integral_interval_sub_left hcx.norm hcy.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- FTC with a prescribed integrable a.e. derivative, in any real Banach space. -/
theorem banach_integral_eq_sub_of_ae_hasDerivAt {f g : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : IntervalIntegrable g volume a b)
    (hd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    (∫ x in a..b, g x) = f b - f a := by
  have hp := banach_primitive_absolutelyContinuous hg (left_mem_uIcc : a ∈ uIcc a b)
  have hz : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt (fun t => f t - ∫ s in a..t, g s) 0 x := by
    filter_upwards [hd, hg.ae_hasDerivAt_integral] with x hx hp hxI
    convert (hx hxI).sub (hp hxI a left_mem_uIcc) using 1 <;> first | rfl | simp
  obtain ⟨C, hC⟩ := (hf.sub hp).const_of_ae_hasDerivAt_zero hz
  have ha := hC a left_mem_uIcc
  have hb := hC b right_mem_uIcc
  simp only [Pi.sub_apply, intervalIntegral.integral_same, sub_zero] at ha hb
  rw [← ha] at hb
  rw [← hb]
  abel

end KsIndex.Trace
