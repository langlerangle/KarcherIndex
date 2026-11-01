module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section


/-! Rational polynomial bounds for arctangent on the nonnegative real axis. -/
noncomputable section
namespace KsIndex.ArctanBounds
open Real

def lower (x : ℝ) : ℝ := x - x^3/3 + x^5/5 - x^7/7
def upper (x : ℝ) : ℝ := lower x + x^9/9

lemma hasDerivAt_lower (x : ℝ) : HasDerivAt lower (1-x^2+x^4-x^6) x := by
  unfold lower
  convert! (((hasDerivAt_id x).sub ((hasDerivAt_id x).pow 3 |>.div_const 3)).add
    ((hasDerivAt_id x).pow 5 |>.div_const 5)).sub
    ((hasDerivAt_id x).pow 7 |>.div_const 7) using 1
  simp

lemma hasDerivAt_upper (x : ℝ) : HasDerivAt upper (1-x^2+x^4-x^6+x^8) x := by
  unfold upper
  convert! (hasDerivAt_lower x).add ((hasDerivAt_id x).pow 9 |>.div_const 9) using 1
  simp

lemma lower_le_arctan {x : ℝ} (hx : 0 ≤ x) : lower x ≤ arctan x := by
  have hd (t : ℝ) : HasDerivAt (fun y => arctan y - lower y) (t^8/(1+t^2)) t := by
    convert! (hasDerivAt_arctan t).sub (hasDerivAt_lower t) using 1
    have hn : 1+t^2 ≠ 0 := by positivity
    field_simp
    ring
  have hm := monotone_of_hasDerivAt_nonneg hd (fun t => by positivity)
  have he := hm hx
  simpa [lower, arctan_zero] using he

lemma arctan_le_upper {x : ℝ} (hx : 0 ≤ x) : arctan x ≤ upper x := by
  have hd (t : ℝ) : HasDerivAt (fun y => upper y - arctan y) (t^10/(1+t^2)) t := by
    convert! (hasDerivAt_upper t).sub (hasDerivAt_arctan t) using 1
    have hn : 1+t^2 ≠ 0 := by positivity
    field_simp
    ring
  have hm := monotone_of_hasDerivAt_nonneg hd (fun t => by positivity)
  have he := hm hx
  simpa [upper, lower, arctan_zero] using he

lemma arctan_inv_reduction {s : ℝ} (hs : 1 ≤ s) :
    arctan (1/s) = π/4 - arctan ((s-1)/(s+1)) := by
  have hp : 0 < s := by linarith
  have hq : 0 < s+1 := by linarith
  have ht : (s-1)/(s+1) < 1 := (div_lt_iff₀ hq).mpr (by linarith)
  have hm : (1/s)*((s-1)/(s+1)) < 1 := by
    have hh := mul_lt_mul_of_pos_left ht (one_div_pos.mpr hp)
    rw [mul_one] at hh
    exact hh.trans_le ((div_le_iff₀ hp).mpr (by simpa using hs))
  have ha := arctan_add hm
  have he : (1/s + (s-1)/(s+1))/(1-(1/s)*((s-1)/(s+1))) = 1 := by
    apply (div_eq_one_iff_eq (ne_of_gt (sub_pos.mpr hm))).mpr
    field_simp
    ring
  rw [he, arctan_one] at ha
  linarith

end KsIndex.ArctanBounds
