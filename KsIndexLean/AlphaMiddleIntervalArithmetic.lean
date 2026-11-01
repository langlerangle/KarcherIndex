module

public import KsIndexLean.AlphaSignedWindowBudget

@[expose] public section


/-! Signed interval glue for the middle-window certificate.
These lemmas do not assert any residual identity or numerical row enclosure. -/
namespace KsIndex.AlphaRemarkTrial.MiddleInterval

/-- Signed multiplication by one exact rational coefficient. -/
def scaleLo (c lo hi : ℚ) : ℚ := if 0 ≤ c then c*lo else c*hi
def scaleHi (c lo hi : ℚ) : ℚ := if 0 ≤ c then c*hi else c*lo

theorem scale_sound (c lo hi : ℚ) (x : ℝ)
    (hx : (lo:ℝ) ≤ x ∧ x ≤ (hi:ℝ)) :
    (scaleLo c lo hi:ℝ) ≤ (c:ℝ)*x ∧
      (c:ℝ)*x ≤ (scaleHi c lo hi:ℝ) := by
  by_cases hc : 0 ≤ c
  · have hcR : (0:ℝ) ≤ c := by exact_mod_cast hc
    simpa [scaleLo, scaleHi, hc] using
      And.intro (mul_le_mul_of_nonneg_left hx.1 hcR)
        (mul_le_mul_of_nonneg_left hx.2 hcR)
  · have hcR : (c:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hc))
    simpa [scaleLo, scaleHi, hc] using
      And.intro (mul_le_mul_of_nonpos_left hx.2 hcR)
        (mul_le_mul_of_nonpos_left hx.1 hcR)

/-- Product enclosure when the first interval is nonnegative; the second may
cross zero. This retains the sign until after interval addition. -/
def productLo (a b c : ℚ) : ℚ := min (a*c) (b*c)
def productHi (a b d : ℚ) : ℚ := max (a*d) (b*d)

theorem product_sound (a b c d : ℚ) (x y : ℝ)
    (ha : 0 ≤ a) (hx : (a:ℝ) ≤ x ∧ x ≤ (b:ℝ))
    (hy : (c:ℝ) ≤ y ∧ y ≤ (d:ℝ)) :
    (productLo a b c:ℝ) ≤ x*y ∧ x*y ≤ (productHi a b d:ℝ) := by
  have haR : (0:ℝ) ≤ a := by exact_mod_cast ha
  have hx0 : 0 ≤ x := haR.trans hx.1
  have hl : min ((a:ℝ)*c) ((b:ℝ)*c) ≤ x*(c:ℝ) := by
    by_cases hc : (0:ℝ) ≤ c
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hc)
    · exact (min_le_right _ _).trans
        (mul_le_mul_of_nonpos_right hx.2 (le_of_lt (lt_of_not_ge hc)))
  have hu : x*(d:ℝ) ≤ max ((a:ℝ)*d) ((b:ℝ)*d) := by
    by_cases hd : (0:ℝ) ≤ d
    · exact (mul_le_mul_of_nonneg_right hx.2 hd).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hx.1 (le_of_lt (lt_of_not_ge hd))).trans
        (le_max_left _ _)
  constructor
  · simpa [productLo] using hl.trans (mul_le_mul_of_nonneg_left hy.1 hx0)
  · simpa [productHi] using (mul_le_mul_of_nonneg_left hy.2 hx0).trans hu

/-- Add signed row components before taking an absolute-value bound. -/
theorem sum_sound {ι : Type*} (s : Finset ι) (lo hi : ι → ℚ) (x : ι → ℝ)
    (hx : ∀ i ∈ s, (lo i:ℝ) ≤ x i ∧ x i ≤ (hi i:ℝ)) :
    ((∑ i ∈ s, lo i):ℝ) ≤ ∑ i ∈ s, x i ∧
      (∑ i ∈ s, x i) ≤ ((∑ i ∈ s, hi i):ℝ) := by
  constructor
  · simpa using Finset.sum_le_sum (fun i hi => (hx i hi).1)
  · simpa using Finset.sum_le_sum (fun i hi => (hx i hi).2)

end KsIndex.AlphaRemarkTrial.MiddleInterval

#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.scale_sound
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.product_sound
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.sum_sound
