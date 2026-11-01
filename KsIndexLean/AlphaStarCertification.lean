module

public import KsIndexLean.Staircase

@[expose] public section


/-! Certificate interfaces for enclosing the spectral threshold, and exact
arithmetic underlying the numerical remark's nonresonance cutoff. -/
noncomputable section
namespace KsIndex.Staircase
open CircleQ Real

/-- A normalized admissible trial function gives a negative-side certificate. -/
lemma gam_neg_of_trial {s : ℝ} {u : ℤ → ℂ}
    (hu : MemDom u) (hn : normSq u = 1) (hq : Qform s u < 0) : gam s < 0 :=
  lt_of_le_of_lt (gam_le hu hn) hq

/-- Strict positivity on the full normalized domain gives a positive-side
certificate, using the proved attainment of the least eigenvalue. -/
lemma gam_pos_of_positive_form {s : ℝ} (hs : 0 < s)
    (hq : ∀ u : ℤ → ℂ, MemDom u → normSq u = 1 → 0 < Qform s u) :
    0 < gam s := by
  obtain ⟨u, hu, hn, he⟩ := exists_minimizer hs
  rw [← he]
  exact hq u hu hn

/-- A negative least eigenvalue locates the parameter below the unique crossing. -/
lemma lt_sstar_of_gam_neg {s : ℝ} (hs : 0 < s) (hn : gam s < 0) : s < sstar := by
  by_contra hnlt
  have hle := Threshold.gam_strictMonoOn.monotoneOn sstar_pos hs (not_lt.mp hnlt)
  rw [sstar_spec.2.1] at hle
  linarith

/-- A positive least eigenvalue locates the parameter above the unique crossing. -/
lemma sstar_lt_of_gam_pos {s : ℝ} (hs : 0 < s) (hp : 0 < gam s) : sstar < s := by
  by_contra hnlt
  have hle := Threshold.gam_strictMonoOn.monotoneOn hs sstar_pos (not_lt.mp hnlt)
  rw [sstar_spec.2.1] at hle
  linarith

/-- Spectral sign certificates give a phase enclosure, with reversed endpoints. -/
theorem alphaStar_enclosure_of_signs {sL sU : ℝ}
    (hL : 0 < sL) (hU : 0 < sU) (hn : gam sL < 0) (hp : 0 < gam sU) :
    2 / π * arctan (1 / sU) < alphaStar ∧
    alphaStar < 2 / π * arctan (1 / sL) := by
  have hls := lt_sstar_of_gam_neg hL hn
  have hsu := sstar_lt_of_gam_pos hU hp
  constructor
  · exact mul_lt_mul_of_pos_left
      (arctan_strictMono ((one_div_lt_one_div hU sstar_pos).mpr hsu)) (by positivity)
  · exact mul_lt_mul_of_pos_left
      (arctan_strictMono ((one_div_lt_one_div sstar_pos hL).mpr hls)) (by positivity)

/-- The decimal interval lies strictly between Farey neighbors whose
 denominators sum to 2299. This does not assert that alphaStar is in the interval. -/
lemma numerical_interval_farey {a : ℝ}
    (hl : 4323617 / 10000000 ≤ a) (hu : a ≤ 4323619 / 10000000) :
    163 / 377 < a ∧ a < 831 / 1922 := by
  constructor <;> linarith

/-- Arithmetic content of the introductory numerical remark:
 every positive period through 2298 is nonresonant for a phase in the stated interval. -/
theorem numerical_interval_nonresonant {a : ℝ}
    (hl : 4323617 / 10000000 ≤ a) (hu : a ≤ 4323619 / 10000000)
    {m : ℕ} (hm : 0 < m) (hmax : m ≤ 2298) :
    ¬ ∃ z : ℤ, (m : ℝ) * a = (z : ℝ) := by
  obtain ⟨hlo, hhi⟩ := numerical_interval_farey hl hu
  rintro ⟨z, hz⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (163 : ℝ) * m < 377 * z := by nlinarith
  have h2 : (1922 : ℝ) * z < 831 * m := by nlinarith
  have hi1 : (163 : ℤ) * m < 377 * z := by exact_mod_cast h1
  have hi2 : (1922 : ℤ) * z < 831 * m := by exact_mod_cast h2
  omega

/-- At denominator 2299 the interval does contain a rational. -/
lemma numerical_interval_first_rational :
    (4323617 / 10000000 : ℝ) < 994 / 2299 ∧
    (994 / 2299 : ℝ) < 4323619 / 10000000 := by
  constructor <;> norm_num

end KsIndex.Staircase
