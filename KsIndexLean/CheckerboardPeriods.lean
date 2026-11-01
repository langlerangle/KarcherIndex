module

public import KsIndexLean.KarcherPlaneSectors

@[expose] public section


/-! Algebraic obstructions to horizontal periods in alternating closed wedges. -/
noncomputable section
namespace KsIndex
open Complex Set

abbrev SpacePoint := ℂ × ℝ

/-- A two-sided translation period of a subset of real three-space. -/
def TranslationPeriod (S : Set SpacePoint) (v : SpacePoint) : Prop :=
  ∀ p, p + v ∈ S ↔ p ∈ S

namespace TranslationPeriod
variable {S : Set SpacePoint} {u v : SpacePoint}
lemma add (hu : TranslationPeriod S u) (hv : TranslationPeriod S v) :
    TranslationPeriod S (u + v) := by
  intro p
  rw [← add_assoc, hv, hu]
lemma neg (hv : TranslationPeriod S v) : TranslationPeriod S (-v) := by
  intro p
  simpa using (hv (p + -v)).symm
lemma sub (hu : TranslationPeriod S u) (hv : TranslationPeriod S v) :
    TranslationPeriod S (u - v) := by simpa [sub_eq_add_neg] using hu.add hv.neg
lemma transport {f : SpacePoint → SpacePoint} {w : SpacePoint}
    (hf : Function.Surjective f) (hS : ∀ p, f p ∈ S ↔ p ∈ S)
    (hv : TranslationPeriod S v) (he : ∀ p, f (p + v) = f p + w) :
    TranslationPeriod S w := by
  intro p
  obtain ⟨q, rfl⟩ := hf p
  rw [← he, hS, hS, hv]
lemma of_intertwining {f g j : SpacePoint → SpacePoint} {v : SpacePoint}
    (hf : Function.Surjective f) (hj : Function.Surjective j)
    (hSf : ∀ p, f p ∈ S ↔ p ∈ S) (hSg : ∀ p, g p ∈ S ↔ p ∈ S)
    (hSj : ∀ p, j p ∈ S ↔ p ∈ S)
    (he : ∀ p, f (g p) = j (f p) + v) : TranslationPeriod S v := by
  intro p
  obtain ⟨q, rfl⟩ := hj p
  obtain ⟨r, rfl⟩ := hf q
  rw [← he, hSf, hSg, hSj, hSf]

end TranslationPeriod

/-- A polar point in an allowed wedge has nonpositive real kth power. -/
lemma checkerboard_power_nonpos {k : ℕ} {r θ : ℝ} {j : ℤ} (hr : 0 ≤ r)
    (hθ : (k : ℝ) * θ / Real.pi ∈ Icc (1 / 2 + 2 * (j : ℝ))
      (3 / 2 + 2 * (j : ℝ))) :
    (((r : ℂ) * Complex.exp ((θ : ℂ) * I)) ^ k).re ≤ 0 := by
  have he : (Complex.exp ((θ : ℂ) * I)) ^ k =
      Complex.exp ((((k : ℝ) * θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, ← Complex.ofReal_pow, he, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re]
  apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hr k)
  have hl := (le_div_iff₀ Real.pi_pos).mp hθ.1
  have hu := (div_le_iff₀ Real.pi_pos).mp hθ.2
  have hc : Real.cos ((k : ℝ) * θ - (j : ℝ) * (2 * Real.pi)) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith) (by nlinarith)
  have hh := Real.cos_add_int_mul_two_pi ((k : ℝ) * θ - (j : ℝ) * (2 * Real.pi)) j
  simpa using (show Real.cos ((k : ℝ) * θ) ≤ 0 from by
    convert hc using 1
    rw [← hh]
    congr 1
    ring)

lemma halfStep_pow {k : ℕ} (hk : 0 < k) :
    (Complex.exp (((Real.pi / k : ℝ) : ℂ) * I)) ^ k = -1 := by
  rw [← Complex.exp_nat_mul]
  have he : (k : ℂ) * (((Real.pi / k : ℝ) : ℂ) * I) = Real.pi * I := by
    have hn : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    push_cast
    field_simp
  rw [he, Complex.exp_pi_mul_I]

lemma one_add_halfStep_pow_im_pos {k : ℕ} (hk : 2 ≤ k) :
    0 < (((1 : ℂ) + Complex.exp (((Real.pi / k : ℝ) : ℂ) * I)) ^ k).im := by
  let δ : ℝ := Real.pi / (2 * k)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδhi : δ < Real.pi / 2 := by
    dsimp [δ]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  have hc : 0 < 2 * Real.cos δ := by
    have := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδhi⟩
    positivity
  have he : (1 : ℂ) + Complex.exp (((Real.pi / k : ℝ) : ℂ) * I) =
      (2 * Real.cos δ : ℝ) * Complex.exp ((δ : ℂ) * I) := by
    have hangle : Real.pi / (k : ℝ) = 2 * δ := by dsimp [δ]; ring
    apply Complex.ext
    · simp only [Complex.add_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
        Complex.re_ofReal_mul, hangle, Real.cos_two_mul]
      ring
    · simp only [Complex.add_im, Complex.one_im, Complex.exp_ofReal_mul_I_im,
        Complex.im_ofReal_mul, hangle, Real.sin_two_mul, zero_add]
      ring
  rw [he, mul_pow, ← Complex.ofReal_pow, Complex.im_ofReal_mul, ← Complex.exp_nat_mul]
  have harg : (k : ℂ) * ((δ : ℂ) * I) = ((Real.pi / 2 : ℝ) : ℂ) * I := by
    dsimp [δ]
    have hn : (k : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
    push_cast
    field_simp
  rw [harg, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_two, mul_one]
  exact pow_pos hc k

/-- A subgroup of horizontal periods contained in the alternating wedges
and closed under the half-step rotation is trivial. -/
theorem horizontal_period_obstruction {k : ℕ} (hk : 2 ≤ k)
    (P : AddSubgroup ℂ)
    (hcone : ∀ v ∈ P, (v ^ k).re ≤ 0)
    (hrot : ∀ v ∈ P, Complex.exp (((Real.pi / k : ℝ) : ℂ) * I) * v ∈ P) :
    ∀ v ∈ P, v = 0 := by
  let c : ℂ := Complex.exp (((Real.pi / k : ℝ) : ℂ) * I)
  have hc : c ^ k = -1 := halfStep_pow (by omega)
  have hzero : ∀ v ∈ P, (v ^ k).re = 0 := by
    intro v hv
    have h1 := hcone v hv
    have h2 := hcone (c * v) (hrot v hv)
    rw [mul_pow, hc, neg_one_mul, Complex.neg_re] at h2
    linarith
  intro v hv
  have hvre := hzero v hv
  have hsum := hzero (v + c * v) (P.add_mem hv (hrot v hv))
  have he : v + c * v = (1 + c) * v := by ring
  rw [he, mul_pow, Complex.mul_re, hvre, mul_zero, zero_sub] at hsum
  have him : (v ^ k).im = 0 := by
    have hp : 0 < ((1 + c) ^ k).im := one_add_halfStep_pow_im_pos hk
    nlinarith
  have hz : v ^ k = 0 := Complex.ext hvre him
  exact (pow_eq_zero_iff (by omega : k ≠ 0)).mp hz

end KsIndex
