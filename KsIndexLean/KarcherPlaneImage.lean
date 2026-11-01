module

public import KsIndexLean.KarcherPlaneLineRange
public import KsIndexLean.KarcherPlaneHeights

@[expose] public section


/-! Exact intersections of the normalized EW image with the distinguished
vertical planes. The range assertion includes every point of every line. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex Set
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- Every nonnegative distance on a distinguished ray is attained at height π / 2. -/
lemma exists_midplane_ray {β L : ℝ} (hβ : Real.cos ((k : ℝ) * β) = 0) (hL : 0 ≤ L) :
    ∃ q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C,
      centeredLiftAmbient R.C R.t q = (L * Real.cos β, -L * Real.sin β, Real.pi / 2) := by
  obtain ⟨r, hr, hrL⟩ := bigL_surjective_nonneg h.out hL
  let w : PuncturedPlane k := ⟨(r : ℂ) * Complex.exp ((β : ℂ) * I), disk_not_puncture (by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact hr.2)⟩
  have hn : ‖w.val‖ = r := by
    simp [w, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hr.1]
  obtain ⟨q, hq⟩ := exists_halfPeriod_over_disk h.out (reflectionBasepoint k) w rfl R.C
    (by rw [hn]; exact hr.2.le)
  have hh := centeredLiftAmbient_midplane_horizontal R q.val hr.1 hr.2 hβ w rfl hq
  rw [hrL] at hh
  have hre : (w.val ^ k).re = 0 := by
    have he : w.val ^ k = (r ^ k : ℂ) * Complex.exp ((((k : ℝ) * β : ℝ) : ℂ) * I) := by
      dsimp [w]
      rw [mul_pow, ← Complex.exp_nat_mul]
      congr 2
      push_cast
      ring
    rw [he, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, hβ]
    ring
  have hz := (midplane_iff h.out (reflectionBasepoint k) w rfl R.C q.val hq q.property).mpr
    ⟨hre, by rw [hn]; exact hr.2⟩
  exact ⟨q.val, Prod.ext hh.1 (Prod.ext hh.2 hz)⟩

lemma exists_midplane_line {θ s : ℝ} (hθ : Real.cos ((k : ℝ) * θ) = 0) :
    ∃ q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C,
      centeredLiftAmbient R.C R.t q = (s * Real.cos θ, s * Real.sin θ, Real.pi / 2) := by
  by_cases hs : 0 ≤ s
  · simpa [Real.cos_neg, Real.sin_neg] using R.exists_midplane_ray (β := -θ) (by simpa using hθ) hs
  · have hβ : Real.cos ((k : ℝ) * (-θ + Real.pi)) = 0 := by
      rw [mul_add, Real.cos_add, Real.sin_nat_mul_pi, mul_neg, Real.cos_neg]
      simp [hθ]
    obtain ⟨q, hq⟩ := R.exists_midplane_ray (β := -θ + Real.pi) (L := -s) hβ (by linarith)
    refine ⟨q, ?_⟩
    simpa [Real.cos_add_pi, Real.sin_add_pi, Real.cos_neg, Real.sin_neg] using hq

/-- Deck translations and reflection in a horizontal plane realize every line
at every half-integer height, without moving its horizontal coordinates. -/
theorem exists_plane_line_point {θ s : ℝ} (hθ : Real.cos ((k : ℝ) * θ) = 0) (n : ℤ) :
    ∃ q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C,
      centeredLiftAmbient R.C R.t q =
        (s * Real.cos θ, s * Real.sin θ, ((n : ℝ) + 1 / 2) * Real.pi) := by
  obtain ⟨q, hq⟩ := R.exists_midplane_line (s := s) hθ
  have hx := congrArg Prod.fst hq
  have hy := congrArg (fun p : AmbientTriple => p.2.1) hq
  have hz := congrArg (fun p : AmbientTriple => p.2.2) hq
  change HeightLift.height q + Real.pi = Real.pi / 2 at hz
  rcases Int.emod_two_eq_zero_or_one n with hn | hn
  · refine ⟨HeightLift.deck (n / 2) q, Prod.ext hx (Prod.ext hy ?_)⟩
    change HeightLift.height (HeightLift.deck (n / 2) q) + Real.pi = _
    rw [HeightLift.height_deck]
    have he : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) := by
      exact_mod_cast (show n = 2 * (n / 2) by omega)
    rw [he]
    linarith
  · let q' := lowerSeamLift R.C R.hC q
    have hq' := centeredLiftAmbient_lowerSeam R.C R.hC R.t q
    rw [hq] at hq'
    have hx' : (centeredLiftAmbient R.C R.t q').1 = s * Real.cos θ := congrArg Prod.fst hq'
    have hy' : (centeredLiftAmbient R.C R.t q').2.1 = s * Real.sin θ :=
      congrArg (fun p : AmbientTriple => p.2.1) hq'
    refine ⟨HeightLift.deck (n / 2 + 1) q', Prod.ext hx' (Prod.ext hy' ?_)⟩
    change HeightLift.height (HeightLift.deck (n / 2 + 1) q') + Real.pi = _
    rw [HeightLift.height_deck]
    have hh := lowerSeamLift_height R.C R.hC q
    change HeightLift.height q' + Real.pi = _ at hh
    have he : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) + 1 := by
      exact_mod_cast (show n = 2 * (n / 2) + 1 by omega)
    rw [he]
    push_cast
    linarith

/-- The full plane intersection assertion: plane membership cuts the actual
EW image into precisely the horizontal lines at half-integer heights. -/
theorem vertical_plane_image {θ : ℝ} (hθ : Real.cos ((k : ℝ) * θ) = 0) :
    Set.range (centeredLiftAmbient (k := k) R.C R.t) ∩
        {p : AmbientTriple | p.2.1 * Real.cos θ = p.1 * Real.sin θ} =
      {p : AmbientTriple | p.2.1 * Real.cos θ = p.1 * Real.sin θ ∧
        ∃ n : ℤ, p.2.2 = ((n : ℝ) + 1 / 2) * Real.pi} := by
  ext p
  constructor
  · rintro ⟨⟨q, rfl⟩, hp⟩
    change (centeredLiftAmbient R.C R.t q).2.1 * Real.cos θ =
      (centeredLiftAmbient R.C R.t q).1 * Real.sin θ at hp
    refine ⟨hp, ?_⟩
    let a : ℂ := Complex.exp (((-θ : ℝ) : ℂ) * I)
    have ha : ‖a‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hak : a ^ (2 * k) = -1 := by
      dsimp [a]
      rw [← Complex.exp_nat_mul]
      have he : (↑(2 * k) : ℂ) * (((-θ : ℝ) : ℂ) * I) =
          (((2 * (k : ℝ) * (-θ)) : ℝ) : ℂ) * I := by push_cast; ring
      rw [he]
      exact exp_two_mul_k_beta k (β := -θ) (by simpa using hθ)
    apply R.plane_height_half_integer q ha hak
    dsimp [a]
    rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
    nlinarith
  · rintro ⟨hp, n, hn⟩
    let s := p.1 * Real.cos θ + p.2.1 * Real.sin θ
    have hx : s * Real.cos θ = p.1 := by
      dsimp [s]
      linear_combination Real.sin θ * hp + p.1 * (Real.sin_sq_add_cos_sq θ)
    have hy : s * Real.sin θ = p.2.1 := by
      dsimp [s]
      linear_combination -Real.cos θ * hp + p.2.1 * (Real.sin_sq_add_cos_sq θ)
    obtain ⟨q, hq⟩ := R.exists_plane_line_point (s := s) hθ n
    refine ⟨⟨q, ?_⟩, hp⟩
    rw [hq, hx, hy, ← hn]

/-- The plane intersection formula with the paper's half-integer plane index. -/
theorem vertical_plane_image_half_integer (j : ℤ) :
    let θ := ((j : ℝ) + 1 / 2) * Real.pi / (k : ℝ)
    Set.range (centeredLiftAmbient (k := k) R.C R.t) ∩
        {p : AmbientTriple | p.2.1 * Real.cos θ = p.1 * Real.sin θ} =
      {p : AmbientTriple | p.2.1 * Real.cos θ = p.1 * Real.sin θ ∧
        ∃ n : ℤ, p.2.2 = ((n : ℝ) + 1 / 2) * Real.pi} := by
  dsimp only
  apply R.vertical_plane_image
  have hk : (k : ℝ) ≠ 0 := by
    exact_mod_cast (show k ≠ 0 from by have := h.out; omega)
  have he : (k : ℝ) * (((j : ℝ) + 1 / 2) * Real.pi / (k : ℝ)) =
      Real.pi / 2 + (j : ℝ) * Real.pi := by
    field_simp
    ring
  rw [he, Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
