module

public import KsIndexLean.KarcherImageAxis
public import KsIndexLean.KarcherPlaneImage

@[expose] public section


/-! Horizontal rotations preserving the EW image have angle an integral
multiple of 2π/k. The obstruction is the checkerboard, not end asymptotics. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open Complex Set
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

lemma image_power_nonpos {p : SpacePoint} (hp : p ∈ R.spaceImage)
    (hz : |p.2| ≤ Real.pi / 2) : (p.1 ^ k).re ≤ 0 := by
  obtain ⟨q, rfl⟩ := hp
  exact R.checkerboard_power q hz

lemma image_midplane_unit {θ : ℝ} (hθ : Real.cos ((k : ℝ) * θ) = 0) :
    (Complex.exp ((θ : ℂ) * I), Real.pi / 2) ∈ R.spaceImage := by
  obtain ⟨q, hq⟩ := R.exists_midplane_line (s := 1) hθ
  refine ⟨q, ?_⟩
  apply Prod.ext
  · dsimp only [spaceImmersion, horizontalComplex]
    rw [hq]
    apply Complex.ext
    · rw [Complex.exp_ofReal_mul_I_re]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, one_mul]
    · rw [Complex.exp_ofReal_mul_I_im]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add, one_mul]
  · exact congrArg (fun p : AmbientTriple => p.2.2) hq

lemma power_re_zero_height {p : SpacePoint} (hp : p ∈ R.spaceImage)
    (hre : (p.1 ^ k).re = 0) : Real.cos p.2 = 0 := by
  obtain ⟨q, rfl⟩ := hp
  let z := R.horizontalComplex q
  by_cases hz : z = 0
  · have ha : R.OnVerticalAxis q := by
      constructor
      · have hh := congrArg Complex.re hz
        simpa [z, horizontalComplex] using hh
      · have hh := congrArg Complex.im hz
        simpa [z, horizontalComplex] using hh
    obtain ⟨n, hn⟩ := R.axis_height_half_integer q ha
    change Real.cos (HeightLift.height q + Real.pi) = 0
    rw [hn]
    apply Real.cos_eq_zero_iff.mpr
    exact ⟨n, by ring⟩
  · have he : z ^ k = (‖z‖ : ℂ) ^ k *
        Complex.exp ((((k : ℝ) * z.arg : ℝ) : ℂ) * I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
      rw [mul_pow, ← Complex.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hθ : Real.cos ((k : ℝ) * z.arg) = 0 := by
      change (z ^ k).re = 0 at hre
      rw [he, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
        Complex.exp_ofReal_mul_I_re] at hre
      exact (mul_eq_zero.mp hre).resolve_left (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))
    have hplane : (centeredLiftAmbient R.C R.t q).2.1 * Real.cos z.arg =
        (centeredLiftAmbient R.C R.t q).1 * Real.sin z.arg := by
      have hx : ‖z‖ * Real.cos z.arg = (centeredLiftAmbient R.C R.t q).1 := by
        simpa only [z, horizontalComplex, Complex.add_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, sub_zero, add_zero] using Complex.norm_mul_cos_arg z
      have hy : ‖z‖ * Real.sin z.arg = (centeredLiftAmbient R.C R.t q).2.1 := by
        simpa only [z, horizontalComplex, Complex.add_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
          mul_one, mul_zero, add_zero, zero_add] using Complex.norm_mul_sin_arg z
      calc
        _ = (‖z‖ * Real.sin z.arg) * Real.cos z.arg :=
          congrArg (fun t => t * Real.cos z.arg) hy.symm
        _ = (‖z‖ * Real.cos z.arg) * Real.sin z.arg := by ring
        _ = _ := congrArg (fun t => t * Real.sin z.arg) hx
    have hm : centeredLiftAmbient R.C R.t q ∈
        Set.range (centeredLiftAmbient (k := k) R.C R.t) ∩
          {p : AmbientTriple | p.2.1 * Real.cos z.arg = p.1 * Real.sin z.arg} :=
      ⟨⟨q, rfl⟩, hplane⟩
    rw [R.vertical_plane_image hθ] at hm
    obtain ⟨n, hn⟩ := hm.2
    change HeightLift.height q + Real.pi = _ at hn
    change Real.cos (HeightLift.height q + Real.pi) = 0
    rw [hn]
    exact Real.cos_eq_zero_iff.mpr ⟨n, by ring⟩

lemma exists_image_height_zero : ∃ z : ℂ, (z, (0 : ℝ)) ∈ R.spaceImage := by
  obtain ⟨q, hq⟩ := exists_halfPeriod_over_disk h.out (reflectionBasepoint k)
    (reflectionBasepoint k) rfl R.C (by simp [reflectionBasepoint])
  have hc := cos_lift_height_shift h.out (reflectionBasepoint k) (reflectionBasepoint k)
    rfl R.C q.val hq
  have hcos : Real.cos (HeightLift.height q.val + Real.pi) = -1 := by
    norm_num [reflectionBasepoint, heightCayley, Complex.div_re, Complex.div_im,
      Complex.norm_def, Complex.normSq_apply] at hc ⊢
    exact hc
  have hh : HeightLift.height q.val + Real.pi = Real.pi := by
    apply Real.strictAntiOn_cos.injOn q.property ⟨Real.pi_pos.le, le_rfl⟩
    rw [hcos, Real.cos_pi]
  have hp : R.spaceImmersion q.val ∈ R.spaceImage := ⟨q.val, rfl⟩
  have hs := (R.mem_spaceScrew_iff _).mpr ((R.mem_spaceReflectZ_iff _).mpr hp)
  refine ⟨screwPhase (k := k) * R.horizontalComplex q.val, ?_⟩
  simpa [spaceImmersion, spaceReflectZ, spaceScrew, hh] using hs

/-- A pure horizontal rotation preserving the image is a k-th root of unity. -/
theorem image_rotation_root {c : ℂ} (hc : ‖c‖ = 1)
    (hs : ∀ p, spaceTurn c p ∈ R.spaceImage ↔ p ∈ R.spaceImage) : c ^ k = 1 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by have := h.out; omega)
  let β := Real.pi / (2 * k)
  have hb : (k : ℝ) * β = Real.pi / 2 := by dsimp [β]; field_simp
  have hp (θ : ℝ) (ht : Real.cos ((k : ℝ) * θ) = 0) :
      ((c * Complex.exp ((θ : ℂ) * I)) ^ k).re ≤ 0 := by
    exact R.image_power_nonpos ((hs _).mpr (R.image_midplane_unit ht))
      (by
        change |Real.pi / 2| ≤ Real.pi / 2
        rw [abs_of_nonneg (by positivity)])
  have he (θ : ℝ) : (Complex.exp ((θ : ℂ) * I)) ^ k =
      Complex.exp ((((k : ℝ) * θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hp1 := hp β (by rw [hb, Real.cos_pi_div_two])
  have hp2 := hp (-β) (by rw [mul_neg, Real.cos_neg, hb, Real.cos_pi_div_two])
  rw [mul_pow, he, hb] at hp1
  rw [mul_pow, he, mul_neg, hb] at hp2
  simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_neg, Real.sin_neg] at hp1 hp2
  have him : (c ^ k).im = 0 := by linarith
  have hn : ‖c ^ k‖ = 1 := by simp [norm_pow, hc]
  have hr : (c ^ k).re = 1 ∨ (c ^ k).re = -1 := by
    have hh := Complex.normSq_eq_norm_sq (c ^ k)
    simp [Complex.normSq_apply, him, hn] at hh
    exact sq_eq_one_iff.mp (by nlinarith : (c ^ k).re ^ 2 = 1)
  rcases hr with hr | hr
  · exact Complex.ext hr him
  · have hminus : c ^ k = -1 := Complex.ext (by simpa using hr) (by simpa using him)
    obtain ⟨z, hz⟩ := R.exists_image_height_zero
    have hle := R.image_power_nonpos hz (by
      change |(0 : ℝ)| ≤ Real.pi / 2
      rw [abs_zero]
      positivity)
    have hle' := R.image_power_nonpos ((hs _).mpr hz) (by
      change |(0 : ℝ)| ≤ Real.pi / 2
      rw [abs_zero]
      positivity)
    change ((c * z) ^ k).re ≤ 0 at hle'
    rw [mul_pow, hminus] at hle'
    simp only [neg_one_mul, Complex.neg_re] at hle'
    have hzero : (z ^ k).re = 0 := by linarith
    have hh := R.power_re_zero_height hz hzero
    norm_num at hh

end KsIndex.KarcherData.PaperHalfPeriodRealization
