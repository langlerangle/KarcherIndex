module

public import KsIndexLean.KarcherLiftConnected

@[expose] public section


/-! The rational height coordinate underlying the half-period disk criterion.
Its logarithmic derivative is i times the actual third EW differential. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex

def heightCayley (k : ℕ) (w : ℂ) : ℂ := (1 + I * w ^ k) / (1 - I * w ^ k)

lemma height_factors {k : ℕ} (w : ℂ) :
    (1 + I * w ^ k) * (1 - I * w ^ k) = 1 + w ^ (2 * k) := by
  rw [mul_comm 2 k, pow_mul]
  linear_combination -(w ^ k) ^ 2 * Complex.I_sq

lemma height_factors_ne {k : ℕ} {w : ℂ} (hw : w ∉ Surface.punctures k) :
    1 + I * w ^ k ≠ 0 ∧ 1 - I * w ^ k ≠ 0 := by
  have hn : 1 + w ^ (2 * k) ≠ 0 := by
    intro he
    apply hw
    change w ^ (2 * k) = -1
    linear_combination he
  rw [← height_factors] at hn
  exact mul_ne_zero_iff.mp hn

lemma heightCayley_ne_zero {k : ℕ} {w : ℂ} (hw : w ∉ Surface.punctures k) :
    heightCayley k w ≠ 0 := div_ne_zero (height_factors_ne hw).1 (height_factors_ne hw).2

/-- The real-part formula determines its sign from the powered radius away from
the punctures. -/
lemma heightCayley_re (k : ℕ) (w : ℂ) :
    (heightCayley k w).re = (1 - Complex.normSq (w ^ k)) / Complex.normSq (1 - I * w ^ k) := by
  unfold heightCayley
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

/-- Multiplying the actual vertical EW form by i gives the logarithmic derivative
of the Cayley coordinate away from the punctures. -/
lemma hasDerivAt_heightCayley {k : ℕ} {w : ℂ} (hw : w ∉ Surface.punctures k) :
    HasDerivAt (heightCayley k) (I * coeff3 k w * heightCayley k w) w := by
  have hp := (hasDerivAt_pow k w).const_mul I
  have hd := (hp.const_add 1).div (hp.const_sub 1) (height_factors_ne hw).2
  have he : I * coeff3 k w * heightCayley k w =
      (I * ((k : ℂ) * w ^ (k - 1)) * (1 - I * w ^ k) -
        (1 + I * w ^ k) * -(I * ((k : ℂ) * w ^ (k - 1)))) / (1 - I * w ^ k) ^ 2 := by
    unfold coeff3 Weierstrass.phi3 gauss etaTarget heightCayley
    have hden : 1 + w ^ (2 * k) ≠ 0 := by
      rw [← height_factors]
      exact mul_ne_zero (height_factors_ne hw).1 (height_factors_ne hw).2
    field_simp [hden, (height_factors_ne hw).2]
    rw [← height_factors]
    ring
  rw [← he] at hd
  exact hd

lemma heightCayley_re_pos_iff {k : ℕ} (hk : 0 < k) {w : ℂ}
    (hw : w ∉ Surface.punctures k) : 0 < (heightCayley k w).re ↔ ‖w‖ < 1 := by
  rw [heightCayley_re, div_pos_iff_of_pos_right (Complex.normSq_pos.mpr (height_factors_ne hw).2),
    sub_pos, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul]
  exact pow_lt_one_iff_of_nonneg (norm_nonneg w) (by omega)

lemma heightCayley_re_zero_iff {k : ℕ} (hk : 0 < k) {w : ℂ}
    (hw : w ∉ Surface.punctures k) : (heightCayley k w).re = 0 ↔ ‖w‖ = 1 := by
  rw [heightCayley_re, div_eq_zero_iff]
  have hn := (Complex.normSq_pos.mpr (height_factors_ne hw).2).ne'
  simp only [hn, or_false, sub_eq_zero]
  rw [eq_comm, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul]
  exact pow_eq_one_iff_of_nonneg (norm_nonneg w) (by omega)

open Set MeasureTheory Piecewise

/-- Exponentiating i times the actual vertical contour integral gives the exact
 ratio of the rational height coordinates at the endpoints. -/
theorem exp_piece_vertical {k : ℕ} (p : Piece)
    (hA : ∀ z ∈ Surface.punctures k, p.Avoids z) :
    Complex.exp (I * p.contour (coeff3 k)) = heightCayley k p.finish / heightCayley k p.start := by
  have hn : ∀ t ∈ Icc p.a p.b, p.curve t ∉ Surface.punctures k :=
    fun t ht hz => hA _ hz t ht rfl
  have hc : ContinuousOn (fun t => heightCayley k (p.curve t)) (Icc p.a p.b) := by
    intro t ht
    exact (hasDerivAt_heightCayley (hn t ht)).continuousAt.comp_continuousWithinAt
      (p.continuous_curve t ht)
  have hf : ContinuousOn (fun t => coeff3 k (p.curve t)) (Icc p.a p.b) := by
    intro t ht
    exact (differentiableAt_coeff3 (hn t ht)).continuousAt.comp_continuousWithinAt
      (p.continuous_curve t ht)
  have hv := p.continuous_velocity.mul (((continuousOn_const (c := I)).mul hf).mul hc)
  have hd : ∀ t ∈ Icc p.a p.b,
      HasDerivWithinAt (fun t => heightCayley k (p.curve t))
        (p.velocity t * (I * coeff3 k (p.curve t) * heightCayley k (p.curve t)))
        (Icc p.a p.b) t := by
    intro t ht
    simpa only [smul_eq_mul, Function.comp_def] using
      (hasDerivAt_heightCayley (hn t ht)).scomp_hasDerivWithinAt t (p.derivative t ht)
  have he := LoopTransport.exp_integral_logarithmicDerivative p.lt hc hv hd
    (fun t ht => heightCayley_ne_zero (hn t ht))
  have hint : (∫ t in p.a..p.b,
      p.velocity t * (I * coeff3 k (p.curve t) * heightCayley k (p.curve t)) /
        heightCayley k (p.curve t)) = I * p.contour (coeff3 k) := by
    rw [Piece.contour, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc p.a p.b := by simpa only [uIcc_of_le p.lt.le] using ht
    field_simp [heightCayley_ne_zero (hn t ht')]
  simp only [Pi.mul_apply] at he
  rw [hint] at he
  exact he

/-- The height identity telescopes across every finite contour chain. -/
theorem exp_chain_vertical {k : ℕ} (C : Chain)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    Complex.exp (I * C.contour (coeff3 k)) =
      heightCayley k C.finish / heightCayley k C.start := by
  rcases C with ⟨n, p, hm⟩
  change Complex.exp (I * ∑ i, (p i).contour (coeff3 k)) =
    heightCayley k (p (Fin.last n)).finish / heightCayley k (p 0).start
  induction n with
  | zero => simpa using exp_piece_vertical (p 0) (fun z hz => hA z hz 0)
  | succ n ih =>
    rw [Fin.sum_univ_succ, mul_add, Complex.exp_add,
      exp_piece_vertical (p 0) (fun z hz => hA z hz 0)]
    rw [ih (fun i => p i.succ) (fun i => hm i.succ) (fun z hz i => hA z hz i.succ)]
    have hj := hm (0 : Fin (n + 1))
    simp only [Fin.castSucc_zero] at hj
    rw [hj]
    have hn : heightCayley k (p (Fin.succ 0)).start ≠ 0 :=
      heightCayley_ne_zero (fun hz => (p (Fin.succ 0)).start_ne (hA _ hz _) rfl)
    have hl : (Fin.last n).succ = Fin.last (n + 1) := rfl
    rw [hl]
    field_simp

/-- Removing the positive exponential amplitude leaves precisely the phase of
 the real part of a complex vertical integral. -/
lemma exp_real_vertical (z : ℂ) :
    Complex.exp (I * (z.re : ℂ)) = Complex.exp (I * z) / (‖Complex.exp (I * z)‖ : ℂ) := by
  rw [Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- The real EW height has the phase of the endpoint Cayley ratio. -/
theorem exp_chain_real_vertical {k : ℕ} (C : Chain)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    Complex.exp (I * ((C.contour (coeff3 k)).re : ℂ)) =
      (heightCayley k C.finish / heightCayley k C.start) /
        (‖heightCayley k C.finish / heightCayley k C.start‖ : ℂ) := by
  rw [exp_real_vertical, exp_chain_vertical C hA]

lemma heightCayley_one (k : ℕ) : heightCayley k 1 = I := by
  unfold heightCayley
  simp only [one_pow, mul_one]
  apply (div_eq_iff (by intro h; have := congrArg Complex.re h; norm_num at this : (1 - I : ℂ) ≠ 0)).mpr
  linear_combination Complex.I_sq

/-- The based height at w=1 has the negative Cayley phase. Translating by π
 is therefore the normalization that puts the disk in the positive half-period. -/
theorem sin_chain_height_shift {k : ℕ} (C : Chain)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) (hs : C.start = 1) :
    Real.sin ((C.contour (coeff3 k)).re + Real.pi) =
      (heightCayley k C.finish).re / ‖heightCayley k C.finish‖ := by
  have he := congrArg Complex.im (exp_chain_real_vertical C hA)
  rw [hs, heightCayley_one] at he
  simp only [norm_div, Complex.norm_I, div_one] at he
  rw [mul_comm I, Complex.exp_ofReal_mul_I_im] at he
  simp only [Complex.div_im, Complex.I_re, Complex.I_im, Complex.normSq_I,
    mul_zero, mul_one, zero_sub, div_one, Complex.ofReal_re, Complex.ofReal_im,
    Complex.normSq_ofReal] at he
  rw [Real.sin_add_pi, he]
  have hn : ‖heightCayley k C.finish‖ ≠ 0 := norm_ne_zero_iff.mpr
    (heightCayley_ne_zero (fun hz => C.finish_ne (hA _ hz) rfl))
  field_simp
  ring

/-- The interior disk criterion for every actual based contour height. -/
theorem sin_chain_height_shift_pos_iff {k : ℕ} (hk : 0 < k) (C : Chain)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) (hs : C.start = 1) :
    0 < Real.sin ((C.contour (coeff3 k)).re + Real.pi) ↔ ‖C.finish‖ < 1 := by
  have hw : C.finish ∉ Surface.punctures k := fun hz => C.finish_ne (hA _ hz) rfl
  rw [sin_chain_height_shift C hA hs,
    div_pos_iff_of_pos_right (norm_pos_iff.mpr (heightCayley_ne_zero hw))]
  exact heightCayley_re_pos_iff hk hw

/-- The unit-circle boundary criterion for every actual based contour height. -/
theorem sin_chain_height_shift_zero_iff {k : ℕ} (hk : 0 < k) (C : Chain)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) (hs : C.start = 1) :
    Real.sin ((C.contour (coeff3 k)).re + Real.pi) = 0 ↔ ‖C.finish‖ = 1 := by
  have hw : C.finish ∉ Surface.punctures k := fun hz => C.finish_ne (hA _ hz) rfl
  rw [sin_chain_height_shift C hA hs, div_eq_zero_iff]
  simp only [norm_ne_zero_iff.mpr (heightCayley_ne_zero hw), or_false]
  exact heightCayley_re_zero_iff hk hw

/-- At a finite point of the intrinsic carrier the actual real height satisfies
 the normalized sine formula, independently of its chosen integral sheet. -/
theorem sin_lift_height_shift {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget)
    (q : PeriodicEWCarrier hk b C)
    (hq : HeightLift.projection q = finiteParameter w) :
    Real.sin (HeightLift.height q + Real.pi) =
      (heightCayley k w.val).re / ‖heightCayley k w.val‖ := by
  have hv : projectPeriod (HeightLift.ambient q) = descendedIntegral hk b w := by
    rw [HeightLift.project_ambient, hq, extendedEWMap_finite]
  obtain ⟨D, hs, ht, hD, he⟩ := exists_chain_with_real_integral hk b w
    (HeightLift.ambient q) hv
  have hz : (D.contour (coeff3 k)).re = HeightLift.height q :=
    congrArg (fun v : AmbientTriple => v.2.2) he
  have hh := sin_chain_height_shift D hD (hs.trans hb)
  rw [hz, ht] at hh
  exact hh

theorem sin_lift_height_shift_pos_iff {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget)
    (q : PeriodicEWCarrier hk b C)
    (hq : HeightLift.projection q = finiteParameter w) :
    0 < Real.sin (HeightLift.height q + Real.pi) ↔ ‖w.val‖ < 1 := by
  rw [sin_lift_height_shift hk b w hb C q hq,
    div_pos_iff_of_pos_right (norm_pos_iff.mpr (heightCayley_ne_zero w.property))]
  exact heightCayley_re_pos_iff (by omega) w.property

theorem sin_lift_height_shift_zero_iff {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget)
    (q : PeriodicEWCarrier hk b C)
    (hq : HeightLift.projection q = finiteParameter w) :
    Real.sin (HeightLift.height q + Real.pi) = 0 ↔ ‖w.val‖ = 1 := by
  rw [sin_lift_height_shift hk b w hb C q hq, div_eq_zero_iff]
  simp only [norm_ne_zero_iff.mpr (heightCayley_ne_zero w.property), or_false]
  exact heightCayley_re_zero_iff (by omega) w.property

/-- The imaginary part records the alternating boundary arc sign. -/
lemma heightCayley_im (k : ℕ) (w : ℂ) :
    (heightCayley k w).im = 2 * (w ^ k).re / Complex.normSq (1 - I * w ^ k) := by
  unfold heightCayley
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im]
  ring

/-- Cosine distinguishes the two boundary levels after the paper's π shift. -/
theorem cos_chain_height_shift {k : ℕ} (C : Chain)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) (hs : C.start = 1) :
    Real.cos ((C.contour (coeff3 k)).re + Real.pi) =
      -(heightCayley k C.finish).im / ‖heightCayley k C.finish‖ := by
  have he := congrArg Complex.re (exp_chain_real_vertical C hA)
  rw [hs, heightCayley_one] at he
  simp only [norm_div, Complex.norm_I, div_one] at he
  rw [mul_comm I, Complex.exp_ofReal_mul_I_re] at he
  simp only [Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im, Complex.normSq_I,
    mul_zero, mul_one, zero_sub, div_one, Complex.ofReal_re, Complex.ofReal_im,
    Complex.normSq_ofReal] at he
  rw [Real.cos_add_pi, he]
  have hn : ‖heightCayley k C.finish‖ ≠ 0 := norm_ne_zero_iff.mpr
    (heightCayley_ne_zero (fun hz => C.finish_ne (hA _ hz) rfl))
  field_simp
  ring

theorem cos_lift_height_shift {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget)
    (q : PeriodicEWCarrier hk b C)
    (hq : HeightLift.projection q = finiteParameter w) :
    Real.cos (HeightLift.height q + Real.pi) =
      -(heightCayley k w.val).im / ‖heightCayley k w.val‖ := by
  have hv : projectPeriod (HeightLift.ambient q) = descendedIntegral hk b w := by
    rw [HeightLift.project_ambient, hq, extendedEWMap_finite]
  obtain ⟨D, hs, ht, hD, he⟩ := exists_chain_with_real_integral hk b w (HeightLift.ambient q) hv
  have hz : (D.contour (coeff3 k)).re = HeightLift.height q :=
    congrArg (fun v : AmbientTriple => v.2.2) he
  have hh := cos_chain_height_shift D hD (hs.trans hb)
  rwa [hz, ht] at hh

theorem cos_lift_height_shift_pos_iff {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget)
    (q : PeriodicEWCarrier hk b C)
    (hq : HeightLift.projection q = finiteParameter w) :
    0 < Real.cos (HeightLift.height q + Real.pi) ↔ (w.val ^ k).re < 0 := by
  rw [cos_lift_height_shift hk b w hb C q hq,
    div_pos_iff_of_pos_right (norm_pos_iff.mpr (heightCayley_ne_zero w.property)),
    neg_pos, heightCayley_im,
    div_lt_iff₀ (Complex.normSq_pos.mpr (height_factors_ne w.property).2)]
  constructor <;> intro hh <;> linarith

theorem cos_lift_height_shift_neg_iff {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget)
    (q : PeriodicEWCarrier hk b C)
    (hq : HeightLift.projection q = finiteParameter w) :
    Real.cos (HeightLift.height q + Real.pi) < 0 ↔ 0 < (w.val ^ k).re := by
  rw [cos_lift_height_shift hk b w hb C q hq,
    div_lt_iff₀ (norm_pos_iff.mpr (heightCayley_ne_zero w.property)),
    zero_mul, neg_lt_zero, heightCayley_im,
    div_pos_iff_of_pos_right (Complex.normSq_pos.mpr (height_factors_ne w.property).2)]
  constructor <;> intro hh <;> linarith

end KsIndex.KarcherData
