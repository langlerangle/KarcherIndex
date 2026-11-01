module

/-
KsIndexLean — Arc support as a Fourier-coefficient fixed-point identity.

For continuous `u : ℝ → ℂ` and `δ > 0`, assume `u θ = 0` whenever
`cos θ < δ`. Then `convS₁ (fc u) = fc u`. Here `fc` is the normalized
window integral on `0..2π`; periodicity and smoothness of `u` are not
hypotheses of this theorem. The weighted summability required for full
`MemArc` membership is a separate condition.

The proof uses the symmetric square-wave partial sums
`sqw J θ = (4/π) * ∑ j < J+1, (-1)^j * cos((2*j+1)*θ)/(2*j+1)`.
They converge pointwise to `1` on the positive-cosine arc. On the portion
`cos θ ≥ δ` of the integration window, their distance from `1` has a bound
independent of `J`. This bound and continuity of `u` provide an integrable
dominator, so the coefficients of `sqw J * u` converge to those of `u`.

The trigonometric-polynomial expansion identifies these coefficients with
finite convolution sums. Square summability of `fc u` gives convergence of
those sums to `convS₁ (fc u)`. Uniqueness of the coefficientwise limit proves
the fixed-point identity.
-/
public import KsIndexLean.SquareWave
public import KsIndexLean.ArcSpace
public import KsIndexLean.Parseval1

@[expose] public section


noncomputable section

open Real Filter Topology
open scoped ContDiff

namespace KsIndex.ArcBridge

open KsIndex.SquareWave KsIndex.Parseval KsIndex.ArcSpace KsIndex.CircleQ
  MeasureTheory intervalIntegral

/-! ### The symmetric partial sums of the square wave -/

/-- `sqw J θ = (4/π) ∑_{j≤J} (−1)^j cos((2j+1)θ)/(2j+1)`: the symmetric partial sum of the Fourier
series of `ς₁ = sgn cos θ` (normalized so `sqw J → 1` on the open arc `{cos > 0}`). -/
def sqw (J : ℕ) (θ : ℝ) : ℝ :=
  (4 / π) * ∑ j ∈ Finset.range (J + 1),
    (-1 : ℝ) ^ j * Real.cos ((2 * (j : ℝ) + 1) * θ) / (2 * (j : ℝ) + 1)

/-- `sqw J` is even (`cos` is even). -/
lemma sqw_neg (J : ℕ) (θ : ℝ) : sqw J (-θ) = sqw J θ := by
  unfold sqw
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (2 * (j : ℝ) + 1) * (-θ) = -((2 * (j : ℝ) + 1) * θ) by ring, Real.cos_neg]

/-! ### The Leibniz and oscillatory-integral parts -/

/-- The Leibniz partial sums converge to `π/4`. -/
lemma tendsto_leibniz :
    Tendsto (fun J : ℕ => ∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1))
      atTop (𝓝 (π / 4)) := by
  refine (tendsto_sum_pi_div_four.comp (tendsto_add_atTop_nat 1)).congr (fun J => ?_)
  simp only [Function.comp_apply]

/-- The oscillatory-integral remainder of the square-wave partial sum tends to `0` (for `0 ≤ x`). -/
lemma tendsto_sqw_integral {x : ℝ} (hx0 : 0 ≤ x) (hx : x < π / 2) :
    Tendsto (fun J : ℕ => (-1 : ℝ) ^ J * ∫ t in (0 : ℝ)..x,
        Real.sin (2 * ((J : ℝ) + 1) * t) / (2 * Real.cos t)) atTop (𝓝 0) := by
  have hmap : Tendsto (fun J : ℕ => 2 * (J + 1)) atTop atTop := by
    refine tendsto_atTop_mono (fun J => ?_) tendsto_id
    simp only [id_eq]; omega
  have hB := (tendsto_integral_sin_mul_div_cos hx0 hx).comp hmap
  have hB' : Tendsto (fun J : ℕ => ∫ t in (0 : ℝ)..x,
      Real.sin (2 * ((J : ℝ) + 1) * t) / (2 * Real.cos t)) atTop (𝓝 0) := by
    have heq : (fun J : ℕ => ∫ t in (0 : ℝ)..x, Real.sin (2 * ((J : ℝ) + 1) * t) / (2 * Real.cos t))
        = fun J : ℕ => (2 : ℝ)⁻¹ * ((fun M : ℕ => ∫ t in (0 : ℝ)..x,
            Real.sin ((M : ℝ) * t) / Real.cos t) ∘ fun J => 2 * (J + 1)) J := by
      funext J
      simp only [Function.comp_apply]
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      push_cast; ring
    rw [heq]; simpa using hB.const_mul (2 : ℝ)⁻¹
  refine squeeze_zero_norm (fun J => le_of_eq ?_) (by simpa using hB'.norm)
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]

/-! ### The pointwise limit -/

/-- `sqw J θ → 1` for `|θ| < π/2` (the open arc `{cos θ > 0}`, modulo `2π`). -/
lemma tendsto_sqw {θ : ℝ} (hθ : |θ| < π / 2) : Tendsto (fun J : ℕ => sqw J θ) atTop (𝓝 1) := by
  -- reduce to `0 ≤ θ` by evenness
  wlog hθ0 : 0 ≤ θ generalizing θ with H
  · have h := H (by rwa [abs_neg]) (le_of_lt (by linarith [not_le.mp hθ0] : (0 : ℝ) < -θ))
    exact h.congr (fun J => sqw_neg J θ)
  have hx : θ < π / 2 := by rwa [abs_of_nonneg hθ0] at hθ
  have hpipos : (0 : ℝ) < π := pi_pos
  -- `sqw J θ = (4/π) · (Leibniz_J − remainder_J)`
  have hrw : (fun J : ℕ => sqw J θ)
      = fun J : ℕ => (4 / π) * ((∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1))
          - (-1 : ℝ) ^ J * ∫ t in (0 : ℝ)..θ,
              Real.sin (2 * ((J : ℝ) + 1) * t) / (2 * Real.cos t)) := by
    funext J
    unfold sqw
    rw [square_wave_partial_sum J (by rwa [abs_of_nonneg hθ0])]
  rw [hrw]
  have hlim : Tendsto (fun J : ℕ => (∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1))
      - (-1 : ℝ) ^ J * ∫ t in (0 : ℝ)..θ,
          Real.sin (2 * ((J : ℝ) + 1) * t) / (2 * Real.cos t)) atTop (𝓝 (π / 4)) := by
    have := tendsto_leibniz.sub (tendsto_sqw_integral hθ0 hx)
    simpa using this
  have := hlim.const_mul (4 / π)
  rw [show (4 / π) * (π / 4) = 1 by field_simp] at this
  exact this

/-! ### The uniform-in-`J` bound (for dominated convergence) -/

/-- The Leibniz partial sums stay within a fixed distance of `π/4` (a convergent sequence is
bounded). -/
lemma exists_leibniz_bound :
    ∃ C : ℝ, ∀ J : ℕ,
      |(∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1)) - π / 4| ≤ C := by
  have hb : BddAbove (Set.range (fun J : ℕ =>
      |(∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1)) - π / 4|)) := by
    have : Tendsto (fun J : ℕ =>
        |(∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1)) - π / 4|) atTop (𝓝 0) := by
      have := (tendsto_leibniz.sub_const (π / 4)).abs; simpa using this
    exact this.bddAbove_range
  obtain ⟨C, hC⟩ := hb
  exact ⟨C, fun J => hC ⟨J, rfl⟩⟩

/-- The oscillatory-integral remainder is bounded uniformly on `[0, θ₀]`:
`|∫₀^θ sin(Mt)/cos t| ≤ 4/√(cos θ₀)`. -/
lemma abs_integral_sin_div_cos_le {M θ θ₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ θ₀) (hθ₀ : θ₀ < π / 2) :
    |∫ t in (0 : ℝ)..θ, Real.sin (M * t) / Real.cos t| ≤ 4 / Real.sqrt (Real.cos θ₀) := by
  have hθlt : θ < π / 2 := lt_of_le_of_lt hθ hθ₀
  have hcospos : ∀ t ∈ Set.Icc (0 : ℝ) θ, 0 < Real.cos t := fun t ht =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcosθ₀ : 0 < Real.cos θ₀ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ₀⟩
  have hcosθ : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθlt⟩
  have hII1 : IntervalIntegrable (fun t => Real.sin (M * t) / Real.cos t)
      MeasureTheory.volume 0 θ := by
    apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le hθ0]
    exact ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hcospos t ht).ne')
  have hII2 : IntervalIntegrable (fun t => (1 : ℝ) / Real.cos t) MeasureTheory.volume 0 θ := by
    apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le hθ0]
    exact ContinuousOn.div continuousOn_const (by fun_prop) (fun t ht => (hcospos t ht).ne')
  have hstep1 : |∫ t in (0 : ℝ)..θ, Real.sin (M * t) / Real.cos t|
      ≤ ∫ t in (0 : ℝ)..θ, 1 / Real.cos t := by
    calc |∫ t in (0 : ℝ)..θ, Real.sin (M * t) / Real.cos t|
        ≤ ∫ t in (0 : ℝ)..θ, |Real.sin (M * t) / Real.cos t| :=
          intervalIntegral.abs_integral_le_integral_abs hθ0
      _ ≤ ∫ t in (0 : ℝ)..θ, 1 / Real.cos t := by
          refine intervalIntegral.integral_mono_on hθ0 hII1.abs hII2 (fun t ht => ?_)
          rw [abs_div, abs_of_pos (hcospos t ht)]
          gcongr
          · exact (hcospos t ht).le
          · exact Real.abs_sin_le_one _
  have hLeafC := sqrt_cos_mul_integral_inv_cos_le hθ0 hθlt
  have hInt_le : (∫ t in (0 : ℝ)..θ, 1 / Real.cos t) ≤ 4 / Real.sqrt (Real.cos θ) := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hcosθ)]
    calc (∫ t in (0 : ℝ)..θ, 1 / Real.cos t) * Real.sqrt (Real.cos θ)
        = Real.sqrt (Real.cos θ) * ∫ t in (0 : ℝ)..θ, 1 / Real.cos t := by ring
      _ ≤ 4 := hLeafC
  have hsqrtle : Real.sqrt (Real.cos θ₀) ≤ Real.sqrt (Real.cos θ) :=
    Real.sqrt_le_sqrt (Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith) hθ)
  calc |∫ t in (0 : ℝ)..θ, Real.sin (M * t) / Real.cos t|
      ≤ ∫ t in (0 : ℝ)..θ, 1 / Real.cos t := hstep1
    _ ≤ 4 / Real.sqrt (Real.cos θ) := hInt_le
    _ ≤ 4 / Real.sqrt (Real.cos θ₀) := by gcongr

/-- **The uniform-in-`J` bound.**  On `[0, θ₀]` (with `θ₀ < π/2`), `|sqw J θ − 1|` is bounded by a
`J`-independent constant `(4/π)(C + 2/√(cos θ₀))`, where `C` bounds the Leibniz distance. -/
lemma sqw_sub_one_bound {C : ℝ}
    (hC : ∀ J : ℕ, |(∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1)) - π / 4| ≤ C)
    (J : ℕ) {θ θ₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ θ₀) (hθ₀ : θ₀ < π / 2) :
    |sqw J θ - 1| ≤ (4 / π) * (C + 2 / Real.sqrt (Real.cos θ₀)) := by
  have hpi : (0 : ℝ) < π := pi_pos
  set L := ∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1) with hL
  set I := ∫ t in (0 : ℝ)..θ, Real.sin (2 * ((J : ℝ) + 1) * t) / (2 * Real.cos t) with hI
  -- `sqw J θ = (4/π)(L − (−1)^J I)`
  have hsqw : sqw J θ = (4 / π) * (L - (-1 : ℝ) ^ J * I) := by
    unfold sqw
    rw [hL, hI, square_wave_partial_sum J (by rw [abs_of_nonneg hθ0]; exact lt_of_le_of_lt hθ hθ₀)]
  -- pull the `1/2` out of `I`
  have hI2 : I = (2 : ℝ)⁻¹ * ∫ t in (0 : ℝ)..θ, Real.sin (2 * ((J : ℝ) + 1) * t) / Real.cos t := by
    rw [hI, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_); ring
  have hIbound : |I| ≤ 2 / Real.sqrt (Real.cos θ₀) := by
    rw [hI2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
    have := abs_integral_sin_div_cos_le (M := 2 * ((J : ℝ) + 1)) hθ0 hθ hθ₀
    calc (2 : ℝ)⁻¹ * |∫ t in (0 : ℝ)..θ, Real.sin (2 * ((J : ℝ) + 1) * t) / Real.cos t|
        ≤ (2 : ℝ)⁻¹ * (4 / Real.sqrt (Real.cos θ₀)) := by gcongr
      _ = 2 / Real.sqrt (Real.cos θ₀) := by ring
  -- `sqw J θ − 1 = (4/π)(L − π/4) − (4/π)(−1)^J I`
  have hkey : sqw J θ - 1 = (4 / π) * (L - π / 4) - (4 / π) * ((-1 : ℝ) ^ J * I) := by
    rw [hsqw]; field_simp; ring
  rw [hkey]
  have hfour : (0 : ℝ) ≤ 4 / π := by positivity
  calc |(4 / π) * (L - π / 4) - (4 / π) * ((-1 : ℝ) ^ J * I)|
      ≤ |(4 / π) * (L - π / 4)| + |(4 / π) * ((-1 : ℝ) ^ J * I)| := abs_sub _ _
    _ = (4 / π) * |L - π / 4| + (4 / π) * |I| := by
        simp only [abs_mul, abs_of_nonneg hfour, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    _ ≤ (4 / π) * C + (4 / π) * (2 / Real.sqrt (Real.cos θ₀)) := by
        gcongr
        exact hC J
    _ = (4 / π) * (C + 2 / Real.sqrt (Real.cos θ₀)) := by ring

/-! ### Fourier-coefficient toolkit -/

/-- **Frequency shift**: `fc (e^{idθ}·u) m = fc u (m − d)`. -/
lemma fc_freq_shift (u : ℝ → ℂ) (d m : ℤ) :
    fc (fun θ => Complex.exp ((d : ℂ) * Complex.I * θ) * u θ) m = fc u (m - d) := by
  unfold fc
  congr 1
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only []
  rw [show Complex.exp ((d : ℂ) * Complex.I * θ) * u θ * Complex.exp (-(m : ℂ) * Complex.I * θ)
      = u θ * (Complex.exp ((d : ℂ) * Complex.I * θ) * Complex.exp (-(m : ℂ) * Complex.I * θ))
        by ring,
    ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- `fc` distributes over a finite sum of continuous functions. -/
lemma fc_sum {ι : Type*} (g : ι → ℝ → ℂ) (s : Finset ι) (m : ℤ)
    (hg : ∀ i ∈ s, Continuous (g i)) :
    fc (fun θ => ∑ i ∈ s, g i θ) m = ∑ i ∈ s, fc (g i) m := by
  have hexp : Continuous (fun θ : ℝ => Complex.exp (-(m : ℂ) * Complex.I * θ)) := by fun_prop
  have hint : ∀ i ∈ s, IntervalIntegrable (fun θ => g i θ * Complex.exp (-(m : ℂ) * Complex.I * θ))
      MeasureTheory.volume 0 (2 * π) := fun i hi => ((hg i hi).mul hexp).intervalIntegrable _ _
  unfold fc
  rw [← Finset.mul_sum]
  congr 1
  rw [← intervalIntegral.integral_finsetSum hint]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [Finset.sum_mul]

/-- `fc` pulls out a constant factor. -/
lemma fc_const_mul (g : ℝ → ℂ) (a : ℂ) (m : ℤ) :
    fc (fun θ => a * g θ) m = a * fc g m := by
  unfold fc
  have hmul : (∫ θ in (0 : ℝ)..2 * π, (fun θ => a * g θ) θ * Complex.exp (-(m : ℂ) * Complex.I * θ))
      = a * ∫ θ in (0 : ℝ)..2 * π, g θ * Complex.exp (-(m : ℂ) * Complex.I * θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only []; ring
  rw [hmul]; ring

/-- `fc` distributes over a binary sum of continuous functions (via `fc_sum` over `Fin 2`). -/
lemma fc_add (g h : ℝ → ℂ) (m : ℤ) (hg : Continuous g) (hh : Continuous h) :
    fc (fun θ => g θ + h θ) m = fc g m + fc h m := by
  have key := fc_sum ![g, h] Finset.univ m (by intro i _; fin_cases i <;> assumption)
  simpa [Fin.sum_univ_two] using key

/-! ### The fc convolution identity -/

/-- `sqw J` as a trig polynomial: the symmetric partial sum of the `ς₁` exponential series
(the integrand identity, `u = 1` form). -/
lemma sqw_decomp (J : ℕ) (θ : ℝ) :
    ((sqw J θ : ℂ)) = ∑ j ∈ Finset.range (J + 1), (sgnHat (2 * (j : ℤ) + 1) : ℂ) *
        (Complex.exp ((↑(2 * (j : ℤ) + 1) : ℂ) * Complex.I * θ)
          + Complex.exp ((↑(-(2 * (j : ℤ) + 1)) : ℂ) * Complex.I * θ)) := by
  unfold sqw
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [sgnHat_odd, chat]
  push_cast
  rw [show ((2 * (x : ℂ) + 1)) * Complex.I * θ = ((2 * (x : ℂ) + 1) * θ) * Complex.I by ring,
    show (-(2 * (x : ℂ) + 1)) * Complex.I * θ = (-((2 * (x : ℂ) + 1) * θ)) * Complex.I by ring,
    ← Complex.two_cos]
  simp only [zpow_natCast]
  ring

/-- **The fc convolution identity.**  For continuous `u`, the `m`-th Fourier coefficient of
`sqw J · u` is the `(2J+1)`-truncated convolution
`∑_{j≤J} ς̂₁(2j+1)(fc u(m−(2j+1)) + fc u(m+(2j+1)))`
of `ς̂₁` with `fc u`. -/
lemma fc_sqw_mul (u : ℝ → ℂ) (hu : Continuous u) (J : ℕ) (m : ℤ) :
    fc (fun θ => (sqw J θ : ℂ) * u θ) m
      = ∑ j ∈ Finset.range (J + 1), (sgnHat (2 * (j : ℤ) + 1) : ℂ) *
          (fc u (m - (2 * (j : ℤ) + 1)) + fc u (m + (2 * (j : ℤ) + 1))) := by
  have hdecomp : (fun θ => (sqw J θ : ℂ) * u θ)
      = fun θ : ℝ => ∑ j ∈ Finset.range (J + 1), (sgnHat (2 * (j : ℤ) + 1) : ℂ) *
          (Complex.exp ((↑(2 * (j : ℤ) + 1) : ℂ) * Complex.I * θ) * u θ
            + Complex.exp ((↑(-(2 * (j : ℤ) + 1)) : ℂ) * Complex.I * θ) * u θ) := by
    funext θ
    rw [sqw_decomp, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hdecomp, fc_sum _ _ _ (by intro j _; fun_prop)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [fc_const_mul, fc_add _ _ _ (by fun_prop) (by fun_prop), fc_freq_shift, fc_freq_shift,
    show m - (-(2 * (j : ℤ) + 1)) = m + (2 * (j : ℤ) + 1) by ring]

/-! ### The coefficient-side limit -/

/-- The reflection `d ↦ m − d` as an equiv on `ℤ` (used to reindex the convolution sum). -/
def reflEquiv (m : ℤ) : ℤ ≃ ℤ :=
  ⟨fun d => m - d, fun d => m - d, fun d => by simp only [sub_sub_cancel],
    fun d => by simp only [sub_sub_cancel]⟩

@[simp] lemma reflEquiv_apply (m d : ℤ) : reflEquiv m d = m - d := rfl

/-- **Coefficient-side limit.**  The symmetric truncated convolution of `ς̂₁` with a sequence
`v ∈ ℓ²` converges to `convS₁ v m`.  (Even frequencies annihilate; the `±(2j+1)` pair is folded
by the `ℤ→ℕ` split `HasSum.nat_add_neg_add_one`, using `ς̂₁(−d) = ς̂₁(d)`.) -/
lemma tendsto_convS₁_partial (v : ℤ → ℂ) (hv : Summable fun n : ℤ => ‖v n‖ ^ 2) (m : ℤ) :
    Tendsto (fun J : ℕ => ∑ j ∈ Finset.range (J + 1),
        (sgnHat (2 * (j : ℤ) + 1) : ℂ)
          * (v (m - (2 * (j : ℤ) + 1)) + v (m + (2 * (j : ℤ) + 1))))
      atTop (𝓝 (convS₁ v m)) := by
  have h1 : convS₁ v m = ∑' d : ℤ, (sgnHat d : ℂ) * v (m - d) := by
    have hre := (reflEquiv m).tsum_eq (fun n : ℤ => (sgnHat (m - n) : ℂ) * v n)
    rw [convS₁, ← hre]
    exact tsum_congr (fun d => by simp only [reflEquiv_apply, sub_sub_cancel])
  have hKsum : Summable (fun d : ℤ => (sgnHat d : ℂ) * v (m - d)) := by
    have h := (summable_convS₁_term hv m).comp_injective (reflEquiv m).injective
    refine h.congr (fun d => ?_)
    simp only [Function.comp_apply, reflEquiv_apply, sub_sub_cancel]
  have hodd : convS₁ v m = ∑' n : ℤ, (sgnHat (2 * n + 1) : ℂ) * v (m - (2 * n + 1)) := by
    rw [h1, tsum_int_even_add_odd' hKsum]
    have hev : (∑' n : ℤ, (sgnHat (2 * n) : ℂ) * v (m - 2 * n)) = 0 := by
      simp only [sgnHat_two_mul, Complex.ofReal_zero, zero_mul, tsum_zero]
    rw [hev, zero_add]
  have hPsum : Summable (fun n : ℤ => (sgnHat (2 * n + 1) : ℂ) * v (m - (2 * n + 1))) := by
    exact hKsum.comp_injective (i := fun n : ℤ => 2 * n + 1)
      (by intro a b hab; simp only [] at hab; omega)
  have hP : HasSum (fun n : ℤ => (sgnHat (2 * n + 1) : ℂ) * v (m - (2 * n + 1))) (convS₁ v m) := by
    rw [hodd]; exact hPsum.hasSum
  have hpair := hP.nat_add_neg_add_one
  have htend := hpair.tendsto_sum_nat
  refine (htend.comp (tendsto_add_atTop_nat 1)).congr (fun J => ?_)
  simp only [Function.comp_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change (sgnHat (2 * (j : ℤ) + 1) : ℂ) * v (m - (2 * (j : ℤ) + 1))
      + (sgnHat (2 * (-((j : ℤ) + 1)) + 1) : ℂ) * v (m - (2 * (-((j : ℤ) + 1)) + 1))
      = (sgnHat (2 * (j : ℤ) + 1) : ℂ)
          * (v (m - (2 * (j : ℤ) + 1)) + v (m + (2 * (j : ℤ) + 1)))
  rw [show (2 * (-((j : ℤ) + 1)) + 1) = -(2 * (j : ℤ) + 1) from by ring, sgnHat_neg,
      show m - (-(2 * (j : ℤ) + 1)) = m + (2 * (j : ℤ) + 1) from by ring]
  ring

/-! ### Continuity and reflection symmetry of `sqw` -/

lemma continuous_sqw (J : ℕ) : Continuous (fun θ : ℝ => sqw J θ) := by
  unfold sqw; fun_prop

/-- `sqw J` is invariant under the reflection `θ ↦ 2π − θ` (periodicity + evenness of `cos`). -/
lemma sqw_two_pi_sub (J : ℕ) (θ : ℝ) : sqw J (2 * π - θ) = sqw J θ := by
  unfold sqw
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hc : (2 * (j : ℝ) + 1) * (2 * π - θ)
      = -((2 * (j : ℝ) + 1) * θ) + ((2 * (j : ℤ) + 1 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
  rw [hc, Real.cos_add_int_mul_two_pi, Real.cos_neg]

/-! ### The arc bound and arc pointwise limit -/

/-- The uniform bound extended to the two arcs of `Ioc 0 (2π)` where `cos θ ≥ δ`.  A point `θ`
with `cos θ ≥ δ` sits within `arccos δ < π/2` of a multiple of `2π`; on the near-`0` arc apply
`sqw_sub_one_bound` directly, on the near-`2π` arc reflect by `sqw_two_pi_sub`. -/
lemma sqw_sub_one_le_of_cos {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {C : ℝ}
    (hC : ∀ J : ℕ, |(∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1)) - π / 4| ≤ C)
    (J : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (2 * π)) (hcos : δ ≤ Real.cos θ) :
    |sqw J θ - 1| ≤ (4 / π) * (C + 2 / Real.sqrt δ) := by
  set θ₀ := Real.arccos δ with hθ₀def
  have hθ₀2 : θ₀ < π / 2 := Real.arccos_lt_pi_div_two.mpr hδ0
  have hcos₀ : Real.cos θ₀ = δ := Real.cos_arccos (by linarith) hδ1
  have hle : ∀ x : ℝ, 0 ≤ x → x ≤ π → δ ≤ Real.cos x → x ≤ θ₀ := by
    intro x hx0 hxπ hxcos
    have h1 : Real.arccos (Real.cos x) ≤ Real.arccos δ := Real.arccos_le_arccos hxcos
    rwa [Real.arccos_cos hx0 hxπ, ← hθ₀def] at h1
  rw [← hcos₀]
  rcases le_total θ π with hθπ | hθπ
  · have hθ0 : 0 ≤ θ := le_of_lt hθ.1
    exact sqw_sub_one_bound hC J hθ0 (hle θ hθ0 hθπ hcos) hθ₀2
  · set φ := 2 * π - θ with hφdef
    have hφ0 : 0 ≤ φ := by rw [hφdef]; linarith [hθ.2]
    have hφπ : φ ≤ π := by rw [hφdef]; linarith
    have hφcos : δ ≤ Real.cos φ := by rw [hφdef, Real.cos_two_pi_sub]; exact hcos
    have hsqw : sqw J θ = sqw J φ := by rw [hφdef, sqw_two_pi_sub]
    rw [hsqw]
    exact sqw_sub_one_bound hC J hφ0 (hle φ hφ0 hφπ hφcos) hθ₀2

/-- The pointwise limit `sqw J θ → 1` extended to the two arcs of `Ioc 0 (2π)`. -/
lemma tendsto_sqw_arc {δ : ℝ} (hδ0 : 0 < δ) {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (2 * π))
    (hcos : δ ≤ Real.cos θ) : Tendsto (fun J : ℕ => sqw J θ) atTop (𝓝 1) := by
  rcases le_total θ π with hθπ | hθπ
  · have hθ2 : θ < π / 2 := by
      have h1 : Real.arccos (Real.cos θ) ≤ Real.arccos δ := Real.arccos_le_arccos hcos
      rw [Real.arccos_cos (le_of_lt hθ.1) hθπ] at h1
      exact lt_of_le_of_lt h1 (Real.arccos_lt_pi_div_two.mpr hδ0)
    exact tendsto_sqw (by rw [abs_of_nonneg (le_of_lt hθ.1)]; exact hθ2)
  · set φ := 2 * π - θ with hφdef
    have hφ0 : 0 ≤ φ := by rw [hφdef]; linarith [hθ.2]
    have hφπ : φ ≤ π := by rw [hφdef]; linarith
    have hφcos : δ ≤ Real.cos φ := by rw [hφdef, Real.cos_two_pi_sub]; exact hcos
    have hφ2 : φ < π / 2 := by
      have h1 : Real.arccos (Real.cos φ) ≤ Real.arccos δ := Real.arccos_le_arccos hφcos
      rw [Real.arccos_cos hφ0 hφπ] at h1
      exact lt_of_le_of_lt h1 (Real.arccos_lt_pi_div_two.mpr hδ0)
    have hlim := tendsto_sqw (θ := φ) (by rw [abs_of_nonneg hφ0]; exact hφ2)
    refine hlim.congr (fun J => ?_)
    rw [hφdef]; exact sqw_two_pi_sub J θ

/-! ### The physical-side dominated convergence -/

/-- **Physical-side limit.**  For continuous `u` vanishing where `cos θ < δ`, the Fourier
coefficients of `sqw J · u` converge to those of `u` (dominated convergence on the window
`Ioc 0 (2π)`; away from `supp u` both integrands vanish, on `supp u` the partial sums converge pointwise with a common bound). -/
lemma tendsto_fc_sqw_mul (u : ℝ → ℂ) (hu : Continuous u) {δ : ℝ} (hδ0 : 0 < δ)
    (hsupp : ∀ θ : ℝ, Real.cos θ < δ → u θ = 0) (m : ℤ) :
    Tendsto (fun J : ℕ => fc (fun θ => (sqw J θ : ℂ) * u θ) m) atTop (𝓝 (fc u m)) := by
  set δ' := min δ 1 with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ0 one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hsupp' : ∀ θ : ℝ, Real.cos θ < δ' → u θ = 0 :=
    fun θ h => hsupp θ (lt_of_lt_of_le h (min_le_left _ _))
  obtain ⟨C, hC⟩ := exists_leibniz_bound
  set B := (4 / π) * (C + 2 / Real.sqrt δ') with hBdef
  set M := 1 + B with hMdef
  have hwnorm : ∀ θ : ℝ, ‖Complex.exp (-(m : ℂ) * Complex.I * (θ : ℂ))‖ = 1 := by
    intro θ
    rw [show -(m : ℂ) * Complex.I * (θ : ℂ) = ((-(m : ℝ) * θ : ℝ) : ℂ) * Complex.I from by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  set μ := volume.restrict (Set.Ioc (0 : ℝ) (2 * π)) with hμdef
  set F : ℕ → ℝ → ℂ :=
    fun J θ => (sqw J θ : ℂ) * u θ * Complex.exp (-(m : ℂ) * Complex.I * (θ : ℂ)) with hFdef
  set flim : ℝ → ℂ := fun θ => u θ * Complex.exp (-(m : ℂ) * Complex.I * (θ : ℂ)) with hflimdef
  set bound : ℝ → ℝ := fun θ => M * ‖u θ‖ with hbounddef
  have hFmeas : ∀ J, AEStronglyMeasurable (F J) μ := by
    intro J
    refine Continuous.aestronglyMeasurable ?_
    simp only [hFdef]
    exact ((Complex.continuous_ofReal.comp (continuous_sqw J)).mul hu).mul (by fun_prop)
  have hbint : Integrable bound μ := by
    rw [hbounddef, hμdef]
    exact (((continuous_const.mul hu.norm).continuousOn).integrableOn_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hdom : ∀ J, ∀ᵐ θ ∂μ, ‖F J θ‖ ≤ bound θ := by
    intro J
    rw [hμdef, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with θ hθ
    simp only [hFdef, hbounddef]
    by_cases hz : u θ = 0
    · simp [hz]
    · have hcos : δ' ≤ Real.cos θ := by
        by_contra h; exact hz (hsupp' θ (not_le.mp h))
      have hbnd : |sqw J θ - 1| ≤ B := by
        rw [hBdef]; exact sqw_sub_one_le_of_cos hδ'0 hδ'1 hC J hθ hcos
      have hsqwle : |sqw J θ| ≤ M := by
        rw [hMdef, abs_le]
        obtain ⟨h1, h2⟩ := abs_le.mp hbnd
        exact ⟨by linarith, by linarith⟩
      rw [norm_mul, norm_mul, hwnorm, mul_one]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hsqwle (norm_nonneg _)
  have hlim : ∀ᵐ θ ∂μ, Tendsto (fun J => F J θ) atTop (𝓝 (flim θ)) := by
    rw [hμdef, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with θ hθ
    simp only [hFdef, hflimdef]
    by_cases hz : u θ = 0
    · simp only [hz, mul_zero, zero_mul]; exact tendsto_const_nhds
    · have hcos : δ' ≤ Real.cos θ := by
        by_contra h; exact hz (hsupp' θ (not_le.mp h))
      have hs := tendsto_sqw_arc hδ'0 hθ hcos
      have hsC : Tendsto (fun J : ℕ => ((sqw J θ : ℝ) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 1).comp hs
      have hmul := (hsC.mul_const (u θ)).mul_const
        (Complex.exp (-(m : ℂ) * Complex.I * (θ : ℂ)))
      simpa using hmul
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence bound hFmeas hbint hdom hlim
  have hconv : (fun J : ℕ => fc (fun θ => (sqw J θ : ℂ) * u θ) m)
      = fun J => (2 * π : ℝ)⁻¹ * ∫ θ, F J θ ∂μ := by
    funext J
    rw [fc, hμdef, ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  have hlimEq : (2 * π : ℝ)⁻¹ * ∫ θ, flim θ ∂μ = fc u m := by
    rw [fc, hμdef, ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [hconv, ← hlimEq]
  exact hDCT.const_mul _

/-! ### The headline: `convS₁ (fc u) = fc u` -/

/-- For continuous `u : ℝ → ℂ` vanishing on a neighbourhood of `{cos ≤ 0}`
(`∃ δ > 0, cos θ < δ → u θ = 0`), the Fourier coefficients `fc u` satisfy the arc fixed-point
identity `convS₁ (fc u) = fc u` — i.e. `fc u` lies in the coefficient fixed-point set of `ς₁·`
(the `MemArc` clause 2).  `fc` is the WINDOWED coefficient functional (the `(2π)⁻¹∫₀^{2π}` of
`Parseval1`), so this is a statement about the coefficients on the window `Ioc 0 (2π)`, not about
`u` on all of `ℝ`; periodicity of `u` is not needed here (it enters only the separate `H^{1/2}`
weight-summability half of `MemArc`, supplied by the consumer). -/
theorem convS₁_fc_eq (u : ℝ → ℂ) (hu : Continuous u) {δ : ℝ} (hδ0 : 0 < δ)
    (hsupp : ∀ θ : ℝ, Real.cos θ < δ → u θ = 0) :
    convS₁ (fc u) = fc u := by
  funext m
  have hl2 : Summable fun n : ℤ => ‖fc u n‖ ^ 2 := (hasSum_sq_fc hu).summable
  have hcoeff := tendsto_convS₁_partial (fc u) hl2 m
  have hphys := tendsto_fc_sqw_mul u hu hδ0 hsupp m
  have hphys' : Tendsto (fun J : ℕ => ∑ j ∈ Finset.range (J + 1),
      (sgnHat (2 * (j : ℤ) + 1) : ℂ)
        * (fc u (m - (2 * (j : ℤ) + 1)) + fc u (m + (2 * (j : ℤ) + 1))))
      atTop (𝓝 (fc u m)) :=
    hphys.congr (fun J => fc_sqw_mul u hu J m)
  exact tendsto_nhds_unique hcoeff hphys'

end KsIndex.ArcBridge
