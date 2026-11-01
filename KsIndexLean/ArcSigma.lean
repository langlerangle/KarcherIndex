module

/-
# Square-wave convolution of the arc test coefficients

For every integer `m`, this file proves
`∑' n, chat (m - n) * c (2*n) = c (2*m + 1)` and its complex-valued
form `convS_arc`. The identity sends the even coefficient subsequence to
the odd subsequence under the square-wave convolution operator.

The proof writes `c` as a cosine integral and sums over
`W m N = Icc (m-N) (m+N+1)`. In this window the substitution `d = m-n`
is symmetric under `d ↦ -d-1`, so the sine terms cancel and the cosine
terms give the square-wave partial sum `T N`.

The resulting integrands converge pointwise on `(0, π/2]` and are
bounded by 6 for all sufficiently large `N`, uniformly on that interval.
Dominated convergence identifies the limit of their integrals. Separately,
absolute summability and exhaustion by the increasing windows identify
that same limit with the infinite convolution sum.
-/
public import KsIndexLean.CircleQ
public import KsIndexLean.SIsometry
public import KsIndexLean.TestField
public import KsIndexLean.SquareWave
public import KsIndexLean.ArcKernel

@[expose] public section


noncomputable section

namespace KsIndex.ArcSigma

open KsIndex.CircleQ KsIndex.TestField KsIndex.SquareWave Real Filter Topology MeasureTheory

/-! ### The square-wave partial sums `T_N`, `L_N = T_N(0)` -/

/-- `T_N(x) = (4/π) ∑_{k≤N} (−1)^k cos((2k+1)x)/(2k+1)`. -/
def T (N : ℕ) (x : ℝ) : ℝ :=
  4 / π * ∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.cos ((2 * (k : ℝ) + 1) * x) / (2 * (k : ℝ) + 1)

/-- `L_N = T_N(0) = (4/π) ∑_{k≤N} (−1)^k/(2k+1)`. -/
def L (N : ℕ) : ℝ := 4 / π * ∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1)

lemma T_continuous (N : ℕ) : Continuous (T N) := by
  unfold T
  exact continuous_const.mul (continuous_finset_sum _ fun k _ => by fun_prop)

/-- Square-wave partial-sum identity in `T`/`L` form: `T_N(x) = L_N − (2/π)(−1)^N ∫₀^x sin(2(N+1)t)/cos t` for `|x| < π/2`. -/
lemma T_eq (N : ℕ) {x : ℝ} (hx : |x| < π / 2) :
    T N x = L N - 2 / π * (-1 : ℝ) ^ N *
      ∫ t in (0 : ℝ)..x, Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t := by
  have h := square_wave_partial_sum N hx
  have hdiv : ∀ t : ℝ, Real.sin (2 * ((N : ℝ) + 1) * t) / (2 * Real.cos t)
      = (Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t) / 2 := fun t => by ring
  unfold T L
  rw [h]
  simp_rw [hdiv]
  rw [intervalIntegral.integral_div]
  ring

/-- `L_N → 1` (Leibniz: `∑ (−1)^k/(2k+1) → π/4`). -/
lemma L_tendsto : Tendsto L atTop (𝓝 1) := by
  have h := Real.tendsto_sum_pi_div_four
  have h2 : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N + 1), (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1))
      atTop (𝓝 (π / 4)) := h.comp (tendsto_add_atTop_nat 1)
  have h3 := h2.const_mul (4 / π)
  have hval : 4 / π * (π / 4) = (1 : ℝ) := by field_simp
  rw [hval] at h3
  exact h3

/-- Eventually `|L_N| ≤ 3` (a convergent sequence is eventually bounded). -/
lemma L_bounded : ∀ᶠ N in atTop, |L N| ≤ 3 := by
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp L_tendsto 1 one_pos
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have h := hN₀ N hN
  rw [Real.dist_eq] at h
  have := abs_sub_abs_le_abs_sub (L N) 1
  rw [abs_one] at this
  linarith

/-! ### The kernel identity (finite trigonometric sum) -/

/-- The window `W m N = Icc (m−N) (m+N+1)`: `d = m − n` ranges over `Icc (−N−1) N`,
which is `(d ↦ −d−1)`-symmetric. -/
def W (m : ℤ) (N : ℕ) : Finset ℤ := Finset.Icc (m - (N : ℤ)) (m + (N : ℤ) + 1)

/-- **Kernel identity** (finite trigonometric sum):
`∑_{n ∈ W m N} chat(m−n) cos((2n+½)x) = cos((2m+3/2)x) · T_N(x)`.
Proof: reindex `n = m − d`, `d ∈ Icc (−N−1) N`; `cos((2(m−d)+½)x) = cos(Ax − Bx)`
with `A = 2m+3/2`, `B = 2d+1`, expand; the `sin(Bx)`-sum vanishes by the involution
`d ↦ −d−1` (`chat(−d−1) = chat d`, `sin` odd); the `cos(Bx)`-sum pairs `d ↔ −d−1` into
`2∑_{k=0}^{N} chat k cos((2k+1)x) = T_N(x)`. -/
theorem kernel_total (m : ℤ) (N : ℕ) (x : ℝ) :
    ∑ n ∈ W m N, chat (m - n) * Real.cos ((2 * (n : ℝ) + 1 / 2) * x)
      = Real.cos ((2 * (m : ℝ) + 3 / 2) * x) * T N x := by
  have h := KsIndex.ArcKernel.kernel_total m N x
  unfold KsIndex.ArcKernel.chat' at h
  unfold W T chat
  exact h

/-! ### `c` as an integral, and the windowed partial sums -/

/-- `c ℓ = (1/π) ∫₀^{π/2} √cos x · cos((ℓ+½)x) dx`. -/
lemma c_eq_integral (ℓ : ℤ) :
    c ℓ = (1 / π) * ∫ x in (0 : ℝ)..(π / 2),
      Real.sqrt (Real.cos x) * Real.cos (((ℓ : ℝ) + 1 / 2) * x) := by
  unfold c g
  ring

/-- `F_N(x) = √cos x · cos((2m+3/2)x) · T_N(x)`, and its limit `f₀(x) = √cos x · cos((2m+3/2)x)`. -/
def F (m : ℤ) (N : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (Real.cos x) * Real.cos ((2 * (m : ℝ) + 3 / 2) * x) * T N x

def f₀ (m : ℤ) (x : ℝ) : ℝ := Real.sqrt (Real.cos x) * Real.cos ((2 * (m : ℝ) + 3 / 2) * x)

lemma F_continuous (m : ℤ) (N : ℕ) : Continuous (F m N) := by
  unfold F
  exact ((Real.continuous_sqrt.comp Real.continuous_cos).mul (by fun_prop)).mul (T_continuous N)

/-- The windowed partial sum is `(1/π) ∫₀^{π/2} F_N`. -/
lemma partial_sum_eq (m : ℤ) (N : ℕ) :
    ∑ n ∈ W m N, chat (m - n) * c (2 * n) = (1 / π) * ∫ x in (0 : ℝ)..(π / 2), F m N x := by
  have hterm : ∀ n ∈ W m N, chat (m - n) * c (2 * n)
      = ∫ x in (0 : ℝ)..(π / 2),
          (1 / π) * (Real.sqrt (Real.cos x)
            * (chat (m - n) * Real.cos ((2 * (n : ℝ) + 1 / 2) * x))) := by
    intro n _
    rw [c_eq_integral, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    push_cast
    ring
  have hint : ∀ n ∈ W m N, IntervalIntegrable (fun x : ℝ =>
      (1 / π) * (Real.sqrt (Real.cos x) * (chat (m - n) * Real.cos ((2 * (n : ℝ) + 1 / 2) * x))))
      volume 0 (π / 2) := by
    intro n _
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((Real.continuous_sqrt.comp Real.continuous_cos).mul (by fun_prop))
  rw [Finset.sum_congr rfl hterm, ← intervalIntegral.integral_finsetSum hint,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [F]
  rw [← Finset.mul_sum, ← Finset.mul_sum, kernel_total]
  ring

/-! ### Domination and pointwise convergence -/

/-- `|∫₀^x sin(Mt)/cos t| ≤ ∫₀^x 1/cos t` for `0 ≤ x < π/2`. -/
lemma abs_integral_sin_div_cos_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x < π / 2) (M : ℝ) :
    |∫ t in (0 : ℝ)..x, Real.sin (M * t) / Real.cos t| ≤ ∫ t in (0 : ℝ)..x, 1 / Real.cos t := by
  have hcos : ∀ t ∈ Set.Icc (0 : ℝ) x, 0 < Real.cos t := fun t ht =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hI1 : IntervalIntegrable (fun t => |Real.sin (M * t) / Real.cos t|) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx0]
    exact (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hcos t ht).ne')).abs
  have hI2 : IntervalIntegrable (fun t => 1 / Real.cos t) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx0]
    exact ContinuousOn.div continuousOn_const (by fun_prop) (fun t ht => (hcos t ht).ne')
  calc |∫ t in (0 : ℝ)..x, Real.sin (M * t) / Real.cos t|
      ≤ ∫ t in (0 : ℝ)..x, |Real.sin (M * t) / Real.cos t| :=
        intervalIntegral.abs_integral_le_integral_abs hx0
    _ ≤ ∫ t in (0 : ℝ)..x, 1 / Real.cos t := by
        refine intervalIntegral.integral_mono_on hx0 hI1 hI2 fun t ht => ?_
        rw [abs_div, abs_of_pos (hcos t ht)]
        exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (hcos t ht).le

/-- Eventually in `N`, `|F_N(x)| ≤ 6` on `(0, π/2]`. -/
lemma F_bound (m : ℤ) : ∀ᶠ N in atTop, ∀ x ∈ Set.Ioc (0 : ℝ) (π / 2), |F m N x| ≤ 6 := by
  filter_upwards [L_bounded] with N hL
  intro x hx
  rcases eq_or_lt_of_le hx.2 with hxe | hxlt
  · simp [F, hxe, Real.cos_pi_div_two]
  · have hx0 : 0 ≤ x := hx.1.le
    have habs : |x| < π / 2 := by rw [abs_of_nonneg hx0]; exact hxlt
    set I : ℝ := ∫ t in (0 : ℝ)..x, Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t with hI
    have hT : T N x = L N - 2 / π * (-1 : ℝ) ^ N * I := T_eq N habs
    have hIle : |I| ≤ ∫ t in (0 : ℝ)..x, 1 / Real.cos t :=
      abs_integral_sin_div_cos_le hx0 hxlt (2 * ((N : ℝ) + 1))
    have hC : Real.sqrt (Real.cos x) * (∫ t in (0 : ℝ)..x, 1 / Real.cos t) ≤ 4 :=
      sqrt_cos_mul_integral_inv_cos_le hx0 hxlt
    have hsq : 0 ≤ Real.sqrt (Real.cos x) := Real.sqrt_nonneg _
    have hsq1 : Real.sqrt (Real.cos x) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact Real.cos_le_one x
    have hcosb : |Real.cos ((2 * (m : ℝ) + 3 / 2) * x)| ≤ 1 := Real.abs_cos_le_one _
    have hπ : 2 / π ≤ 2 / 3 := by
      have := Real.pi_gt_three
      rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
      linarith
    have hπ0 : (0 : ℝ) ≤ 2 / π := by positivity
    have hT' : |T N x| ≤ |L N| + 2 / π * |I| := by
      rw [hT]
      calc |L N - 2 / π * (-1 : ℝ) ^ N * I| ≤ |L N| + |2 / π * (-1 : ℝ) ^ N * I| := abs_sub _ _
        _ = |L N| + 2 / π * |I| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hπ0, abs_pow, abs_neg, abs_one, one_pow, mul_one]
    have hsqI : Real.sqrt (Real.cos x) * |I| ≤ 4 :=
      le_trans (mul_le_mul_of_nonneg_left hIle hsq) hC
    unfold F
    rw [abs_mul, abs_mul, abs_of_nonneg hsq]
    calc Real.sqrt (Real.cos x) * |Real.cos ((2 * (m : ℝ) + 3 / 2) * x)| * |T N x|
        ≤ Real.sqrt (Real.cos x) * 1 * (|L N| + 2 / π * |I|) := by gcongr
      _ = Real.sqrt (Real.cos x) * |L N| + 2 / π * (Real.sqrt (Real.cos x) * |I|) := by ring
      _ ≤ 1 * 3 + 2 / 3 * 4 := by gcongr
      _ ≤ 6 := by norm_num

/-- Pointwise: `F_N(x) → f₀(x)` on `(0, π/2]`. -/
lemma F_tendsto (m : ℤ) {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) (π / 2)) :
    Tendsto (fun N => F m N x) atTop (𝓝 (f₀ m x)) := by
  rcases eq_or_lt_of_le hx.2 with hxe | hxlt
  · simp [F, f₀, hxe, Real.cos_pi_div_two]
  · have hx0 : 0 ≤ x := hx.1.le
    have habs : |x| < π / 2 := by rw [abs_of_nonneg hx0]; exact hxlt
    have hTeq : ∀ N : ℕ, F m N x = f₀ m x * (L N - 2 / π * (-1 : ℝ) ^ N *
        ∫ t in (0 : ℝ)..x, Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t) := fun N => by
      rw [F, f₀, T_eq N habs]
    simp_rw [hTeq]
    have hI : Tendsto
        (fun N : ℕ => ∫ t in (0 : ℝ)..x, Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t)
        atTop (𝓝 0) := by
      have h := tendsto_integral_sin_mul_div_cos hx0 hxlt
      have hsub : Tendsto (fun N : ℕ => 2 * N + 2) atTop atTop :=
        tendsto_atTop_atTop.mpr fun b => ⟨b, fun N hN => by omega⟩
      refine (h.comp hsub).congr fun N => ?_
      simp only [Function.comp]
      congr 1
      funext t
      push_cast
      ring_nf
    have hsign : Tendsto (fun N : ℕ => 2 / π * (-1 : ℝ) ^ N *
        ∫ t in (0 : ℝ)..x, Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t) atTop (𝓝 0) := by
      have hπ : 2 / π ≤ 1 := by
        rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
      have hbd : ∀ N : ℕ, ‖2 / π * (-1 : ℝ) ^ N *
          ∫ t in (0 : ℝ)..x, Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t‖
          ≤ ‖∫ t in (0 : ℝ)..x, Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t‖ := by
        intro N
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
          one_pow, mul_one, abs_of_pos (by positivity : (0 : ℝ) < 2 / π)]
        exact mul_le_of_le_one_left (abs_nonneg _) hπ
      exact squeeze_zero_norm hbd (by simpa using hI.norm)
    have := (L_tendsto.sub hsign).const_mul (f₀ m x)
    simpa using this

/-- Dominated convergence: `∫₀^{π/2} F_N → ∫₀^{π/2} f₀`. -/
lemma integral_F_tendsto (m : ℤ) :
    Tendsto (fun N => ∫ x in (0 : ℝ)..(π / 2), F m N x) atTop
      (𝓝 (∫ x in (0 : ℝ)..(π / 2), f₀ m x)) := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (6 : ℝ))
    ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun N => (F_continuous m N).aestronglyMeasurable
  · filter_upwards [F_bound m] with N hN
    refine ae_of_all _ fun x hx => ?_
    rw [Set.uIoc_of_le hle] at hx
    rw [Real.norm_eq_abs]
    exact hN x hx
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun x hx => ?_
    rw [Set.uIoc_of_le hle] at hx
    exact F_tendsto m hx

/-- The windowed partial sums converge to `c(2m+1)`. -/
lemma partial_sum_tendsto (m : ℤ) :
    Tendsto (fun N => ∑ n ∈ W m N, chat (m - n) * c (2 * n)) atTop (𝓝 (c (2 * m + 1))) := by
  simp_rw [partial_sum_eq]
  have h := (integral_F_tendsto m).const_mul (1 / π)
  have hval : (1 / π) * ∫ x in (0 : ℝ)..(π / 2), f₀ m x = c (2 * m + 1) := by
    rw [c_eq_integral]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    simp only [f₀]
    push_cast
    ring_nf
  rw [hval] at h
  exact h

/-! ### Absolute convergence and the exhaustion -/

lemma habs_ge_third (ℓ : ℤ) : (1 : ℝ) / 3 ≤ |(ℓ : ℝ) + 1 / 3| := by
  rcases le_or_gt 0 ℓ with h | h
  · have hn : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith
  · have hle : ℓ ≤ -1 := by omega
    have hn : (ℓ : ℝ) ≤ -1 := by exact_mod_cast hle
    rw [abs_of_neg (by linarith)]; linarith

lemma two_mul_injective : Function.Injective (fun n : ℤ => 2 * n) := fun a b h => by
  simp only at h; omega

/-- `n ↦ chat(m−n)·c(2n)` is absolutely summable (`|ab| ≤ (a²+b²)/2`, both squares summable). -/
lemma summable_term (m : ℤ) : Summable (fun n : ℤ => chat (m - n) * c (2 * n)) := by
  have ha : Summable (fun n : ℤ => chat (m - n) ^ 2) :=
    KsIndex.SIsometry.summable_chat_sq.comp_injective (fun a b h => by omega)
  have hb : Summable (fun n : ℤ => c (2 * n) ^ 2) := by
    have h := ((summable_abs_mul_sq (show (1 / 3 : ℝ) ∈ Set.Ioo 0 1 by norm_num)).mul_left 3)
      |>.comp_injective two_mul_injective
    refine h.of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_
    simp only [Function.comp]
    push_cast
    have h13 := habs_ge_third (2 * n)
    push_cast at h13
    nlinarith [sq_nonneg (c (2 * n))]
  refine Summable.of_norm_bounded ((ha.add hb).mul_left (1 / 2)) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|chat (m - n)| - |c (2 * n)|), sq_abs (chat (m - n)), sq_abs (c (2 * n)),
    abs_nonneg (chat (m - n)), abs_nonneg (c (2 * n))]

lemma W_mono (m : ℤ) : Monotone (W m) := by
  intro a b hab
  simp only [W]
  apply Finset.Icc_subset_Icc <;> omega

lemma W_cover (m : ℤ) (n : ℤ) : ∃ N : ℕ, n ∈ W m N := by
  refine ⟨(n - m).toNat + (m - n).toNat, ?_⟩
  simp only [W, Finset.mem_Icc]
  omega

/-- **Real convolution identity**: `∑' n, chat(m−n)·c(2n) = c(2m+1)`. -/
theorem tsum_chat_mul_c (m : ℤ) : ∑' n : ℤ, chat (m - n) * c (2 * n) = c (2 * m + 1) := by
  have hs := (summable_term m).hasSum
  have hW : Tendsto (W m) atTop atTop := tendsto_atTop_finset_of_monotone (W_mono m) (W_cover m)
  have h1 : Tendsto (fun N => ∑ n ∈ W m N, chat (m - n) * c (2 * n)) atTop
      (𝓝 (∑' n : ℤ, chat (m - n) * c (2 * n))) := hs.comp hW
  exact tendsto_nhds_unique h1 (partial_sum_tendsto m)

/-- **Complex convolution identity**: `convS (fun n => c(2n)) m = c(2m+1)`. -/
theorem convS_arc (m : ℤ) :
    convS (fun n : ℤ => (c (2 * n) : ℂ)) m = (c (2 * m + 1) : ℂ) := by
  unfold convS
  have hfun : (fun n : ℤ => (chat (m - n) : ℂ) * (c (2 * n) : ℂ))
      = fun n : ℤ => ((chat (m - n) * c (2 * n) : ℝ) : ℂ) := by
    funext n; push_cast; ring
  rw [hfun, ← Complex.ofReal_tsum, tsum_chat_mul_c]

end KsIndex.ArcSigma
