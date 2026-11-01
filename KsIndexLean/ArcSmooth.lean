module

/-
# Regularity and cubic Fourier decay of the cut field

For each `η > 0`, `psiF η` is `C³` on the real line. The proof uses two open
regions: where `cos θ < η`, the field vanishes locally; where `cos θ > 0`, the
periodic representative differs from θ by a locally constant multiple of `2π`.
On the second region the field is locally a product of the square-root amplitude,
a half-angle phase, and a smooth cutoff.

Three applications of `fc_deriv` give
`‖fc (psiF η) ℓ‖ ≤ M / |ℓ|³` for nonzero frequencies. The constant is obtained
from a bound on the third derivative over one period and may depend on `η`.
Consequently both the coefficients and their `|ℓ|`-weighted norms are summable.
These estimates supply tail and gradient bounds for finite Fourier truncations
at a fixed cutoff parameter.
-/
public import KsIndexLean.ArcWitness

@[expose] public section


noncomputable section

open Real Set Filter
open KsIndex.ArcField KsIndex.Parseval

namespace KsIndex.ArcSmooth

/-! ### The phase is locally affine off the seam -/

/-- Off the seam (`cos θ₀ > 0` suffices), `per t − t` is locally constant: it is
`−toIocDiv·2π ∈ 2πℤ` and continuous, and two elements of `2πℤ` within `2π` coincide. -/
lemma per_eventually_affine {θ₀ : ℝ} (h : 0 < Real.cos θ₀) :
    ∀ᶠ t in nhds θ₀, per t = t + (per θ₀ - θ₀) := by
  have hπ := Real.pi_pos
  have hmod : ¬ θ₀ ≡ -π [PMOD (2 * π)] := by
    intro hmod
    obtain ⟨z, hz⟩ := AddCommGroup.modEq_iff_zsmul'.mp hmod
    rw [zsmul_eq_mul] at hz
    have hθ : θ₀ = -π + ((-z : ℤ) : ℝ) * (2 * π) := by push_cast; linarith
    rw [hθ, Real.cos_add_int_mul_two_pi, Real.cos_neg, Real.cos_pi] at h
    linarith
  have hper : ContinuousAt per θ₀ := continuousAt_toIocMod Real.two_pi_pos (-π) hmod
  have hcont : ContinuousAt (fun t => per t - t) θ₀ := hper.sub continuousAt_id
  have hev : ∀ᶠ t in nhds θ₀, dist (per t - t) (per θ₀ - θ₀) < 2 * π :=
    hcont (Metric.ball_mem_nhds _ Real.two_pi_pos)
  filter_upwards [hev] with t ht
  -- both differences are `−div·2π`
  have hdiv : ∀ s : ℝ, per s - s = -((toIocDiv Real.two_pi_pos (-π) s : ℤ) : ℝ) * (2 * π) := by
    intro s
    have := toIocMod_sub_self Real.two_pi_pos (-π) s
    rw [zsmul_eq_mul] at this
    calc per s - s = toIocMod Real.two_pi_pos (-π) s - s := rfl
      _ = -((toIocDiv Real.two_pi_pos (-π) s : ℤ) : ℝ) * (2 * π) := by
          rw [this]; push_cast; ring
  rw [Real.dist_eq, hdiv t, hdiv θ₀] at ht
  set dt : ℤ := toIocDiv Real.two_pi_pos (-π) t
  set d0 : ℤ := toIocDiv Real.two_pi_pos (-π) θ₀
  have habs : |((d0 : ℝ) - (dt : ℝ))| * (2 * π) < 2 * π := by
    have : -(dt : ℝ) * (2 * π) - -(d0 : ℝ) * (2 * π) = ((d0 : ℝ) - (dt : ℝ)) * (2 * π) := by
      ring
    rw [this, abs_mul, abs_of_pos Real.two_pi_pos] at ht
    exact ht
  have hlt1 : |((d0 : ℝ) - (dt : ℝ))| < 1 := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [Real.two_pi_pos]
  have heq : dt = d0 := by
    have h2 : |((d0 - dt : ℤ) : ℝ)| < 1 := by
      rwa [show ((d0 - dt : ℤ) : ℝ) = (d0 : ℝ) - (dt : ℝ) by push_cast; ring]
    have h3 : |d0 - dt| < 1 := by exact_mod_cast h2
    have h4 : d0 - dt = 0 := by
      rcases lt_trichotomy (d0 - dt) 0 with h' | h' | h'
      · rw [abs_of_neg h'] at h3; omega
      · exact h'
      · rw [abs_of_pos h'] at h3; omega
    omega
  have hteq : toIocDiv Real.two_pi_pos (-π) t = toIocDiv Real.two_pi_pos (-π) θ₀ := heq
  have h1 := hdiv t
  have h0 := hdiv θ₀
  rw [hteq] at h1
  linarith

/-! ### `C³` of the cut field by the two-chart cover -/

lemma contDiffAt_psiF (η : ℝ) (hη0 : 0 < η) (θ₀ : ℝ) :
    ContDiffAt ℝ 3 (psiF η) θ₀ := by
  rcases lt_or_ge (Real.cos θ₀) η with hlt | hge
  · -- locally zero
    have hnb : {t : ℝ | Real.cos t < η} ∈ nhds θ₀ :=
      (isOpen_lt Real.continuous_cos continuous_const).mem_nhds hlt
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0:ℂ))) ?_
    filter_upwards [hnb] with t ht
    exact psiF_eq_zero hη0 (le_of_lt ht)
  · -- the smooth chart
    have hpos : 0 < Real.cos θ₀ := lt_of_lt_of_le hη0 hge
    have haff := per_eventually_affine hpos
    have hcosnb : ∀ᶠ t in nhds θ₀, 0 < Real.cos t :=
      (isOpen_lt continuous_const Real.continuous_cos).mem_nhds hpos
    set c : ℝ := per θ₀ - θ₀ with hcdef
    -- the smooth model
    have hF : ContDiffAt ℝ 3 (fun t : ℝ =>
        ((Real.sqrt (Real.cos t) : ℝ) : ℂ)
          * Complex.exp (-Complex.I * ((t + c : ℝ) : ℂ) / 2)
          * ((wCol η t : ℝ) : ℂ)) θ₀ := by
      have hsqrt : ContDiffAt ℝ 3 (fun t : ℝ => Real.sqrt (Real.cos t)) θ₀ :=
        (Real.contDiffAt_sqrt hpos.ne').comp θ₀ Real.contDiff_cos.contDiffAt
      have hsqrtC : ContDiffAt ℝ 3 (fun t : ℝ => ((Real.sqrt (Real.cos t) : ℝ) : ℂ)) θ₀ :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp θ₀ hsqrt
      have harg : ContDiffAt ℝ 3 (fun t : ℝ => -Complex.I * ((t + c : ℝ) : ℂ) / 2) θ₀ := by
        have h1 : ContDiffAt ℝ 3 (fun t : ℝ => (((t + c : ℝ)) : ℂ)) θ₀ :=
          Complex.ofRealCLM.contDiff.contDiffAt.comp θ₀
            ((contDiff_id.add contDiff_const).contDiffAt)
        exact ((contDiffAt_const (c := -Complex.I)).mul h1).div_const 2
      have hexp : ContDiffAt ℝ 3
          (fun t : ℝ => Complex.exp (-Complex.I * ((t + c : ℝ) : ℂ) / 2)) θ₀ :=
        Complex.contDiff_exp.contDiffAt.comp θ₀ harg
      have hw : ContDiffAt ℝ 3 (fun t : ℝ => ((wCol η t : ℝ) : ℂ)) θ₀ := by
        refine Complex.ofRealCLM.contDiff.contDiffAt.comp θ₀ ?_
        exact (Real.smoothTransition.contDiff.comp
          ((Real.contDiff_cos.sub contDiff_const).div_const η)).contDiffAt
      exact (hsqrtC.mul hexp).mul hw
    refine hF.congr_of_eventuallyEq ?_
    filter_upwards [haff, hcosnb] with t haff_t hcos_t
    simp only [psiF, vF, hAmp_eq_sqrt hcos_t.le, haff_t]

theorem contDiff_psiF (η : ℝ) (hη0 : 0 < η) : ContDiff ℝ 3 (psiF η) :=
  contDiff_iff_contDiffAt.mpr (contDiffAt_psiF η hη0)

/-! ### Periodicity of derivatives, and a `fc` sup-bound -/

lemma periodic_deriv {f : ℝ → ℂ} (hf : Function.Periodic f (2 * π)) :
    Function.Periodic (deriv f) (2 * π) := by
  intro x
  have h1 : deriv (fun y : ℝ => f (y + 2 * π)) x = deriv f (x + 2 * π) :=
    deriv_comp_add_const f (2 * π) x
  have h2 : (fun y : ℝ => f (y + 2 * π)) = f := funext (fun y => hf y)
  rw [h2] at h1
  exact h1.symm

/-- `fc` is bounded by a sup-bound of the integrand. -/
lemma norm_fc_le {g : ℝ → ℂ} {C : ℝ} (_hC : 0 ≤ C)
    (hg : ∀ x ∈ Set.Icc (0:ℝ) (2 * π), ‖g x‖ ≤ C) (ℓ : ℤ) : ‖Parseval.fc g ℓ‖ ≤ C := by
  have hπ := Real.pi_pos
  simp only [Parseval.fc]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := C) (f := fun θ => g θ * Complex.exp (-(ℓ:ℂ) * Complex.I * θ))
    (fun x hx => by
      rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * π)] at hx
      have hexp1 : ‖Complex.exp (-(ℓ:ℂ) * Complex.I * x)‖ = 1 := by
        rw [show -(ℓ:ℂ) * Complex.I * x = ((-(ℓ:ℝ) * x : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      rw [norm_mul, hexp1, mul_one]
      exact hg x ⟨le_of_lt hx.1, hx.2⟩)
  calc (2 * π)⁻¹ * ‖∫ θ in (0:ℝ)..2 * π, g θ * Complex.exp (-(ℓ:ℂ) * Complex.I * θ)‖
      ≤ (2 * π)⁻¹ * (C * |2 * π - 0|) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C := by
        rw [sub_zero, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
        field_simp

/-! ### The cubic decay -/

/-- For each `η > 0`, the nonzero Fourier coefficients admit a cubic decay
bound with a nonnegative constant depending on the cut field. -/
theorem fc_psiF_decay (η : ℝ) (hη0 : 0 < η) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ℓ : ℤ, ℓ ≠ 0 →
      ‖Parseval.fc (psiF η) ℓ‖ ≤ M / |(ℓ : ℝ)| ^ 3 := by
  set u : ℝ → ℂ := psiF η with hudef
  have hu3 : ContDiff ℝ 3 u := contDiff_psiF η hη0
  have hu2 : ContDiff ℝ 2 (deriv u) := (contDiff_succ_iff_deriv.mp hu3).2.2
  have hu1 : ContDiff ℝ 1 (deriv (deriv u)) := (contDiff_succ_iff_deriv.mp hu2).2.2
  have hper0 : Function.Periodic u (2 * π) := psiF_periodic η
  have hper1 : Function.Periodic (deriv u) (2 * π) := periodic_deriv hper0
  have hper2 : Function.Periodic (deriv (deriv u)) (2 * π) := periodic_deriv hper1
  have hd0 : ∀ x, HasDerivAt u (deriv u x) x := fun x =>
    ((hu3.differentiable (by norm_num)) x).hasDerivAt
  have hd1 : ∀ x, HasDerivAt (deriv u) (deriv (deriv u) x) x := fun x =>
    ((hu2.differentiable (by norm_num)) x).hasDerivAt
  have hd2 : ∀ x, HasDerivAt (deriv (deriv u)) (deriv (deriv (deriv u)) x) x := fun x =>
    ((hu1.differentiable (by norm_num)) x).hasDerivAt
  have hc1 : Continuous (deriv u) := hu2.continuous
  have hc2 : Continuous (deriv (deriv u)) := hu1.continuous
  have hc3 : Continuous (deriv (deriv (deriv u))) := hu1.continuous_deriv le_rfl
  -- the three IBPs
  have hIBP1 := fun ℓ => fc_deriv hd0 hc1 hper0 ℓ
  have hIBP2 := fun ℓ => fc_deriv hd1 hc2 hper1 ℓ
  have hIBP3 := fun ℓ => fc_deriv hd2 hc3 hper2 ℓ
  -- the sup bound on the third derivative over one period
  obtain ⟨C, hCb⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hc3.continuousOn
  set M : ℝ := max C 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMb : ∀ x ∈ Set.Icc (0:ℝ) (2 * π), ‖deriv (deriv (deriv u)) x‖ ≤ M := fun x hx =>
    le_trans (hCb x hx) (le_max_left _ _)
  refine ⟨M, hM0, fun ℓ hℓ => ?_⟩
  have hfc3 : ‖Parseval.fc (deriv (deriv (deriv u))) ℓ‖ ≤ M := norm_fc_le hM0 hMb ℓ
  -- unfold the chain: fc u''' = (Iℓ)³ · fc u
  have hchain : Parseval.fc (deriv (deriv (deriv u))) ℓ
      = (Complex.I * (ℓ : ℂ)) ^ 3 * Parseval.fc u ℓ := by
    rw [hIBP3 ℓ, hIBP2 ℓ, hIBP1 ℓ]
    ring
  have hnorm : ‖(Complex.I * (ℓ : ℂ)) ^ 3‖ = |(ℓ : ℝ)| ^ 3 := by
    rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
  have hpos : (0:ℝ) < |(ℓ : ℝ)| ^ 3 := by
    have : (0:ℝ) < |(ℓ : ℝ)| := by
      rw [abs_pos]
      exact_mod_cast hℓ
    positivity
  rw [hchain, norm_mul, hnorm] at hfc3
  rw [le_div_iff₀ hpos, mul_comm]
  exact hfc3

/-! ### The ℓ¹-controls -/

/-- Generic comparison: nonneg `v` with `v ℓ ≤ M·|ℓ|^{−p}` off `0`, `p > 1`, is summable. -/
lemma summable_of_decay {v : ℤ → ℝ} (hv : ∀ ℓ, 0 ≤ v ℓ) (M p : ℝ) (hp : 1 < p)
    (h : ∀ ℓ : ℤ, ℓ ≠ 0 → v ℓ ≤ M * |(ℓ : ℝ)| ^ (-p)) : Summable v := by
  have hbase : Summable (fun ℓ : ℤ => M * |(ℓ : ℝ)| ^ (-p)) :=
    (Real.summable_abs_int_rpow hp).mul_left M
  have hpatch : Summable (fun ℓ : ℤ => if ℓ = 0 then (0:ℝ) else v ℓ) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) hbase
    · by_cases h0 : ℓ = 0
      · rw [if_pos h0]
      · rw [if_neg h0]; exact hv ℓ
    · by_cases h0 : ℓ = 0
      · subst h0
        rw [if_pos rfl]
        simp only [Int.cast_zero, abs_zero]
        rw [Real.zero_rpow (by linarith : -p ≠ 0), mul_zero]
      · rw [if_neg h0]; exact h ℓ h0
  have hsingle : Summable (fun ℓ : ℤ => if ℓ = 0 then v 0 else (0:ℝ)) := by
    apply summable_of_ne_finset_zero (s := ({0} : Finset ℤ))
    intro ℓ hℓ
    simp only [Finset.mem_singleton] at hℓ
    simp [hℓ]
  refine (hpatch.add hsingle).congr (fun ℓ => ?_)
  by_cases h0 : ℓ = 0 <;> simp [h0]

/-- The cut-field coefficients are `ℓ¹`. -/
theorem summable_fc_psiF (η : ℝ) (hη0 : 0 < η) :
    Summable (fun ℓ : ℤ => ‖Parseval.fc (psiF η) ℓ‖) := by
  obtain ⟨M, hM0, hM⟩ := fc_psiF_decay η hη0
  refine summable_of_decay (fun ℓ => norm_nonneg _) M 3 (by norm_num)
    (fun ℓ hℓ => ?_)
  have habs : (0:ℝ) < |(ℓ : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast hℓ
  refine le_trans (hM ℓ hℓ) (le_of_eq ?_)
  rw [Real.rpow_neg (abs_nonneg _), show ((3:ℝ)) = ((3:ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  rw [div_eq_mul_inv]

/-- At fixed `η > 0`, the `|ℓ|`-weighted coefficient norms are summable,
supplying a gradient bound uniform in Fourier truncation size. -/
theorem summable_abs_mul_fc_psiF (η : ℝ) (hη0 : 0 < η) :
    Summable (fun ℓ : ℤ => |(ℓ : ℝ)| * ‖Parseval.fc (psiF η) ℓ‖) := by
  obtain ⟨M, hM0, hM⟩ := fc_psiF_decay η hη0
  refine summable_of_decay (fun ℓ => by positivity) M 2 (by norm_num)
    (fun ℓ hℓ => ?_)
  have habs : (0:ℝ) < |(ℓ : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast hℓ
  calc |(ℓ : ℝ)| * ‖Parseval.fc (psiF η) ℓ‖
      ≤ |(ℓ : ℝ)| * (M / |(ℓ : ℝ)| ^ 3) :=
        mul_le_mul_of_nonneg_left (hM ℓ hℓ) (abs_nonneg _)
    _ = M * |(ℓ : ℝ)| ^ (-(2:ℝ)) := by
        rw [Real.rpow_neg (abs_nonneg _), show ((2:ℝ)) = ((2:ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
        field_simp

end KsIndex.ArcSmooth
