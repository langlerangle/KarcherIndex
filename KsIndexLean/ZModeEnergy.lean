module

/-
# Linear energy bound for the cutoff radial test

For `k ≥ 2` and fixed `c > 0`, `Qd_zModeCut_le` gives a real constant
`C = C(k, c)` such that `|Qd k (zModeCut k δ c)| ≤ C δ` for every
`0 < δ ≤ 1/2`. The constant is independent of `δ`; no uniform bound in
`c` is asserted.

On the disk, `zModeCut` agrees with the slit cutoff times `groundC k`.
The uncut radial function has zero quadratic-form value. The comparison
estimate `Qd_cut_collar` therefore bounds the cut function's form by a
collar contribution. On this collar the radial function vanishes linearly,
compensating for the cutoff derivative's `1/δ` growth, while the collar
has area at most `2πδ`. This proves the stated bound on the absolute form
value. The mixed-space negative-direction argument is a separate application.
-/
public import KsIndexLean.CollarBound
public import KsIndexLean.SlitCutoffGrad

@[expose] public section


noncomputable section

open Complex MeasureTheory Set Filter
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SingleDiskBridge KsIndex.Radial
  KsIndex.PunctureCutoff KsIndex.CutoffContinuity KsIndex.CollarBound
open scoped ContDiff

namespace KsIndex.SingleDisk

variable {k : ℕ}

/-- `zModeCut` is the cut ground state, as far as the disk form is concerned. -/
lemma Qd_zModeCut_eq (hk1 : 1 ≤ k) (δ c : ℝ) :
    Qd k (zModeCut k δ c) = Qd k (cutMul (cutSlit k δ c) (groundC k)) := by
  refine Qd_congr_disk fun w hw => ?_
  rw [zModeCut_eq_of_mem hw, Complex.ofReal_mul]
  rfl

/-- For `k ≥ 2` and fixed `c > 0`, the absolute disk form value is bounded
by `C δ`, uniformly for `0 < δ ≤ 1/2`. -/
theorem Qd_zModeCut_le (hk2 : 2 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → |Qd k (zModeCut k δ c)| ≤ C * δ := by
  have hk1 : 1 ≤ k := by omega
  have hκ : 0 < kap k := kap_pos hk2
  set n : ℝ := ((2 * k - 2 : ℕ) : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  -- global data for the ground state
  have hf : ∀ w ∈ disk, DifferentiableAt ℝ (groundC k) w := fun w _ =>
    ((contDiff_groundC k).differentiable (by simp)).differentiableAt
  have hMf : ∀ w ∈ disk, ‖groundC k w‖ ≤ kap k := fun w _ => abs_groundC_le hk2 w
  obtain ⟨Df, hDfcb⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (((contDiff_groundC k).continuous_fderiv (by simp)).continuousOn
      (s := Metric.closedBall (0 : ℂ) 1))
  have hDf : ∀ w ∈ disk, ‖fderiv ℝ (groundC k) w‖ ≤ Df := fun w hw =>
    hDfcb w (Metric.ball_subset_closedBall hw)
  have hDf0 : 0 ≤ Df := le_trans (norm_nonneg _)
    (hDfcb 0 (by simp [Metric.mem_closedBall]))
  -- the uniform bounds on m·G and m
  set P : ℝ := 16 * (kap k * n * Mψ) + 2 * (kap k * n * (k : ℝ) * Mψ) / c with hP
  have hP0 : 0 ≤ P := by
    have h1 : 0 ≤ kap k * n * Mψ := mul_nonneg (mul_nonneg hκ.le hn0) Mψ_nonneg
    have h2 : 0 ≤ kap k * n * (k : ℝ) * Mψ :=
      mul_nonneg (mul_nonneg (mul_nonneg hκ.le hn0) (Nat.cast_nonneg k)) Mψ_nonneg
    have h3 : 0 ≤ 2 * (kap k * n * (k : ℝ) * Mψ) / c := by positivity
    linarith
  set mbar : ℝ := kap k * n with hmbar
  have hmbar0 : 0 ≤ mbar := mul_nonneg hκ.le hn0
  -- the uniform bracket bound
  set Bbar : ℝ := 2 * (2 * (Df * (Df + P)) + P * (Df + P)
    + 8 * ((k : ℝ) - 1) ^ 2 * (mbar * kap k)) with hBbar
  refine ⟨Bbar * (2 * Real.pi), fun δ hδ hhalf => ?_⟩
  -- the collar and its data
  set S : Set ℂ := {w : ℂ | 1 - 2 * δ ≤ w.re ^ 2 + w.im ^ 2} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const
      (((Complex.continuous_re.pow 2).add (Complex.continuous_im.pow 2)).measurable)
  have hχd : ∀ w, DifferentiableAt ℝ (cutSlit k δ c) w := fun w =>
    ((contDiff_cutSlit k δ c).differentiable (by simp)).differentiableAt
  have hχ0 : ∀ w, 0 ≤ cutSlit k δ c w := fun w => (cutSlit_mem_Icc k δ c w).1
  have hχ1 : ∀ w, cutSlit k δ c w ≤ 1 := fun w => (cutSlit_mem_Icc k δ c w).2
  have hout : ∀ w ∈ disk, w ∉ S →
      cutSlit k δ c w = 1 ∧ fderiv ℝ (cutSlit k δ c) w = 0 := by
    intro w _ hwS
    exact cutSlit_off_collar hδ hc (not_le.mp hwS)
  set m : ℝ := kap k * n * (2 * δ) with hm
  have hm0 : 0 ≤ m := mul_nonneg (mul_nonneg hκ.le hn0) (by linarith)
  set G : ℝ := 8 * Mψ / δ + 2 * (k : ℝ) * Mψ / c with hG
  have hG0 : 0 ≤ G := by
    have h1 : 0 ≤ 8 * Mψ / δ := div_nonneg (mul_nonneg (by norm_num) Mψ_nonneg) hδ.le
    have h2 : 0 ≤ 2 * (k : ℝ) * Mψ / c :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) Mψ_nonneg) hc.le
    linarith
  have hmS : ∀ w ∈ disk ∩ S, ‖groundC k w‖ ≤ m := fun w ⟨hw, hwS⟩ =>
    groundC_collar_le hk2 (mem_disk_iff.mp hw) hwS
  have hGS : ∀ w ∈ disk ∩ S,
      |fderiv ℝ (cutSlit k δ c) w 1| + |fderiv ℝ (cutSlit k δ c) w I| ≤ G := fun w ⟨hw, _⟩ =>
    cutSlit_grad_bound hδ hc (mem_disk_iff.mp hw).le
  -- the collar bound
  have hcollar := Qd_cut_collar hk2 hS hχd hχ0 hχ1 hout hm0 hG0 hf hMf hDf hmS hGS
  -- the uniform bounds
  have hmG : m * G ≤ P := by
    have e1 : m * G = 16 * (kap k * n * Mψ)
        + 4 * (kap k * n * (k : ℝ) * Mψ) * (δ / c) := by
      rw [hm, hG]
      field_simp
      ring
    have h2 : δ / c ≤ (1 / 2) / c := by gcongr
    have h3 : 4 * (kap k * n * (k : ℝ) * Mψ) * (δ / c)
        ≤ 4 * (kap k * n * (k : ℝ) * Mψ) * ((1 / 2) / c) := by
      refine mul_le_mul_of_nonneg_left h2 ?_
      have : 0 ≤ kap k * n * (k : ℝ) * Mψ :=
        mul_nonneg (mul_nonneg (mul_nonneg hκ.le hn0) (Nat.cast_nonneg k)) Mψ_nonneg
      linarith
    have e2 : 4 * (kap k * n * (k : ℝ) * Mψ) * ((1 / 2) / c)
        = 2 * (kap k * n * (k : ℝ) * Mψ) / c := by ring
    rw [hP, e1]
    linarith [h3, e2 ▸ h3]
  have hmG0 : 0 ≤ m * G := mul_nonneg hm0 hG0
  have hmmbar : m ≤ mbar := by
    rw [hm, hmbar]
    have : 2 * δ ≤ 1 := by linarith
    nlinarith [mul_nonneg hκ.le hn0]
  -- the bracket is bounded by Bbar
  have hbrk : 2 * (2 * (Df * (Df + m * G)) + G * (m * (Df + m * G))
      + 8 * ((k : ℝ) - 1) ^ 2 * (m * kap k)) ≤ Bbar := by
    have c1 : Df * (Df + m * G) ≤ Df * (Df + P) :=
      mul_le_mul_of_nonneg_left (by linarith) hDf0
    have c2 : (m * G) * (Df + m * G) ≤ P * (Df + P) :=
      mul_le_mul hmG (by linarith) (by linarith) hP0
    have c3 : m * kap k ≤ mbar * kap k := mul_le_mul_of_nonneg_right hmmbar hκ.le
    have c3' : 8 * ((k : ℝ) - 1) ^ 2 * (m * kap k)
        ≤ 8 * ((k : ℝ) - 1) ^ 2 * (mbar * kap k) :=
      mul_le_mul_of_nonneg_left c3 (by positivity)
    have e : G * (m * (Df + m * G)) = (m * G) * (Df + m * G) := by ring
    rw [hBbar, e]
    linarith [c1, c2, c3']
  have hbrk0 : 0 ≤ 2 * (2 * (Df * (Df + m * G)) + G * (m * (Df + m * G))
      + 8 * ((k : ℝ) - 1) ^ 2 * (m * kap k)) := by
    have h1 : 0 ≤ Df * (Df + m * G) := mul_nonneg hDf0 (by linarith)
    have h2 : 0 ≤ G * (m * (Df + m * G)) :=
      mul_nonneg hG0 (mul_nonneg hm0 (by linarith))
    have h3 : 0 ≤ 8 * ((k : ℝ) - 1) ^ 2 * (m * kap k) := by
      have := mul_nonneg hm0 hκ.le
      positivity
    linarith
  -- volume
  have hvol := volume_real_collar_le hδ hhalf
  have hvol0 : 0 ≤ (volume : Measure ℂ).real (disk ∩ S) := by positivity
  -- assemble
  have hQg : Qd k (groundC k) = 0 := Qd_ground_zero hk2
  have hstart : |Qd k (zModeCut k δ c)|
      = |Qd k (cutMul (cutSlit k δ c) (groundC k)) - Qd k (groundC k)| := by
    rw [Qd_zModeCut_eq hk1, hQg, sub_zero]
  rw [hstart]
  calc |Qd k (cutMul (cutSlit k δ c) (groundC k)) - Qd k (groundC k)|
      ≤ 2 * (2 * (Df * (Df + m * G)) + G * (m * (Df + m * G))
          + 8 * ((k : ℝ) - 1) ^ 2 * (m * kap k))
        * (volume : Measure ℂ).real (disk ∩ S) := hcollar
    _ ≤ Bbar * (volume : Measure ℂ).real (disk ∩ S) :=
        mul_le_mul_of_nonneg_right hbrk hvol0
    _ ≤ Bbar * (2 * Real.pi * δ) := by
        refine mul_le_mul_of_nonneg_left hvol ?_
        linarith [hbrk, hbrk0]
    _ = Bbar * (2 * Real.pi) * δ := by ring

end KsIndex.SingleDisk
