module

/-
# The class-zero mixed seam index

The quadratic expansion
`Qd(f + t·g) = Qd f + 2t · Re Bd(f,g) + t² · Qd g`
holds for `DiskNice` fields, real `t`, and `k ≥ 2`. A collar estimate then
controls the cross pairing of a cut ground state with a fixed trace partner
by an error of order `δ`.

For `k ≥ 3` and `0 < c ≤ 1/2`, the partner with fixed scale `δ₀ = 1/2` has
strictly negative ground-state cross pairing. The cut ground state's energy
tends to zero, so `exists_neg_dip` supplies a real positive coefficient and
a sufficiently small cutoff scale producing a negative direction in
`NatCc k true false ⊓ Erot1 k 0`. This proves the lower bound one.
Combining it with the trace-coefficient upper bound gives
`seamNat k true false 0 = 1`.
-/
public import KsIndexLean.CrossTerm
public import KsIndexLean.SeamLowerCount
public import KsIndexLean.ZModeEnergy
public import KsIndexLean.SeamNat

@[expose] public section


noncomputable section

open Complex MeasureTheory Set
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.Radial KsIndex.ModeDiag KsIndex.SingleDiskBridge
  KsIndex.FormIndex KsIndex.CutoffContinuity KsIndex.PunctureCutoff KsIndex.CollarBound
open scoped ContDiff

namespace KsIndex.SingleDisk

variable {k : ℕ}

/-- **The quadratic expansion of the Jacobi form along a real direction.**  For `DiskNice` `f, g`
and real `t`,
  `Qd(f + t·g) = Qd f + 2t · Re Bd(f,g) + t² · Qd g`. -/
lemma Qd_add_smul (hk : 2 ≤ k) {f g : ℂ → ℂ} (hf : DiskNice f) (hg : DiskNice g) (t : ℝ) :
    Qd k (fun w => f w + (t : ℂ) • g w)
      = Qd k f + 2 * t * (Bd k f g).re + t ^ 2 * Qd k g := by
  set u : Fin 2 → ℂ → ℂ := ![f, g] with hu
  set a : Fin 2 → ℂ := ![1, (t : ℂ)] with ha
  have hnice : ∀ i, DiskNice (u i) := by
    intro i; fin_cases i
    · simpa [hu] using hf
    · simpa [hu] using hg
  have hcongr : Qd k (fun w => f w + (t : ℂ) • g w) = Qd k (fun w => ∑ i, a i • u i w) := by
    congr 1
    funext w
    simp [ha, hu, Fin.sum_univ_two]
  rw [hcongr]
  have hB := Bd_finsum hk a a hnice
  rw [Bd_self_eq_Qd hk] at hB
  have hfg : Bd k f g + Bd k g f = 2 * ((Bd k f g).re : ℂ) := by
    rw [← Bd_conj_symm f g, Complex.add_conj]; norm_cast
  have hgoal : (Qd k (fun w => ∑ i, a i • u i w) : ℂ)
      = ((Qd k f + 2 * t * (Bd k f g).re + t ^ 2 * Qd k g : ℝ) : ℂ) := by
    rw [hB]
    simp only [Fin.sum_univ_two, ha, hu, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_one, one_mul, mul_one, Complex.conj_ofReal, Bd_self_eq_Qd hk]
    push_cast
    linear_combination (t : ℂ) * hfg
  exact_mod_cast hgoal

/-! ### The collar cross-bound -/

/-- The cut ground state, as a globally smooth function (`= zModeCut` on the disk). -/
lemma contDiff_cutMul_groundC (k : ℕ) (δ c : ℝ) :
    ContDiff ℝ ∞ (cutMul (cutSlit k δ c) (groundC k)) := by
  have h : cutMul (cutSlit k δ c) (groundC k)
      = fun w => ((cutSlit k δ c w * groundR k w : ℝ) : ℂ) := by
    funext w; simp only [cutMul, groundC]; push_cast; ring
  rw [h]; exact contDiff_zModeF k δ c

/-- `‖cutSlitC‖ ≤ 1` on all of `ℂ`. -/
lemma norm_cutSlitC_le_one (k : ℕ) (δ c : ℝ) (w : ℂ) : ‖cutSlitC k δ c w‖ ≤ 1 := by
  rw [cutSlitC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutSlit_mem_Icc k δ c w).1]
  exact (cutSlit_mem_Icc k δ c w).2

/-- **The collar cross-bound** for `k ≥ 2`, `c > 0`, fixed real `δ₀` and `0 < δ ≤ 1/2`.  `‖Bd(cutMul χ_δ f₀, cutSlitC δ₀) − Bd(f₀,
cutSlitC δ₀)‖ ≤ C·δ`: the cut ground state's cross pairing against the fixed trace partner converges
to `Bd(f₀, cutSlitC δ₀)` at rate `O(δ)` (the collar-localized continuity `Bd_cutLeft_collar`, with
`m ∼ δ`, `G ∼ 1/δ`, `vol(collar) ≤ 2πδ`). -/
theorem bd_cross_bound (hk2 : 2 ≤ k) {c : ℝ} (hc : 0 < c) (δ₀ : ℝ) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ‖Bd k (cutMul (cutSlit k δ c) (groundC k)) (cutSlitC k δ₀ c)
          - Bd k (groundC k) (cutSlitC k δ₀ c)‖ ≤ C * δ := by
  have hκ : 0 < kap k := kap_pos hk2
  set n : ℝ := ((2 * k - 2 : ℕ) : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set g : ℂ → ℂ := cutSlitC k δ₀ c with hgdef
  -- global data for the ground state `f₀`
  have hf : ∀ w ∈ disk, DifferentiableAt ℝ (groundC k) w := fun w _ =>
    ((contDiff_groundC k).differentiable (by simp)).differentiableAt
  have hMf : ∀ w ∈ disk, ‖groundC k w‖ ≤ kap k := fun w _ => abs_groundC_le hk2 w
  obtain ⟨Df, hDfcb⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (((contDiff_groundC k).continuous_fderiv (by simp)).continuousOn
      (s := Metric.closedBall (0 : ℂ) 1))
  have hDf : ∀ w ∈ disk, ‖fderiv ℝ (groundC k) w‖ ≤ Df := fun w hw =>
    hDfcb w (Metric.ball_subset_closedBall hw)
  have hDf0 : 0 ≤ Df := le_trans (norm_nonneg _) (hDfcb 0 (by simp [Metric.mem_closedBall]))
  -- global data for the fixed trace partner `g`
  have hg : ∀ w ∈ disk, DifferentiableAt ℝ g w := fun w _ =>
    ((contDiff_cutSlitC k δ₀ c).differentiable (by simp)).differentiableAt
  have hMg : ∀ w ∈ disk, ‖g w‖ ≤ 1 := fun w _ => norm_cutSlitC_le_one k δ₀ c w
  obtain ⟨Dg, hDgcb⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (((contDiff_cutSlitC k δ₀ c).continuous_fderiv (by simp)).continuousOn
      (s := Metric.closedBall (0 : ℂ) 1))
  have hDg : ∀ w ∈ disk, ‖fderiv ℝ g w‖ ≤ Dg := fun w hw =>
    hDgcb w (Metric.ball_subset_closedBall hw)
  have hDg0 : 0 ≤ Dg := le_trans (norm_nonneg _) (hDgcb 0 (by simp [Metric.mem_closedBall]))
  -- the uniform bounds
  set P : ℝ := 16 * (kap k * n * Mψ) + 2 * (kap k * n * (k : ℝ) * Mψ) / c with hP
  have hP0 : 0 ≤ P := by
    have h1 : 0 ≤ kap k * n * Mψ := mul_nonneg (mul_nonneg hκ.le hn0) Mψ_nonneg
    have h3 : 0 ≤ 2 * (kap k * n * (k : ℝ) * Mψ) / c := by
      apply div_nonneg _ hc.le
      have := mul_nonneg (mul_nonneg (mul_nonneg hκ.le hn0) (Nat.cast_nonneg k)) Mψ_nonneg
      linarith
    linarith
  set Bbar : ℝ := 2 * (Df * Dg) + P * Dg + 8 * ((k : ℝ) - 1) ^ 2 * (kap k * n) with hBbar
  have hBbar0 : 0 ≤ Bbar := by
    have t1 : 0 ≤ 2 * (Df * Dg) := by have := mul_nonneg hDf0 hDg0; linarith
    have t2 : 0 ≤ P * Dg := mul_nonneg hP0 hDg0
    have t3 : 0 ≤ 8 * ((k : ℝ) - 1) ^ 2 * (kap k * n) :=
      mul_nonneg (by positivity) (mul_nonneg hκ.le hn0)
    linarith
  refine ⟨Bbar * (2 * Real.pi), fun δ hδ hhalf => ?_⟩
  set S : Set ℂ := {w : ℂ | 1 - 2 * δ ≤ w.re ^ 2 + w.im ^ 2} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const
      (((Complex.continuous_re.pow 2).add (Complex.continuous_im.pow 2)).measurable)
  have hχd : ∀ w, DifferentiableAt ℝ (cutSlit k δ c) w := fun w =>
    ((contDiff_cutSlit k δ c).differentiable (by simp)).differentiableAt
  have hχ0 : ∀ w, 0 ≤ cutSlit k δ c w := fun w => (cutSlit_mem_Icc k δ c w).1
  have hχ1 : ∀ w, cutSlit k δ c w ≤ 1 := fun w => (cutSlit_mem_Icc k δ c w).2
  have hout : ∀ w ∈ disk, w ∉ S → cutSlit k δ c w = 1 ∧ fderiv ℝ (cutSlit k δ c) w = 0 := by
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
  have hcollar := Bd_cutLeft_collar hk2 hS hχd hχ0 hχ1 hout hm0 hG0 hf hMf hDf hg hMg hDg hmS hGS
  -- the uniform bounds on the bracket
  have hmG : m * G ≤ P := by
    have e1 : m * G = 16 * (kap k * n * Mψ)
        + 4 * (kap k * n * (k : ℝ) * Mψ) * (δ / c) := by
      rw [hm, hG]; field_simp; ring
    have h2 : δ / c ≤ (1 / 2) / c := by gcongr
    have h3 : 4 * (kap k * n * (k : ℝ) * Mψ) * (δ / c)
        ≤ 4 * (kap k * n * (k : ℝ) * Mψ) * ((1 / 2) / c) := by
      refine mul_le_mul_of_nonneg_left h2 ?_
      have : 0 ≤ kap k * n * (k : ℝ) * Mψ :=
        mul_nonneg (mul_nonneg (mul_nonneg hκ.le hn0) (Nat.cast_nonneg k)) Mψ_nonneg
      linarith
    have e2 : 4 * (kap k * n * (k : ℝ) * Mψ) * ((1 / 2) / c)
        = 2 * (kap k * n * (k : ℝ) * Mψ) / c := by ring
    rw [hP, e1]; linarith [e2 ▸ h3]
  have hmmbar : m ≤ kap k * n := by
    rw [hm]; nlinarith [mul_nonneg hκ.le hn0]
  have hbrk : 2 * (Df * Dg) + G * (m * Dg) + 8 * ((k : ℝ) - 1) ^ 2 * (m * 1) ≤ Bbar := by
    have c1 : G * (m * Dg) ≤ P * Dg := by
      rw [show G * (m * Dg) = (m * G) * Dg by ring]
      exact mul_le_mul_of_nonneg_right hmG hDg0
    have c2 : 8 * ((k : ℝ) - 1) ^ 2 * (m * 1) ≤ 8 * ((k : ℝ) - 1) ^ 2 * (kap k * n) := by
      rw [mul_one]; exact mul_le_mul_of_nonneg_left hmmbar (by positivity)
    rw [hBbar]; linarith
  have hbrk0 : 0 ≤ 2 * (Df * Dg) + G * (m * Dg) + 8 * ((k : ℝ) - 1) ^ 2 * (m * 1) := by
    have t1 : 0 ≤ 2 * (Df * Dg) := by have := mul_nonneg hDf0 hDg0; linarith
    have t2 : 0 ≤ G * (m * Dg) := mul_nonneg hG0 (mul_nonneg hm0 hDg0)
    have t3 : 0 ≤ 8 * ((k : ℝ) - 1) ^ 2 * (m * 1) :=
      mul_nonneg (by positivity) (by rw [mul_one]; exact hm0)
    linarith
  have hvol := volume_real_collar_le hδ hhalf
  have hvol0 : 0 ≤ (volume : Measure ℂ).real (disk ∩ S) := by positivity
  calc ‖Bd k (cutMul (cutSlit k δ c) (groundC k)) g - Bd k (groundC k) g‖
      ≤ (2 * (Df * Dg) + G * (m * Dg) + 8 * ((k : ℝ) - 1) ^ 2 * (m * 1))
          * (volume : Measure ℂ).real (disk ∩ S) := hcollar
    _ ≤ Bbar * (volume : Measure ℂ).real (disk ∩ S) := mul_le_mul_of_nonneg_right hbrk hvol0
    _ ≤ Bbar * (2 * Real.pi * δ) := mul_le_mul_of_nonneg_left hvol hBbar0
    _ = Bbar * (2 * Real.pi) * δ := by ring

/-! ### The quadratic dip and the lower bound -/

/-- **The abstract dip.**  Given a nonzero (negative) linear coefficient `b₀ < 0` and `O(δ)`
error bounds `qU ≤ Cz·δ`, `bδ ≤ b₀ + Cx·δ`, there is `t₀ > 0` and a small `δ ∈ (0,½]` making the
quadratic `qU + 2t₀·bδ + t₀²·A` strictly negative. -/
lemma exists_neg_dip {A Cz Cx b₀ : ℝ} (hb₀ : b₀ < 0) (hCz : 0 ≤ Cz) (hCx : 0 ≤ Cx) :
    ∃ t₀ δ : ℝ, 0 < t₀ ∧ 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ qU bδ : ℝ, qU ≤ Cz * δ → bδ ≤ b₀ + Cx * δ → qU + 2 * t₀ * bδ + t₀ ^ 2 * A < 0 := by
  set ab : ℝ := -b₀ with habdef
  have hab : 0 < ab := by rw [habdef]; linarith
  set t₀ : ℝ := ab / (|A| + 1) with ht₀def
  have hden : 0 < |A| + 1 := by positivity
  have ht₀ : 0 < t₀ := div_pos hab hden
  have ht₀rel : t₀ * (|A| + 1) = ab := by rw [ht₀def]; field_simp
  set M : ℝ := -(2 * t₀ * b₀ + t₀ ^ 2 * A) with hMdef
  have hM0 : 0 < M := by
    have hAle : A ≤ |A| := le_abs_self A
    have h1 : t₀ * A ≤ t₀ * |A| := mul_le_mul_of_nonneg_left hAle ht₀.le
    have h2 : t₀ * |A| = ab - t₀ := by rw [← ht₀rel]; ring
    rw [hMdef]; nlinarith [h1, h2, ht₀, hab]
  set K : ℝ := Cz + 2 * t₀ * Cx with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]; have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht₀.le) hCx; linarith
  have hKden : 0 < 2 * (K + 1) := by positivity
  set δ : ℝ := min (1 / 2) (M / (2 * (K + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hM0 hKden)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδK : δ * (2 * (K + 1)) ≤ M := (le_div_iff₀ hKden).mp (min_le_right _ _)
  refine ⟨t₀, δ, ht₀, hδ0, hδhalf, fun qU bδ hqU hbδ => ?_⟩
  have h2t : 2 * t₀ * bδ ≤ 2 * t₀ * (b₀ + Cx * δ) :=
    mul_le_mul_of_nonneg_left hbδ (by positivity)
  have hexp : qU + 2 * t₀ * bδ + t₀ ^ 2 * A ≤ -M + δ * K := by
    rw [hMdef, hKdef]; nlinarith [hqU, h2t]
  have hfin : -M + δ * K < 0 := by nlinarith [hδK, hδ0, hK0, hM0]
  linarith [hexp, hfin]

/-- **The class-zero mixed lower bound** for `k ≥ 3` and `0 < c ≤ 1/2`.  `1 ≤ seamNat k true false 0`.  The witness is
`u_δ + t₀·v` (`zModeCut` plus a scaled fixed trace partner `vSlitC`), whose disk energy the dip
drives negative: `Qd(u_δ) = O(δ) → 0` while the cross pairing tends to `−2π κ² ν ≠ 0`. -/
theorem one_le_seamNat_true_false_zero (hk : 3 ≤ k) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    (1 : ℕ∞) ≤ seamNat k true false 0 := by
  have hk2 : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hκ : 0 < kap k := kap_pos hk2
  -- the fixed trace partner uses δ₀ = ½
  have hδ₀ : (0 : ℝ) < 1 / 2 := by norm_num
  set ν : ℝ := nuSlit k (1 / 2) c with hνdef
  have hν : 0 < ν := nuSlit_pos hk2 hδ₀ hc hc2
  set b₀ : ℝ := -(2 * Real.pi * kap k ^ 2) * ν with hb₀def
  have hb₀ : b₀ < 0 := by
    have hpos : 0 < 2 * Real.pi * kap k ^ 2 * ν :=
      mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos hκ 2)) hν
    rw [hb₀def]; nlinarith [hpos]
  -- the two O(δ) bounds
  obtain ⟨Cz, hCz⟩ := Qd_zModeCut_le hk2 hc
  obtain ⟨Cx, hCx⟩ := bd_cross_bound hk2 hc (1 / 2)
  have hCz0 : 0 ≤ Cz := by
    have h := hCz (1 / 2) hδ₀ le_rfl
    have hn : (0 : ℝ) ≤ |Qd k (zModeCut k (1 / 2) c)| := abs_nonneg _
    linarith
  have hCx0 : 0 ≤ Cx := by
    have h := hCx (1 / 2) hδ₀ le_rfl
    have hn : (0 : ℝ) ≤ ‖Bd k (cutMul (cutSlit k (1 / 2) c) (groundC k)) (cutSlitC k (1 / 2) c)
      - Bd k (groundC k) (cutSlitC k (1 / 2) c)‖ := norm_nonneg _
    linarith
  -- the dip supplies t₀ and δ
  obtain ⟨t₀, δ, ht₀, hδ0, hδhalf, hdip⟩ :=
    exists_neg_dip (A := Qd k (cutSlitC k (1 / 2) c)) hb₀ hCz0 hCx0
  -- the witness and its smooth model on the disk
  set W : ℂ → ℂ := fun w => zModeCut k δ c w + (t₀ : ℂ) • vSlitC k (1 / 2) c w with hWdef
  have hUnice : DiskNice (cutMul (cutSlit k δ c) (groundC k)) :=
    diskNice_of_contDiff (contDiff_cutMul_groundC k δ c)
  have hgnice : DiskNice (cutSlitC k (1 / 2) c) :=
    diskNice_of_contDiff (contDiff_cutSlitC k (1 / 2) c)
  have hWeq : ∀ w ∈ disk, W w
      = cutMul (cutSlit k δ c) (groundC k) w + (t₀ : ℂ) • cutSlitC k (1 / 2) c w := by
    intro w hw
    rw [hWdef]
    simp only [zModeCut_eq_of_mem hw, vSlitC_eq_of_mem hw]
    congr 1
    simp only [cutMul, groundC]; push_cast; ring
  have hQW : Qd k W = Qd k (cutMul (cutSlit k δ c) (groundC k))
      + 2 * t₀ * (Bd k (cutMul (cutSlit k δ c) (groundC k)) (cutSlitC k (1 / 2) c)).re
      + t₀ ^ 2 * Qd k (cutSlitC k (1 / 2) c) := by
    rw [Qd_congr_disk hWeq]; exact Qd_add_smul hk2 hUnice hgnice t₀
  -- the two bounds feed the dip
  have hqU : Qd k (cutMul (cutSlit k δ c) (groundC k)) ≤ Cz * δ := by
    have hcong : Qd k (cutMul (cutSlit k δ c) (groundC k)) = Qd k (zModeCut k δ c) := by
      refine Qd_congr_disk fun w hw => ?_
      rw [zModeCut_eq_of_mem hw]; simp only [cutMul, groundC]; push_cast; ring
    rw [hcong]; exact le_trans (le_abs_self _) (hCz δ hδ0 hδhalf)
  have hbδ : (Bd k (cutMul (cutSlit k δ c) (groundC k)) (cutSlitC k (1 / 2) c)).re ≤ b₀ + Cx * δ := by
    have hb₀eq : (Bd k (groundC k) (cutSlitC k (1 / 2) c)).re = b₀ := by
      rw [Bd_groundC_cutSlitC hk2, Complex.ofReal_re, hb₀def, hνdef]
    have hdiff : (Bd k (cutMul (cutSlit k δ c) (groundC k)) (cutSlitC k (1 / 2) c)).re - b₀
        ≤ Cx * δ := by
      rw [← hb₀eq, ← Complex.sub_re]
      exact le_trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)) (hCx δ hδ0 hδhalf)
    linarith
  have hQWneg : Qd k W < 0 := by rw [hQW]; exact hdip _ _ hqU hbδ
  -- the witness lies in the space and is smooth on the disk
  have hWmem : W ∈ NatCc k true false ⊓ Erot1 k 0 :=
    Submodule.add_mem _ (zModeCut_mem hk1 hδ0 hc)
      (Submodule.smul_mem _ _ (vSlit_mem hk1 hδ₀ hc))
  have hWcd : ContDiffOn ℝ ∞ W disk :=
    (((contDiff_cutMul_groundC k δ c).add
      ((contDiff_cutSlitC k (1 / 2) c).const_smul (t₀ : ℂ))).contDiffOn).congr hWeq
  -- assemble the lower bound
  rw [seamNat]
  refine formIndex_ge_of_neg (Qd_zero k) ![W] (fun i => ?_) (fun cc hcc => ?_)
  · fin_cases i; exact hWmem
  · have hc0 : cc 0 ≠ 0 := fun h => hcc (funext fun i => by fin_cases i; exact h)
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    rw [Qd_smul hk2 hWcd]
    exact mul_neg_of_pos_of_neg (pow_pos (norm_pos_iff.mpr hc0) 2) hQWneg

/-- **The class-0 mixed seam identity** (`k ≥ 3`, `0 < c ≤ ½`): `seamNat k true false 0 = 1`,
combining the Gram lower bound with the trace-coefficient upper bound (the paper's `ind_{DN,0}=1`,
ksindexi.tex:2466). -/
theorem seamNat_true_false_zero (hk : 3 ≤ k) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    seamNat k true false 0 = 1 := by
  have hk2 : 2 ≤ k := by omega
  refine le_antisymm ?_ (one_le_seamNat_true_false_zero hk hc hc2)
  have hup := KsIndex.SeamUpper.seamNat_le_neumannCount (k := k) (b₁ := true) (b₀ := false)
    hk (r := 0) (by omega)
  rw [seamNat]
  simpa [neumannCount_zero hk] using hup

end KsIndex.SingleDisk
