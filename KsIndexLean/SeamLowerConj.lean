module

/-
# Conjugate cutoff modes and vanishing cross terms

This file proves that pointwise complex conjugation preserves `Qd`, the
natural single-disk domains and `DiskNice`, while conjugating rotation
eigenvalues. It also proves rotation invariance of `Bd` for smooth disk
functions and its scalar multiplication identities.

The modes `cm` are `modeU` multiplied by the puncture cutoff, and `cmC`
are their complex conjugates. Their angular factors are `w^ℓ` and
`conj(w)^ℓ`; the full functions also contain radial and cutoff factors.
For `k ≥ 2`, `0 < ε < 1` and `ℓ + ℓ' = k`, `Bd_cm_cmC` proves that
`Bd k (cm k ε ℓ) (cmC k ε ℓ') = 0`. The screw rotation preserves the
cutoff and multiplies this cross term by `-1`, forcing it to vanish.

The final lemmas place the truncated conjugate modes in the natural
pure-Neumann domain and in rotation class `r` when `r ≡ ℓ (mod k)`.
-/
public import KsIndexLean.SeamLowerNat

@[expose] public section


noncomputable section

open Complex MeasureTheory Filter Topology
open scoped ContDiff

namespace KsIndex.SingleDisk

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.FormIndex KsIndex.Bracket
  KsIndex.SingleDiskBridge KsIndex.PunctureCutoff KsIndex.JacobiMode KsIndex.CutoffContinuity
  KsIndex.ModeDiag KsIndex.ThetaOrtho KsIndex.GradOrtho

variable {k : ℕ}

/-! ### Rotation invariance of the polarized form -/

/-- The disk integral of a complex function is invariant under rotation by a circle element. -/
lemma setIntegral_disk_comp_mul (a : Circle) (F : ℂ → ℂ) :
    ∫ w in disk, F ((a : ℂ) * w) = ∫ w in disk, F w := by
  have hmp : MeasurePreserving (rotation a) volume volume := (rotation a).measurePreserving
  have hemb : MeasurableEmbedding (rotation a) := (rotation a).toHomeomorph.measurableEmbedding
  have hpre : (rotation a) ⁻¹' disk = disk := by
    ext w
    simp only [Set.mem_preimage, rotation_apply, disk, Metric.mem_ball, dist_zero_right,
      norm_mul, Circle.norm_coe, one_mul]
  have h := hmp.setIntegral_preimage_emb hemb F disk
  rw [hpre] at h
  simpa only [rotation_apply] using h

/-- **Rotation invariance of `Bd`** under any unimodular rotation. -/
lemma Bd_rot1 {a : ℂ} (ha : ‖a‖ = 1) {f g : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f disk)
    (hg : ContDiffOn ℝ ∞ g disk) :
    Bd k (rot1 a f) (rot1 a g) = Bd k f g := by
  let ac : Circle := ⟨a, mem_sphere_zero_iff_norm.mpr ha⟩
  have hac : (ac : ℂ) = a := rfl
  unfold Bd
  have h1 : ∫ w in disk, gradInner (rot1 a f) (rot1 a g) w = ∫ w in disk, gradInner f g w := by
    rw [← setIntegral_disk_comp_mul ac (gradInner f g), hac]
    refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    have haw : a * w ∈ disk := by
      rw [mem_disk_iff, norm_mul, ha, one_mul]; exact mem_disk_iff.mp hw
    change gradInner (fun z => f (a * z)) (fun z => g (a * z)) w = gradInner f g (a * w)
    exact gradInner_comp_mul ha
      ((hf.contDiffAt (Metric.isOpen_ball.mem_nhds haw)).differentiableAt (by simp))
      ((hg.contDiffAt (Metric.isOpen_ball.mem_nhds haw)).differentiableAt (by simp))
  have h2 : ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (rot1 a f w) * rot1 a g w
      = ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w := by
    rw [← setIntegral_disk_comp_mul ac (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w),
      hac]
    refine setIntegral_congr_fun measurableSet_disk fun w _ => ?_
    simp only [rot1_apply, KsIndex.ThetaOrtho.potV_rotation k ha]
  rw [h1, h2]

/-- `Bd` pulls out scalars: conjugate-linear on the left. -/
lemma Bd_const_smul_left {f g : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f disk) (c : ℂ) :
    Bd k (c • f) g = (starRingEnd ℂ) c * Bd k f g := by
  unfold Bd
  rw [mul_sub, ← integral_const_mul, ← integral_const_mul]
  congr 1
  · refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    have hd : DifferentiableAt ℝ f w :=
      (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp)
    have hfd : fderiv ℝ (fun z => c • f z) w = c • fderiv ℝ f w := fderiv_const_smul hd c
    change gradInner (fun z => c • f z) g w = _
    rw [gradInner, gradInner, hfd]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, map_mul]
    ring
  · refine setIntegral_congr_fun measurableSet_disk fun w _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring

/-- `Bd` pulls out scalars: linear on the right. -/
lemma Bd_const_smul_right {f g : ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g disk) (c : ℂ) :
    Bd k f (c • g) = c * Bd k f g := by
  unfold Bd
  rw [mul_sub, ← integral_const_mul, ← integral_const_mul]
  congr 1
  · refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    have hd : DifferentiableAt ℝ g w :=
      (hg.contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp)
    have hgd : fderiv ℝ (fun z => c • g z) w = c • fderiv ℝ g w := fderiv_const_smul hd c
    change gradInner f (fun z => c • g z) w = _
    rw [gradInner, gradInner, hgd]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  · refine setIntegral_congr_fun measurableSet_disk fun w _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-! ### Complex conjugation -/

/-- Pointwise complex conjugation of a function. -/
def conjF (f : ℂ → ℂ) : ℂ → ℂ := fun w => (starRingEnd ℂ) (f w)

lemma conjF_eq_comp (f : ℂ → ℂ) : conjF f = ⇑Complex.conjCLE ∘ f := rfl

lemma fderiv_conjF (f : ℂ → ℂ) (w : ℂ) :
    fderiv ℝ (conjF f) w = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f w) := by
  rw [conjF_eq_comp, Complex.conjCLE.comp_fderiv]

lemma gradSq_conjF (f : ℂ → ℂ) (w : ℂ) : gradSq (conjF f) w = gradSq f w := by
  unfold gradSq
  rw [fderiv_conjF]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    Complex.norm_conj]

/-- `Qd` is conjugation-invariant. -/
theorem Qd_conjF (f : ℂ → ℂ) : Qd k (conjF f) = Qd k f := by
  unfold Qd dirichletG potentialG
  congr 1
  · exact setIntegral_congr_fun measurableSet_disk fun w _ => by rw [gradSq_conjF]
  · exact setIntegral_congr_fun measurableSet_disk fun w _ => by
      simp only [conjF, Complex.norm_conj]

lemma contDiff_conjF {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (conjF f) := by
  rw [conjF_eq_comp]; exact Complex.conjCLE.contDiff.comp hf

lemma contDiffOn_conjF {f : ℂ → ℂ} {s : Set ℂ} (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (conjF f) s := by
  rw [conjF_eq_comp]; exact Complex.conjCLE.contDiff.comp_contDiffOn hf

lemma oneSided_conjF {f : ℂ → ℂ} {w₀ : ℂ} (hf : OneSided f w₀) : OneSided (conjF f) w₀ := by
  obtain ⟨F, hF, hFe⟩ := hf
  refine ⟨conjF F, ?_, ?_⟩
  · rw [conjF_eq_comp]; exact Complex.conjCLE.contDiff.contDiffAt.comp w₀ hF
  · filter_upwards [hFe] with w h1 hw
    simp only [conjF, h1 hw]

lemma arcCond_conjF {A S : Set ℂ} {b : Bool} {f : ℂ → ℂ} (hf : ArcCond A S b f) :
    ArcCond A S b (conjF f) := by
  cases b
  · obtain ⟨ε, hε, h⟩ := hf
    exact ⟨ε, hε, fun w hw => by simp only [conjF, h w hw, map_zero]⟩
  · exact fun w hw => oneSided_conjF (hf w hw)

/-- Conjugation preserves every natural single-disk space. -/
theorem conjF_mem_NatCc {b₁ b₀ : Bool} {f : ℂ → ℂ} (hf : f ∈ NatCc k b₁ b₀) :
    conjF f ∈ NatCc k b₁ b₀ := by
  rw [mem_NatCc] at hf ⊢
  obtain ⟨f1, f2, f3, f4, ε, hε, f5⟩ := hf
  exact ⟨contDiffOn_conjF f1, arcCond_conjF f2, arcCond_conjF f3,
    fun w hw => by simp only [conjF, f4 w hw, map_zero],
    ⟨ε, hε, fun w hw => by simp only [conjF, f5 w hw, map_zero]⟩⟩

lemma rot1_conjF (a : ℂ) (f : ℂ → ℂ) : rot1 a (conjF f) = conjF (rot1 a f) := rfl

lemma conjF_smul (c : ℂ) (f : ℂ → ℂ) : conjF (c • f) = (starRingEnd ℂ) c • conjF f := by
  funext w; simp [conjF]

/-- Conjugation flips the rotation eigenvalue. -/
lemma conjF_mem_eigenspace {a μ : ℂ} {f : ℂ → ℂ}
    (hf : f ∈ Module.End.eigenspace (rot1 a) μ) :
    conjF f ∈ Module.End.eigenspace (rot1 a) ((starRingEnd ℂ) μ) := by
  rw [Module.End.mem_eigenspace_iff] at hf ⊢
  rw [rot1_conjF, hf, conjF_smul]

/-- `DiskNice` is preserved by conjugation. -/
lemma diskNice_conjF {u : ℂ → ℂ} (hu : DiskNice u) : DiskNice (conjF u) := by
  obtain ⟨hd, M, hM⟩ := hu
  refine ⟨fun w hw => ?_, M, fun w hw => ⟨?_, ?_⟩⟩
  · rw [conjF_eq_comp]; exact Complex.conjCLE.differentiableAt.comp w (hd w hw)
  · simp only [conjF, Complex.norm_conj]; exact (hM w hw).1
  · rw [fderiv_conjF]
    have h1 : ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
    calc ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ u w)‖
        ≤ ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ)‖ * ‖fderiv ℝ u w‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * M := mul_le_mul h1 (hM w hw).2 (norm_nonneg _) zero_le_one
      _ = M := one_mul M

/-! ### The cut-off modes, both orientations, and their rotation law -/

/-- The puncture cutoff multiplied by `modeU k ℓ`, whose angular factor is `w^ℓ`. -/
def cm (k : ℕ) (ε : ℝ) (ℓ : ℕ) : ℂ → ℂ := cutMul (cutP k ε) (modeU k ℓ)

/-- The cut-off conjugate mode. -/
def cmC (k : ℕ) (ε : ℝ) (ℓ : ℕ) : ℂ → ℂ := conjF (cm k ε ℓ)

lemma contDiff_cm (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (ℓ : ℕ) :
    ContDiff ℝ ∞ (cm k ε ℓ) := contDiff_cutMul_modeU hk h0 h1 ℓ

lemma contDiff_cmC (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (ℓ : ℕ) :
    ContDiff ℝ ∞ (cmC k ε ℓ) := contDiff_conjF (contDiff_cm hk h0 h1 ℓ)

lemma diskNice_cm (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (ℓ : ℕ) : DiskNice (cm k ε ℓ) :=
  diskNice_cutMul (cutP_contDiff k h0 h1) (cutP_nonneg k ε) (cutP_le_one k ε)
    (diskNice_modeU (k := k) hk ℓ)

lemma diskNice_cmC (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (ℓ : ℕ) :
    DiskNice (cmC k ε ℓ) := diskNice_conjF (diskNice_cm hk h0 h1 ℓ)

/-- Rotation law of the cut-off mode with angular factor `w^ℓ`, for any `a` with `‖a‖ = 1`, `a^{2k} = 1`. -/
lemma cm_rot (hk : 1 ≤ k) (ε : ℝ) (ℓ : ℕ) {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = 1) :
    rot1 a (cm k ε ℓ) = (a ^ ℓ) • cm k ε ℓ := by
  funext w
  simp only [rot1_apply, Pi.smul_apply, cm, cutMul, cutP_rot hk ε ha hak, modeU_rotation k ℓ ha,
    smul_eq_mul]
  ring

lemma cmC_rot (hk : 1 ≤ k) (ε : ℝ) (ℓ : ℕ) {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = 1) :
    rot1 a (cmC k ε ℓ) = ((starRingEnd ℂ) (a ^ ℓ)) • cmC k ε ℓ := by
  rw [cmC, rot1_conjF, cm_rot hk ε ℓ ha hak, conjF_smul]

/-- **The cross term vanishes exactly**: for `ℓ + ℓ' = k` the cut-off mode
and conjugate cut-off mode are `Bd`-orthogonal (screw rotation, `a^k = −1`). -/
theorem Bd_cm_cmC (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {ℓ ℓ' : ℕ}
    (hsum : ℓ + ℓ' = k) : Bd k (cm k ε ℓ) (cmC k ε ℓ') = 0 := by
  have hk1 : 1 ≤ k := by omega
  set a := screwUnit k with ha_def
  have ha : ‖a‖ = 1 := norm_screwUnit k
  have hak : a ^ (2 * k) = 1 := by rw [pow_mul', screwUnit_pow hk1, neg_one_sq]
  have hu : ContDiffOn ℝ ∞ (cm k ε ℓ) disk := (contDiff_cm hk1 h0 h1 ℓ).contDiffOn
  have hv : ContDiffOn ℝ ∞ (cmC k ε ℓ') disk := (contDiff_cmC hk1 h0 h1 ℓ').contDiffOn
  have hrot := Bd_rot1 (k := k) ha hu hv
  rw [cm_rot hk1 ε ℓ ha hak, cmC_rot hk1 ε ℓ' ha hak, Bd_const_smul_left hu,
    Bd_const_smul_right hv, ← mul_assoc] at hrot
  have hc : (starRingEnd ℂ) (a ^ ℓ) * (starRingEnd ℂ) (a ^ ℓ') = -1 := by
    rw [← map_mul, ← pow_add, hsum, screwUnit_pow hk1, map_neg, map_one]
  rw [hc] at hrot
  linear_combination (-1/2 : ℂ) * hrot

/-! ### The truncated conjugate mode -/

/-- The cut-off conjugate mode, truncated to the closed disk. -/
def truncCutC (k : ℕ) (ε : ℝ) (ℓ : ℕ) : ℂ → ℂ := conjF (truncCut k ε ℓ)

lemma truncCutC_eq_of_mem {ε : ℝ} {ℓ : ℕ} {w : ℂ} (hw : w ∈ disk) :
    truncCutC k ε ℓ w = cmC k ε ℓ w := by
  simp only [truncCutC, cmC, cm, conjF, truncCut_eq_of_mem hw]

theorem truncCutC_mem_NatCc (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (ℓ : ℕ) :
    truncCutC k ε ℓ ∈ NatCc k true true :=
  conjF_mem_NatCc (truncCut_mem_NatCc hk h0 h1 ℓ)

/-- **The class of the conjugate mode**: `truncCutC ε ℓ ∈ Erot1 k r` when `r ≡ ℓ (mod k)`. -/
theorem truncCutC_mem_Erot1 (hk : 1 ≤ k) (ε : ℝ) {ℓ r : ℕ} (hr : r ≡ ℓ [MOD k]) :
    truncCutC k ε ℓ ∈ Erot1 k r := by
  have hmem : truncCut k ε ℓ ∈ Module.End.eigenspace (rot1 (rotUnit k : ℂ)) ((rotUnit k : ℂ) ^ ℓ) :=
    Module.End.mem_eigenspace_iff.mpr (truncCut_rot hk ε ℓ)
  have h := conjF_mem_eigenspace hmem
  have hk0 : 0 < k := by omega
  have hxi : (xi k)⁻¹ = zeta k := (eq_inv_of_mul_eq_one_left (zeta_mul_xi hk0)).symm
  have heq : (starRingEnd ℂ) ((rotUnit k : ℂ) ^ ℓ) = zeta k ^ r := by
    rw [rotUnit_coe_eq_zeta_inv, map_pow, map_inv₀]
    change (xi k)⁻¹ ^ ℓ = _
    rw [hxi]
    have hz0 : zeta k ≠ 0 := (zeta_prim hk0).ne_zero hk0.ne'
    have hdvd : (k : ℤ) ∣ (ℓ : ℤ) - r := hr.dvd
    have h1 : zeta k ^ ((ℓ : ℤ) - r) = 1 := ((zeta_prim hk0).zpow_eq_one_iff_dvd _).mpr hdvd
    rwa [zpow_sub₀ hz0, zpow_natCast, zpow_natCast, div_eq_one_iff_eq (pow_ne_zero _ hz0)] at h1
  rw [heq] at h
  exact h

end KsIndex.SingleDisk
