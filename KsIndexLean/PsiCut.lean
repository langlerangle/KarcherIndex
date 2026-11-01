module

/-
KsIndexLean — Cut finite-mode witnesses in the natural mixed space.

The slit cutoff times the finite-mode witness, truncated to the closed disk,

  `psiCut k r N t δ c = 𝟙_{‖w‖ ≤ 1}·(cutSlit k δ c)·(Psi k r N t)`,

belongs to `NatCc k true false ⊓ Erot1 k r` when `k ≥ 3`, `1 ≤ r ≤ k - 1`,
and the cutoff parameters `δ, c` are positive (`psiCut_mem`). The natural
condition on `arc_1` uses the globally smooth untruncated product as a
one-sided extension. The essential Dirichlet condition on `arc_0` follows
from vanishing near the closed slit. Since `punctures ⊆ slit`, the support
also stays away from the punctures. Rotation invariance of the cutoff and
of the closed disk preserves the witness's rotation class.

On the open disk, `psiCut` equals `cutMul (cutSlit k δ c) (Psi k r N t)`.
The lemma `Qd_psiCut_eq` transfers its energy to this untruncated product.
The file also proves that `Qd` depends only on open-disk data and scales
by `‖c‖²` under multiplication by a complex scalar.
-/
public import KsIndexLean.ModeWitness
public import KsIndexLean.SlitCutoff
public import KsIndexLean.CutoffContinuity

@[expose] public section


noncomputable section

open Complex Real Set Filter
open scoped ContDiff
open KsIndex.Surface KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.ModeKit
  KsIndex.ModeWitness KsIndex.SurfaceSym KsIndex.SurfaceForm KsIndex.Bracket
  KsIndex.FormIndex

namespace KsIndex.PsiCut

variable {k r : ℕ}

/-- **The cut class-`r` witness**, truncated to the closed disk. -/
def psiCut (k r N : ℕ) (t : ℤ → ℂ) (δ c : ℝ) (w : ℂ) : ℂ :=
  if ‖w‖ ≤ 1 then ((cutSlit k δ c w : ℝ) : ℂ) * Psi k r N t w else 0

lemma psiCut_eq_of_mem {N : ℕ} {t : ℤ → ℂ} {δ c : ℝ} {w : ℂ} (hw : w ∈ disk) :
    psiCut k r N t δ c w = ((cutSlit k δ c w : ℝ) : ℂ) * Psi k r N t w := by
  have h1 : ‖w‖ < 1 := mem_disk_iff.mp hw
  simp [psiCut, h1.le]

/-- The untruncated product is globally smooth. -/
lemma contDiff_psiCutF (k r N : ℕ) (t : ℤ → ℂ) (δ c : ℝ) :
    ContDiff ℝ ∞ (fun w => ((cutSlit k δ c w : ℝ) : ℂ) * Psi k r N t w) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_cutSlit k δ c)).mul (contDiff_Psi k r N t)

/-- **Membership in the natural mixed space** (Neumann on `arc_1`, Dirichlet on `arc_0`). -/
theorem psiCut_mem_NatCc (hk : 1 ≤ k) (N : ℕ) (t : ℤ → ℂ) {δ c : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) :
    psiCut k r N t δ c ∈ NatCc k true false := by
  have hF := contDiff_psiCutF k r N t δ c
  have hone : ∀ w₀, KsIndex.Bracket.OneSided (psiCut k r N t δ c) w₀ := fun w₀ =>
    ⟨_, hF.contDiffAt, Eventually.of_forall fun w hw => psiCut_eq_of_mem hw⟩
  obtain ⟨ε, hε, hnb⟩ := slit_nbhd hk hδ hc
  have hvan : ∀ w : ℂ, (∃ p ∈ slit k, ‖w - p‖ < ε) → psiCut k r N t δ c w = 0 := by
    intro w hw
    obtain ⟨h1, h2⟩ := hnb w hw
    unfold psiCut
    split_ifs
    · rw [cutSlit_zero hδ hc h1 h2, Complex.ofReal_zero, zero_mul]
    · rfl
  rw [mem_NatCc]
  refine ⟨hF.contDiffOn.congr fun w hw => psiCut_eq_of_mem hw,
    fun w _ => hone w,
    ⟨ε, hε, hvan⟩,
    fun w hw => by simp [psiCut, not_le.mpr hw],
    ⟨ε, hε, fun w ⟨p, hp, hwp⟩ =>
      hvan w ⟨p, KsIndex.Bracket.punctures_subset_slit hk hp, hwp⟩⟩⟩

/-- The truncated cut witness inherits `Psi`'s rotation class. -/
theorem psiCut_mem_Erot1 (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (N : ℕ)
    (t : ℤ → ℂ) (δ c : ℝ) : psiCut k r N t δ c ∈ Erot1 k r := by
  have ha : ‖(rotUnit k : ℂ)‖ = 1 := Circle.norm_coe _
  have hak : (rotUnit k : ℂ) ^ k = 1 := rotUnit_pow (by omega)
  rw [Erot1, Module.End.mem_eigenspace_iff]
  funext w
  show psiCut k r N t δ c ((rotUnit k : ℂ) * w) = zeta k ^ r • psiCut k r N t δ c w
  -- the mode witness's own rotation law, pointwise
  have hPsi : Psi k r N t ((rotUnit k : ℂ) * w) = zeta k ^ r * Psi k r N t w := by
    have h := Psi_mem_Erot1 hk hr1 hrk N t
    rw [Erot1, Module.End.mem_eigenspace_iff] at h
    have hw := congrFun h w
    simpa [rot1_apply, smul_eq_mul] using hw
  unfold psiCut
  rw [norm_mul, ha, one_mul, cutSlit_rot ha hak]
  split_ifs
  · rw [hPsi]
    simp only [smul_eq_mul]
    ring
  · simp

/-- The cut class-`r` witness lies in the mixed natural cell. -/
theorem psiCut_mem (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (N : ℕ) (t : ℤ → ℂ)
    {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    psiCut k r N t δ c ∈ NatCc k true false ⊓ Erot1 k r :=
  Submodule.mem_inf.mpr
    ⟨psiCut_mem_NatCc (by omega) N t hδ hc, psiCut_mem_Erot1 hk hr1 hrk N t δ c⟩

/-! ### `Qd` sees only open-disk data -/

/-- **The `Qd`-congruence**: two functions agreeing on the open disk have equal one-disk Jacobi
energy — both integrals run over `disk`, and the `fderiv` at an interior point only sees the
open-disk germ. -/
lemma Qd_congr_disk {f g : ℂ → ℂ} (h : ∀ w ∈ disk, f w = g w) : Qd k f = Qd k g := by
  have hopen : IsOpen disk := Metric.isOpen_ball
  have hfd : ∀ w ∈ disk, fderiv ℝ f w = fderiv ℝ g w := fun w hw =>
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hopen.mem_nhds hw) h)
  unfold Qd dirichletG potentialG
  congr 1
  · refine MeasureTheory.setIntegral_congr_fun measurableSet_disk (fun w hw => ?_)
    unfold gradSq
    rw [hfd w hw]
  · refine MeasureTheory.setIntegral_congr_fun measurableSet_disk (fun w hw => ?_)
    rw [h w hw]

/-- The truncation is `Qd`-invisible: `Qd (psiCut) = Qd (cutMul cutSlit Psi)` so energy estimates for `cutMul`, such as `Qd_cut_collar`, apply to this witness. -/
lemma Qd_psiCut_eq (k r N : ℕ) (t : ℤ → ℂ) (δ c : ℝ) :
    Qd k (psiCut k r N t δ c)
      = Qd k (KsIndex.CutoffContinuity.cutMul (cutSlit k δ c) (Psi k r N t)) :=
  Qd_congr_disk (fun w hw => by
    rw [psiCut_eq_of_mem hw]
    rfl)

/-! ### Scaling of `Qd` by complex scalars -/

lemma gradSq_smul (c : ℂ) (f : ℂ → ℂ) (w : ℂ) :
    gradSq (c • f) w = ‖c‖ ^ 2 * gradSq f w := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul]
    unfold gradSq
    simp
  · by_cases hf : DifferentiableAt ℝ f w
    · unfold gradSq
      rw [fderiv_const_smul hf c]
      simp only [ContinuousLinearMap.smul_apply, norm_smul]
      ring
    · have hcf : ¬ DifferentiableAt ℝ (c • f) w := fun h => hf (by
        have h2 := h.const_smul c⁻¹
        have h3 : c⁻¹ • (c • f) = f := by
          funext z
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
        rwa [h3] at h2)
      unfold gradSq
      rw [fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt hcf]
      simp

/-- **`Qd` is quadratic**: `Qd (c • f) = ‖c‖² · Qd f` (unconditional). -/
lemma Qd_smul (k : ℕ) (c : ℂ) (f : ℂ → ℂ) : Qd k (c • f) = ‖c‖ ^ 2 * Qd k f := by
  unfold Qd dirichletG potentialG
  rw [show (∫ w in disk, (gradSq (c • f) w / rho k w ^ 2) * rho k w ^ 2)
      = ∫ w in disk, ‖c‖ ^ 2 * ((gradSq f w / rho k w ^ 2) * rho k w ^ 2) from
    MeasureTheory.setIntegral_congr_fun measurableSet_disk (fun w _ => by
      rw [gradSq_smul]; ring),
    show (∫ w in disk, (absA k w * ‖(c • f) w‖) ^ 2 * rho k w ^ 2)
      = ∫ w in disk, ‖c‖ ^ 2 * ((absA k w * ‖f w‖) ^ 2 * rho k w ^ 2) from
    MeasureTheory.setIntegral_congr_fun measurableSet_disk (fun w _ => by
      rw [Pi.smul_apply, norm_smul]; ring),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  ring


end KsIndex.PsiCut
