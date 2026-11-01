module

/-
Cut-off modes in the natural pure-Neumann test space.

`truncCut k ε ℓ` restricts the smooth cut-off mode to the closed disk and
sets it to zero outside. Its values and derivatives on the open disk are
unchanged, so the disk Jacobi energy and negative finite-mode estimates
are preserved. For `1 ≤ k` and `0 < ε < 1`, it belongs to `NatCc k true true`:
it is smooth on the open disk, has one-sided smooth extensions at both arcs,
and vanishes near the punctures.

The rotation convention is `rotUnit k = ζ_k⁻¹`. The truncated mode has
eigenvalue `ζ_k^(−ℓ)`, so `k ∣ r + ℓ` suffices for membership in `Erot1 k r`.
The finite-family negative-energy estimate is supplied in a form suitable
for applying a lower bound on the form index.
-/
public import KsIndexLean.SeamLower
public import KsIndexLean.SingleDiskNat

@[expose] public section


noncomputable section

open Complex MeasureTheory Filter Topology
open scoped ContDiff

namespace KsIndex.SingleDisk

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.FormIndex KsIndex.Bracket
  KsIndex.SingleDiskBridge KsIndex.PunctureCutoff KsIndex.JacobiMode KsIndex.CutoffContinuity
  KsIndex.ModeDiag KsIndex.ThetaOrtho

variable {k : ℕ}

/-! ### `Qd` only sees the open disk -/

lemma gradSq_congr_disk {f g : ℂ → ℂ} (hfg : ∀ w ∈ disk, f w = g w) {w : ℂ} (hw : w ∈ disk) :
    gradSq f w = gradSq g w := by
  have hopen : IsOpen disk := Metric.isOpen_ball
  have heq : f =ᶠ[𝓝 w] g := Filter.eventuallyEq_of_mem (hopen.mem_nhds hw) hfg
  unfold gradSq
  rw [heq.fderiv_eq]

/-- `Qd k` depends only on the values on the open disk. -/
theorem Qd_congr_disk {f g : ℂ → ℂ} (hfg : ∀ w ∈ disk, f w = g w) : Qd k f = Qd k g := by
  unfold Qd dirichletG potentialG
  congr 1
  · exact setIntegral_congr_fun measurableSet_disk fun w hw => by rw [gradSq_congr_disk hfg hw]
  · exact setIntegral_congr_fun measurableSet_disk fun w hw => by rw [hfg w hw]

/-! ### The truncated cut-off mode -/

/-- The cut-off mode `χ_ε · modeU ℓ`, truncated to the closed disk. -/
def truncCut (k : ℕ) (ε : ℝ) (ℓ : ℕ) (w : ℂ) : ℂ :=
  if ‖w‖ ≤ 1 then cutMul (cutP k ε) (modeU k ℓ) w else 0

lemma truncCut_eq_of_mem {ε : ℝ} {ℓ : ℕ} {w : ℂ} (hw : w ∈ disk) :
    truncCut k ε ℓ w = cutMul (cutP k ε) (modeU k ℓ) w := by
  have h1 : ‖w‖ < 1 := by simpa [disk] using hw
  simp [truncCut, h1.le]

/-- The cut-off mode is globally smooth. -/
lemma contDiff_cutMul_modeU (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (ℓ : ℕ) :
    ContDiff ℝ ∞ (cutMul (cutP k ε) (modeU k ℓ)) := by
  have hχ : ContDiff ℝ ∞ (fun w => (cutP k ε w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (cutP_contDiff k h0 h1)
  exact hχ.mul (modeU_contDiff hk ℓ)

/-- The truncated cut-off mode is a natural pure-Neumann test function. -/
theorem truncCut_mem_NatCc (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (ℓ : ℕ) :
    truncCut k ε ℓ ∈ NatCc k true true := by
  have hF := contDiff_cutMul_modeU hk h0 h1 ℓ
  have hone : ∀ w₀, OneSided (truncCut k ε ℓ) w₀ := fun w₀ =>
    ⟨cutMul (cutP k ε) (modeU k ℓ), hF.contDiffAt,
      Eventually.of_forall fun w hw => truncCut_eq_of_mem hw⟩
  rw [mem_NatCc]
  refine ⟨?_, fun w _ => hone w, fun w _ => hone w, fun w hw => ?_,
    ⟨ε ^ 2, by positivity, fun w ⟨p, hp, hwp⟩ => ?_⟩⟩
  · exact hF.contDiffOn.congr fun w hw => truncCut_eq_of_mem hw
  · simp [truncCut, not_le.mpr hw]
  · unfold truncCut
    split_ifs
    · simp [cutMul, cutP_eq_zero hk h0 h1 ⟨p, hp, hwp.le⟩]
    · rfl

/-! ### The rotation-character convention -/

/-- `rotUnit k = e^{−2πi/k} = ζ_k⁻¹`. -/
lemma rotUnit_coe_eq_zeta_inv (k : ℕ) : ((rotUnit k : Circle) : ℂ) = (zeta k)⁻¹ := by
  rw [rotUnit, Circle.coe_exp, zeta, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- The truncated cut-off mode is a `rot1 (rotUnit k)`-eigenfunction with eigenvalue
`(rotUnit k)^ℓ`. -/
lemma truncCut_rot (hk : 1 ≤ k) (ε : ℝ) (ℓ : ℕ) :
    rot1 (rotUnit k : ℂ) (truncCut k ε ℓ) = ((rotUnit k : ℂ) ^ ℓ) • truncCut k ε ℓ := by
  funext w
  have ha : ‖(rotUnit k : ℂ)‖ = 1 := Circle.norm_coe _
  have hak : (rotUnit k : ℂ) ^ (2 * k) = 1 := by
    rw [pow_mul', rotUnit_pow (by omega), one_pow]
  simp only [rot1_apply, Pi.smul_apply, truncCut, norm_mul, ha, one_mul]
  split_ifs with h
  · simp only [cutMul, cutP_rot hk ε ha hak, modeU_rotation k ℓ ha, smul_eq_mul]
    ring
  · simp

/-- If `k ∣ r + ℓ`, the truncated cut-off mode belongs to `Erot1 k r`,
since its rotation eigenvalue is `ζ_k^(−ℓ)`. -/
theorem truncCut_mem_Erot1 (hk : 1 ≤ k) (ε : ℝ) {ℓ r : ℕ} (hr : k ∣ r + ℓ) :
    truncCut k ε ℓ ∈ Erot1 k r := by
  rw [Erot1, Module.End.mem_eigenspace_iff, truncCut_rot hk ε ℓ]
  congr 1
  rw [rotUnit_coe_eq_zeta_inv, inv_pow]
  obtain ⟨q, hq⟩ := hr
  have hz : zeta k ^ (r + ℓ) = 1 := by rw [hq, pow_mul, zeta_pow_N (by omega), one_pow]
  rw [pow_add] at hz
  exact (eq_inv_of_mul_eq_one_left hz).symm

/-! ### `Qd` of combinations is unchanged by the truncation -/

lemma sum_smul_truncCut_eq_on_disk (ε : ℝ) (S : Finset ℕ) (c : ℕ → ℂ) {w : ℂ}
    (hw : w ∈ disk) :
    (∑ ℓ ∈ S, c ℓ • truncCut k ε ℓ) w
      = (∑ ℓ ∈ S, c ℓ • cutMul (cutP k ε) (modeU k ℓ)) w := by
  simp only [Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl fun ℓ _ => by rw [truncCut_eq_of_mem hw]

theorem Qd_sum_truncCut (ε : ℝ) (S : Finset ℕ) (c : ℕ → ℂ) :
    Qd k (∑ ℓ ∈ S, c ℓ • truncCut k ε ℓ)
      = Qd k (∑ ℓ ∈ S, c ℓ • cutMul (cutP k ε) (modeU k ℓ)) :=
  Qd_congr_disk fun _ hw => sum_smul_truncCut_eq_on_disk ε S c hw

/-- **The Gram perturbation, for the truncated modes.** -/
theorem exists_eps_neg_trunc (hk : 2 ≤ k) (S : Finset ℕ) (hS1 : ∀ ℓ ∈ S, 1 ≤ ℓ)
    (hSneg : ∀ ℓ ∈ S, KsIndex.Radial.sigma k ℓ < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ c : ℕ → ℂ, (∃ ℓ ∈ S, c ℓ ≠ 0) →
      Qd k (∑ ℓ ∈ S, c ℓ • truncCut k ε ℓ) < 0 := by
  obtain ⟨ε, h0, h1, hneg⟩ := exists_eps_neg hk S hS1 hSneg
  exact ⟨ε, h0, h1, fun c hc => by rw [Qd_sum_truncCut]; exact hneg c hc⟩

end KsIndex.SingleDisk
