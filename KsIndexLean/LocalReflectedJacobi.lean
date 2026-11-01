module

public import KsIndexLean.GeneralBoundaryParity

@[expose] public section


/-! Bounded chain fields obtained from a smooth disk representative and its
local odd/even reflection identity. No global extension of the PDE is required. -/
noncomputable section
open Set Filter
namespace KsIndex.JacobiFamily
open KsIndex.Surface KsIndex.Trace KsIndex.JacobiFields KsIndex.SurfaceForm

lemma glue_symFam_on_collar {m : ℕ} {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {f : ℂ → ℂ}
    (hf : ∀ w ∈ seamDomain Set.univ isOpen_univ, f (Bracket.σ w) = ε * f w)
    (n : ZMod (2 * m)) {w : ℂ} (hw : w ∈ seamDomain Set.univ isOpen_univ) :
    glue (symFam m ε f) n w = ε ^ (parity m n).val * f w := by
  unfold glue
  split_ifs with h
  · exact symFam_of_le n h
  · have hwgt : 1 < ‖w‖ := lt_of_not_ge h
    have hs : ‖(1 : ℂ) / (starRingEnd ℂ) w‖ ≤ 1 := by
      rw [norm_sigma]
      exact (div_le_one (by positivity)).mpr hwgt.le
    rw [symFam_of_le _ hs]
    change ε ^ (parity m (n + 1)).val * f (Bracket.σ w) = _
    rw [hf w hw, parity_succ_val, ← mul_assoc, pow_sub_mul hε (parity_val_lt_two m n)]

lemma isSmooth_symFam_local {k m : ℕ} {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {f : ℂ → ℂ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2))
    (hf : ∀ w ∈ seamDomain Set.univ isOpen_univ, f (Bracket.σ w) = ε * f w) :
    IsSmooth k m (symFam m ε f) := by
  refine ⟨fun n => ?_, fun n w hw => ?_, fun n w hw => ?_⟩
  · refine ((contDiffOn_const (c := ε ^ (parity m n).val)).mul (hsm.mono
      (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)))).congr fun w hw => ?_
    exact symFam_of_le n (le_of_lt (by simpa only [dist_zero_right] using Metric.mem_ball.mp hw))
  · have hn : ‖w‖ = 1 := hw.1
    have hs : w ∈ seamDomain Set.univ isOpen_univ := by rw [fullSeam_mem_iff, hn]; norm_num
    have hb : w ∈ Metric.ball (0 : ℂ) 2 := by simp [Metric.mem_ball, hn]
    have he : glue (symFam m ε f) n =ᶠ[nhds w] (fun z => ε ^ (parity m n).val * f z) := by
      filter_upwards [(seamDomain Set.univ isOpen_univ).isOpen.mem_nhds hs] with z hz
      exact glue_symFam_on_collar hε hf n hz
    exact (contDiffAt_const.mul (hsm.contDiffAt (Metric.isOpen_ball.mem_nhds hb))).congr_of_eventuallyEq he
  · simp [symFam, cutD_of_lt hw]

lemma isBounded_symFam_local {m : ℕ} {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {f : ℂ → ℂ}
    (hb : ∃ C : ℝ, ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖f w‖ ≤ C) :
    IsBounded (symFam m ε f) := by
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (f 0)) (hC 0 (by simp))
  have hε1 : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  refine ⟨C, fun n w => ?_⟩
  unfold symFam cutD
  rw [norm_mul, norm_pow, hε1, one_pow, one_mul]
  split_ifs with hw
  · exact hC w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)
  · simpa using hC0

lemma isJacobiField_symFam_local {k m : ℕ} (hk : 2 ≤ k) {ε : ℂ} {f : ℂ → ℂ}
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2))
    (hP : ∀ w ∈ (disk : Set ℂ), laplacian f w + (potV k w : ℂ) * f w = 0) :
    IsJacobiField k m (symFam m ε f) := by
  intro n w hw
  let c : ℂ := ε ^ (parity m n).val
  have he : symFam m ε f n =ᶠ[nhds w] c • f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
    exact symFam_of_le n (le_of_lt (by simpa only [dist_zero_right] using Metric.mem_ball.mp hz))
  have hsmw := hsm.contDiffAt (Metric.isOpen_ball.mem_nhds
    (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hw))
  have hv : symFam m ε f n w = c * f w := he.self_of_nhds
  rw [laplacianG, laplacian_congr he, laplacian_smul c hsmw, hv]
  have hj := laplacianG_add_absASq_of_flat hk hw (hP w hw)
  rw [laplacianG] at hj
  linear_combination c * hj

/-- Local smooth reflected data define an actual normalized bounded Jacobi field
on every finite cyclic chain. -/
def localReflectedJacobi {k : ℕ} (hk : 2 ≤ k) (m : ℕ) (ε : ℂ)
    (hε : ε = 1 ∨ ε = -1) (f : ℂ → ℂ)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2))
    (hf : ∀ w ∈ seamDomain Set.univ isOpen_univ, f (Bracket.σ w) = ε * f w)
    (hb : ∃ C : ℝ, ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖f w‖ ≤ C)
    (hP : ∀ w ∈ (disk : Set ℂ), laplacian f w + (potV k w : ℂ) * f w = 0) :
    BoundedJacobi k m := by
  have hbc : ε = -1 → ∀ w : ℂ, ‖w‖ = 1 → f w = 0 := by
    intro hε w hw
    have hs : w ∈ seamDomain Set.univ isOpen_univ := by rw [fullSeam_mem_iff, hw]; norm_num
    have h := hf w hs
    change f ((1 : ℂ) / (starRingEnd ℂ) w) = ε * f w at h
    rw [sigma_fix hw, hε] at h
    linear_combination (1 / 2 : ℂ) * h
  exact ⟨punc0 k (symFam m ε f),
    isSmooth_punc0 (by omega) (isSmooth_symFam_local hε hsm hf),
    isBounded_punc0 (isBounded_symFam_local hε hb),
    isJacobiField_punc0 (by omega) (isJacobiField_symFam_local hk hsm hP),
    punctureZero_punc0 k _, seamVal_punc0 (seamVal_symFam hε hbc)⟩

end KsIndex.JacobiFamily
