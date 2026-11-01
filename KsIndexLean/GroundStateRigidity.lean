module

public import KsIndexLean.GroundStateTransform
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


/-! Rigidity in the equality case of the ground-state energy identity. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.GroundState
open KsIndex.Trace KsIndex.Surface

lemma fderiv_eq_zero_of_gradSq_eq_zero {v : ℂ → ℂ} {z : ℂ}
    (h : gradSq v z = 0) : fderiv ℝ v z = 0 := by
  have h1 : fderiv ℝ v z 1 = 0 := by
    have hs : ‖fderiv ℝ v z 1‖ ^ 2 = 0 := by
      unfold gradSq at h
      nlinarith [sq_nonneg ‖fderiv ℝ v z Complex.I‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
  have hI : fderiv ℝ v z Complex.I = 0 := by
    have hs : ‖fderiv ℝ v z Complex.I‖ ^ 2 = 0 := by
      unfold gradSq at h
      nlinarith [sq_nonneg ‖fderiv ℝ v z 1‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)
  ext w
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using w.re_add_im.symm
  rw [hw, map_add, map_smul, map_smul, h1, hI]
  simp

/-- A zero-energy smooth multiple of a nonvanishing real ground state has
constant multiplier on the open disk. -/
theorem ground_state_multiple_rigid (g v : ℂ → ℂ) (V : ℂ → ℝ)
    (hg : ContDiff ℝ 2 g) (hv : ContDiff ℝ 1 v)
    (hr : ∀ z, (starRingEnd ℂ) (g z) = g z)
    (hb : ∀ z : Circle₁, g z = 0)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian g z + V z * g z = 0)
    (hne : ∀ z ∈ (WeakH1.disk : Set ℂ), g z ≠ 0)
    (hzero : (∫ z in (WeakH1.disk : Set ℂ),
      gradSq (fun w => g w * v w) z - V z * ‖g z * v z‖ ^ 2) = 0) :
    ∃ c : ℂ, ∀ z ∈ (WeakH1.disk : Set ℂ), v z = c := by
  have hc : Continuous (fun z => ‖g z‖ ^ 2 * gradSq v z) :=
    (hg.continuous.norm.pow 2).mul (KsIndex.PiAssembly.continuous_gradSq hv)
  have hi : IntegrableOn (fun z => ‖g z‖ ^ 2 * gradSq v z)
      (WeakH1.disk : Set ℂ) :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
      Metric.ball_subset_closedBall
  rw [disk_ground_state_energy g v V hg hv hr hb he] at hzero
  have ha : (fun z => ‖g z‖ ^ 2 * gradSq v z) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      (fun _ => 0) :=
    (integral_eq_zero_iff_of_nonneg (fun z => mul_nonneg (sq_nonneg _)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))) hi).mp hzero
  have hp := Measure.eqOn_open_of_ae_eq ha WeakH1.disk.isOpen
    hc.continuousOn continuousOn_const
  apply WeakH1.disk.isOpen.exists_is_const_of_fderiv_eq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected (hv.differentiable (by norm_num)).differentiableOn
  intro z hz
  apply fderiv_eq_zero_of_gradSq_eq_zero
  exact (mul_eq_zero.mp (hp hz)).resolve_left (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne z hz)))
/-- For the vertical radial Jacobi field, zero energy of a smooth multiple
forces the multiplier to be constant in the disk. -/
theorem radial_ground_multiple_rigid {k : ℕ} (hk : 2 ≤ k)
    (v : ℂ → ℂ) (hv : ContDiff ℝ 1 v)
    (hzero : (∫ z in (WeakH1.disk : Set ℂ),
      gradSq (fun w => KsIndex.JacobiMode.modeU k 0 w * v w) z -
        potV k z * ‖KsIndex.JacobiMode.modeU k 0 z * v z‖ ^ 2) = 0) :
    ∃ c : ℂ, ∀ z ∈ (WeakH1.disk : Set ℂ), v z = c := by
  apply ground_state_multiple_rigid (KsIndex.JacobiMode.modeU k 0) v (potV k)
    ((KsIndex.ModeDiag.modeU_contDiff (by omega : 1 ≤ k) 0).of_le (by simp)) hv
  · intro z
    simp only [KsIndex.JacobiMode.modeU, pow_zero, mul_one, Complex.conj_ofReal]
  · intro z
    rw [KsIndex.JacobiMode.modeU, show ‖(z : ℂ)‖ = 1 by simp,
      KsIndex.Radial.gRad_zero_one hk]
    simp
  · intro z _
    exact modeU_jacobi hk 0 z
  · intro z hz heq
    have hp := radial_ground_positive hk hz
    rw [heq] at hp
    exact (lt_irrefl 0) hp
  · exact hzero

end KsIndex.GroundState
