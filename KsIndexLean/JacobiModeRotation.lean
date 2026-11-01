module

public import KsIndexLean.NormalizedJacobiModes
public import KsIndexLean.SectorInfiniteFamily
public import KsIndexLean.DiskRotationForms

@[expose] public section


noncomputable section
open Set MeasureTheory Complex
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.JacobiMode KsIndex.Radial KsIndex.DtNCircle

lemma signedModeU_eq_radial_fourier (k : ℕ) (n : ℤ) (w : ℂ) :
    signedModeU k n w = (gRad k n.natAbs ‖w‖ : ℂ) * fourierAmbient n w := by
  cases n <;> simp [signedModeU, modeU, fourierAmbient, map_mul, map_pow]

lemma signedModeU_planeRotation (k : ℕ) (n : ℤ) (θ : ℝ) (w : ℂ) :
    signedModeU k n (planeRotation θ w) = exp ((n : ℂ) * θ * I) * signedModeU k n w := by
  rw [signedModeU_eq_radial_fourier, (planeRotation θ).norm_map,
    fourierAmbient_planeRotation, signedModeU_eq_radial_fourier]
  ring

lemma normalizedJacobiMode_rotation {k : ℕ} (hk : 2 ≤ k) (n : NZ) (θ : ℝ) :
    diskRotation θ (normalizedJacobiMode hk n) =
      exp ((n.val : ℂ) * θ * I) • normalizedJacobiMode hk n := by
  have h := weakCharacter_of_value_eq
    (globalSmoothH1 (signedModeU k n) (signedModeU_smooth hk n)) θ
    (exp ((n.val : ℂ) * θ * I)) (globalSmoothH1_value _ _)
    (signedModeU_planeRotation k n θ)
  rw [mem_weakCharacterDomain] at h
  simp only [normalizedJacobiMode, map_smul, h]
  exact smul_comm _ _ _

/-- Distinct signed angular frequencies are orthogonal in the full H1 norm. -/
lemma normalizedJacobiMode_inner_eq_zero {k : ℕ} (hk : 2 ≤ k) (n m : NZ) (hnm : n ≠ m) :
    inner ℂ (normalizedJacobiMode hk n) (normalizedJacobiMode hk m) = 0 := by
  have hd : (m.val : ℂ) - n.val ≠ 0 := by
    intro h
    have hi : m.val = n.val := by exact_mod_cast sub_eq_zero.mp h
    exact hnm (Subtype.ext hi.symm)
  let θ : ℝ := Real.pi / ((m.val : ℝ) - n.val)
  have he : (starRingEnd ℂ) (exp ((n.val : ℂ) * θ * I)) *
      exp ((m.val : ℂ) * θ * I) = -1 := by
    rw [← exp_conj, ← exp_add]
    have ha : (starRingEnd ℂ) ((n.val : ℂ) * θ * I) + (m.val : ℂ) * θ * I =
        (Real.pi : ℂ) * I := by
      simp only [map_mul, map_intCast, Complex.conj_ofReal, Complex.conj_I]
      dsimp [θ]
      push_cast
      field_simp
      ring
    rw [ha, exp_pi_mul_I]
  have h := (diskRotation θ).inner_map_map (normalizedJacobiMode hk n) (normalizedJacobiMode hk m)
  rw [normalizedJacobiMode_rotation, normalizedJacobiMode_rotation, inner_smul_left,
    inner_smul_right, ← mul_assoc, he] at h
  have h2 : (2 : ℂ) * inner ℂ (normalizedJacobiMode hk n) (normalizedJacobiMode hk m) = 0 := by
    linear_combination -h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

end KsIndex.Trace
