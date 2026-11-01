module

public import KsIndexLean.CirclePowerL2
public import KsIndexLean.FiniteFourierUniqueness
public import KsIndexLean.AngularFourierIdentity
public import KsIndexLean.SingleArcEquivalence
public import KsIndexLean.CircleSobolevApproximation
public import KsIndexLean.JacobiExtensionTrace

@[expose] public section


noncomputable section
open MeasureTheory
namespace KsIndex.Trace
open KsIndex.CircleSobolev KsIndex.ModeWitness KsIndex.SingleArcReindex

lemma phased_fourierAmbient (k c : ℕ) (n : ℤ) (w : Circle₁) :
    (w : ℂ)^c * fourierAmbient n (circlePower k w) =
      fourierAmbient ((k : ℤ)*n+c) w := by
  have hw : (w : ℂ) ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp w.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  rw [fourierAmbient_eq_zpow_on_circle, fourierAmbient_eq_zpow_on_circle]
  change (w : ℂ)^c * ((w : ℂ)^k)^n = _
  rw [zpow_add₀ hw, zpow_natCast, mul_comm]
  congr 1
  rw [← zpow_natCast (w : ℂ) k, ← zpow_mul]

lemma phasedPower_fourierTest {k : ℕ} (hk : 0 < k) (c : ℕ) (n : ℤ) :
    phasedPowerLI hk c (fourierTestLp n) = fourierTestLp ((k : ℤ)*n+c) := by
  apply Lp.ext
  have h := (measurePreserving_circlePower hk).quasiMeasurePreserving.ae_eq_comp
    (fourierTestLp_coe n)
  filter_upwards [phasedPowerL2_ae hk c (fourierTestLp n), h,
    fourierTestLp_coe ((k : ℤ)*n+c)] with w hp hn ht
  change phasedPowerL2 hk c (fourierTestLp n) w = _
  simp only [Function.comp_apply] at hn
  rw [hp, hn, ht]
  exact phased_fourierAmbient k c n w

lemma toL2_single (n : ℤ) (a : ℂ) :
    toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (lp.single 2 n a) =
      ((weight (1 / 2) n : ℂ)⁻¹ * a) • fourierTestLp n := by
  apply circleFourierCLE.injective
  apply Subtype.ext
  funext m
  simp only [circleFourierCLE_apply, fourierCoeff_toL2]
  rw [← circleCoefficientCLM_apply]
  rw [map_smul, circleCoefficientCLM_apply,
    congrFun (circleFourierCoeff_congr_ae (fourierTestLp_coe n)) m,
    circleFourierCoeff_fourierAmbient]
  by_cases h : n = m
  · subst m
    simp [coeff]
  · simp [coeff, Ne.symm h]

lemma toL2_insert_single {k j : ℕ} (hk : 3 ≤ k) (n : ℤ) (a : ℂ) :
    toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (insert hk j (lp.single 2 n a)) =
      ((weight (1 / 2) n : ℂ)⁻¹ * a) • fourierTestLp (lz k j n) := by
  apply circleFourierCLE.injective
  apply Subtype.ext
  funext m
  simp only [circleFourierCLE_apply, fourierCoeff_toL2, coeff_insert]
  rw [← circleCoefficientCLM_apply, map_smul, circleCoefficientCLM_apply,
    congrFun (circleFourierCoeff_congr_ae (fourierTestLp_coe (lz k j n))) m,
    circleFourierCoeff_fourierAmbient]
  by_cases hm : ∃ q, m = lz k j q
  · obtain ⟨q, rfl⟩ := hm
    rw [insertCoeff_lattice hk]
    by_cases hn : n = q
    · subst q
      simp [coeff]
    · have hl : lz k j n ≠ lz k j q := fun h => hn (lz_injective hk h)
      simp [coeff, Ne.symm hn, Ne.symm hl]
  · rw [insertCoeff_off k j _ m hm]
    have hl : m ≠ lz k j n := fun h => hm ⟨n, h⟩
    simp [hl]

/-- Fourier insertion and the geometric phased covering agree on all Hhalf data. -/
theorem toL2_insert_eq_phasedPower {k j : ℕ} (hk : 3 ≤ k) (hj : j ≤ k)
    (f : Space (1 / 2)) :
    toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (insert hk j f) =
      phasedPowerLI (by omega : 0 < k) (k - j)
        (toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num) f) := by
  let I : Space (1 / 2) →L[ℂ] Space (1 / 2) :=
    LinearMap.mkContinuous
      ({ toFun := insert hk j
         map_add' := fun f g => congrArg Subtype.val ((characterEquiv hk hj).symm.map_add f g)
         map_smul' := fun c f =>
           congrArg Subtype.val ((characterEquiv hk hj).symm.map_smul c f) } :
        Space (1 / 2) →ₗ[ℂ] Space (1 / 2))
      (Real.sqrt ((k : ℝ) + 1)) (fun f => by
        change ‖insert hk j f‖ ≤ Real.sqrt ((k : ℝ) + 1) * ‖f‖
        apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
        simpa only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)]
          using insert_norm_sq_le hk j f)
  let L : Space (1 / 2) →L[ℂ] Lp ℂ 2 circleMeasure :=
    (toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)).comp I
  let R : Space (1 / 2) →L[ℂ] Lp ℂ 2 circleMeasure :=
    (phasedPowerLI (by omega : 0 < k) (k - j)).toContinuousLinearMap.comp
      (toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num))
  have he (n : ℤ) (a : ℂ) : L (lp.single 2 n a) = R (lp.single 2 n a) := by
    simp only [L, R, I, ContinuousLinearMap.comp_apply, LinearMap.mkContinuous_apply]
    change toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (insert hk j (lp.single 2 n a)) =
      phasedPowerLI (by omega : 0 < k) (k - j)
        (toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (lp.single 2 n a))
    rw [toL2_insert_single hk, toL2_single, map_smul, phasedPower_fourierTest]
    rfl
  have hsum := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) f
  have hl := L.hasSum hsum
  have hr := R.hasSum hsum
  have hh : (fun n : ℤ => L (lp.single 2 n (f n))) =
      (fun n : ℤ => R (lp.single 2 n (f n))) := funext fun n => he n (f n)
  rw [hh] at hl
  have hx := hl.unique hr
  exact hx

end KsIndex.Trace
