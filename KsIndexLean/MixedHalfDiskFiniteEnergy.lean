module

public import KsIndexLean.MixedHalfDiskGreen
public import KsIndexLean.WeakH1Integration

@[expose] public section


/-! Finite energy of bounded classical half-period Jacobi fields, derived
from their equation and one-sided mixed boundary conditions. -/
noncomputable section
open Set MeasureTheory Filter Topology Complex Real
namespace KsIndex.Trace.ClassicalMixedHalfDiskJacobi
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.PunctureCutoff KsIndex.FaithfulInjection
variable {k : ℕ} {b1 b0 : Bool} (u : ClassicalMixedHalfDiskJacobi k b1 b0)

/-- The truncated energies have a common bound as puncture cutoffs shrink. -/
theorem uniform_cutoff_energy_bound (hk : 2 ≤ k) :
    ∃ K : ℝ, ∀ {ε : ℝ}, 0 < ε → ε ≤ Real.exp (-1) →
      ∫ w in disk, (cutP k ε w)^(2 : ℕ) * gradSq u.value w ≤ K := by
  obtain ⟨C, hCb⟩ := u.bounded
  have hC : ∀ w ∈ disk, ‖u.value w‖ ≤ C := fun w hw =>
    hCb w (mem_disk_iff.mp hw).le (punctures_notMem_disk (by omega) hw)
  set Vol := (volume (Metric.ball (0 : ℂ) 1)).toReal with hVol
  set Dmax := 4 * π * ((pF k).card : ℝ)^(2 : ℕ) * Mψ^(2 : ℕ) with hDmax
  refine ⟨2 * (8 * ((k : ℝ)-1)^(2 : ℕ) * C^(2 : ℕ) * Vol) + 4 * (C^(2 : ℕ) * Dmax), ?_⟩
  intro ε h0 hε
  have h1 : ε < 1 := hε.trans_lt (Real.exp_lt_one_iff.mpr (by norm_num))
  have hEe := u.cutoff_energy_integrable hk h0 h1
  have hEp := u.cutoff_potential_integrable hk h0 h1
  have hEcross := u.cutoff_cross_integrable hk h0 h1
  have hgc_int : IntegrableOn (gradSq (cutPC k ε)) disk :=
    (integrable_gradSq_cutPC k h0 h1).integrableOn
  have hEqc : IntegrableOn (fun w => ‖u.value w‖^(2 : ℕ) * gradSq (cutPC k ε) w) disk := by
    refine (hgc_int.const_mul (C ^ 2)).mono'
      ((u.smooth.continuousOn.norm.pow 2).mul (continuous_gradSq_cutPC k h0 h1).continuousOn
        |>.aestronglyMeasurable measurableSet_ball)
      (ae_restrict_of_forall_mem measurableSet_ball fun w hw => ?_)
    have hgcnn : (0 : ℝ) ≤ gradSq (cutPC k ε) w := by unfold gradSq; positivity
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hC w hw, norm_nonneg (u.value w)]) hgcnn
  have hbI : IntegrableOn (fun w => 1/2 * ((cutP k ε w)^(2 : ℕ) * gradSq u.value w) +
      2 * (‖u.value w‖^(2 : ℕ) * gradSq (cutPC k ε) w)) disk :=
    (hEe.const_mul (1/2)).add (hEqc.const_mul 2)
  have hcross : -(∫ w in disk, crossDens k ε u.value w).re ≤
      1/2 * (∫ w in disk, (cutP k ε w)^(2 : ℕ) * gradSq u.value w) +
      2 * ∫ w in disk, ‖u.value w‖^(2 : ℕ) * gradSq (cutPC k ε) w := by
    calc
      _ ≤ ‖∫ w in disk, crossDens k ε u.value w‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      _ ≤ ∫ w in disk, ‖crossDens k ε u.value w‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ w in disk, 1/2 * ((cutP k ε w)^(2 : ℕ) * gradSq u.value w) +
          2 * (‖u.value w‖^(2 : ℕ) * gradSq (cutPC k ε) w) :=
        setIntegral_mono_on hEcross.norm hbI measurableSet_disk
          (fun w _ => crossDens_le k h0 h1 u.value w)
      _ = _ := by rw [integral_add (hEe.const_mul _) (hEqc.const_mul _),
                      integral_const_mul, integral_const_mul]
  have hre : (∫ w in disk, (cutP k ε w)^(2 : ℕ) * gradSq u.value w) =
      -(∫ w in disk, crossDens k ε u.value w).re +
      ∫ w in disk, potV k w * (cutP k ε w)^(2 : ℕ) * ‖u.value w‖^(2 : ℕ) := by
    simpa using congrArg Complex.re (u.cutoff_green_identity hk h0 h1)
  have hpot_bd : (∫ w in disk, potV k w * (cutP k ε w)^(2 : ℕ) * ‖u.value w‖^(2 : ℕ)) ≤
      8 * ((k : ℝ)-1)^(2 : ℕ) * C^(2 : ℕ) * Vol := by
    calc (∫ w in Metric.ball (0 : ℂ) 1, potV k w * (cutP k ε w) ^ 2 * ‖u.value w‖ ^ 2)
        ≤ ∫ _ in Metric.ball (0 : ℂ) 1, 8 * ((k : ℝ) - 1) ^ 2 * C ^ 2 :=
          setIntegral_mono_on hEp (integrableOn_const measure_ball_lt_top.ne)
            measurableSet_ball (fun w hw => by
              have hpotnn : 0 ≤ potV k w := by unfold potV; positivity
              have h1' : potV k w ≤ 8 * ((k : ℝ) - 1) ^ 2 := potV_le_of_disk hw
              have h2' : (cutP k ε w) ^ 2 ≤ 1 := by nlinarith [cutP_nonneg k ε w, cutP_le_one k ε w]
              have h3' : ‖u.value w‖ ^ 2 ≤ C ^ 2 := by nlinarith [hC w hw, norm_nonneg (u.value w)]
              have hpc : potV k w * (cutP k ε w) ^ 2 ≤ 8 * ((k : ℝ) - 1) ^ 2 :=
                le_of_le_of_eq (mul_le_mul h1' h2' (sq_nonneg _) (by positivity)) (mul_one _)
              exact mul_le_mul hpc h3' (sq_nonneg _) (by positivity))
      _ = 8 * ((k : ℝ) - 1) ^ 2 * C ^ 2 * Vol := by
          rw [setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def, ← hVol]; ring
  have hqc_bd : (∫ w in disk, ‖u.value w‖^(2 : ℕ) * gradSq (cutPC k ε) w) ≤ C^(2 : ℕ) * Dmax := by
    calc (∫ w in Metric.ball (0 : ℂ) 1, ‖u.value w‖ ^ 2 * gradSq (cutPC k ε) w)
        ≤ ∫ w in Metric.ball (0 : ℂ) 1, C ^ 2 * gradSq (cutPC k ε) w :=
          setIntegral_mono_on hEqc (hgc_int.const_mul _) measurableSet_ball (fun w hw => by
            have hgcnn : (0 : ℝ) ≤ gradSq (cutPC k ε) w := by unfold gradSq; positivity
            exact mul_le_mul_of_nonneg_right (by nlinarith [hC w hw, norm_nonneg (u.value w)]) hgcnn)
      _ = C ^ 2 * ∫ w in Metric.ball (0 : ℂ) 1, gradSq (cutPC k ε) w := integral_const_mul _ _
      _ ≤ C ^ 2 * Dmax := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          calc (∫ w in Metric.ball (0 : ℂ) 1, gradSq (cutPC k ε) w)
              ≤ ∫ w in disk, gradSq (cutPC k ε) w := le_refl _
            _ ≤ 4 * π * ((pF k).card : ℝ) ^ 2 * Mψ ^ 2 / Lε ε := energy_cutP_le k h0 h1
            _ ≤ Dmax := by
                rw [hDmax]
                have hL := one_le_Lε h0 hε
                have hnn : (0 : ℝ) ≤ 4 * π * ((pF k).card : ℝ) ^ 2 * Mψ ^ 2 := by positivity
                rw [div_le_iff₀ (by linarith)]; nlinarith [hnn, hL]
  linarith

/-- No finite-energy assumption is required: it follows by Fatou from the
uniform cutoff estimate. -/
theorem finite_dirichlet_energy (hk : 2 ≤ k) : IntegrableOn (gradSq u.value) disk := by
  obtain ⟨K, hK⟩ := u.uniform_cutoff_energy_bound hk
  exact (integrableOn_of_cutP_bound (by omega) (FaithfulInjection.measurable_gradSq u.value).aestronglyMeasurable
    (fun w _ => gradSq_nonneg _ _)
    (fun j => u.cutoff_energy_integrable hk (cutoffEps_pos j) (cutoffEps_lt_one j))
    (fun j => hK (cutoffEps_pos j) (cutoffEps_le_exp_neg_one j))).1

/-- The classical field supplies all data of the disk Sobolev adapter. -/
def smoothH1Data (hk : 2 ≤ k) : WeakH1.SmoothH1Data where
  F := u.value
  smooth := u.smooth
  value_mem := (memLp_two_iff_integrable_sq_norm
    (u.smooth.continuousOn.aestronglyMeasurable Metric.isOpen_ball.measurableSet)).mpr
      (u.value_sq_integrable (by omega))
  dx_mem := (WeakH1.coordinate_memLp (u.finite_dirichlet_energy hk)).1
  dy_mem := (WeakH1.coordinate_memLp (u.finite_dirichlet_energy hk)).2

/-- The actual Sobolev representative, with energy derived from the classical data. -/
def toH1 (hk : 2 ≤ k) : WeakH1.ComplexH1 := WeakH1.smoothToH1 (u.smoothH1Data hk)

lemma toH1_value_ae (hk : 2 ≤ k) :
    (WeakH1.valueCLM (u.toH1 hk) : ℂ → ℂ) =ᵐ[volume.restrict disk] u.value :=
  WeakH1.smoothToH1_value_ae _

lemma toH1_dx_ae (hk : 2 ≤ k) :
    (WeakH1.dxCLM (u.toH1 hk) : ℂ → ℂ) =ᵐ[volume.restrict disk]
      (fun w => fderiv ℝ u.value w 1) := WeakH1.smoothToH1_dx_ae _

lemma toH1_dy_ae (hk : 2 ≤ k) :
    (WeakH1.dyCLM (u.toH1 hk) : ℂ → ℂ) =ᵐ[volume.restrict disk]
      (fun w => fderiv ℝ u.value w I) := WeakH1.smoothToH1_dy_ae _

end KsIndex.Trace.ClassicalMixedHalfDiskJacobi
