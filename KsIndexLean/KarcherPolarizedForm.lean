module

public import KsIndexLean.KarcherSignedForm

@[expose] public section


/-! Complex weighted copywise Jacobi pairing, conjugate-linear in its first
argument on the compact smooth test domain. These are disk-coordinate integrals; intrinsic quotient area
compatibility remains a separate geometric theorem. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace KsIndex.KarcherData

lemma integral_ewAreaMeasure_complex (k : ℕ) (f : ℂ → ℂ) :
    ∫ w, f w ∂ewAreaMeasure k = ∫ w, (Surface.rho k w ^ 2 : ℝ) • f w := by
  rw [ewAreaMeasure, integral_withDensity_eq_integral_toReal_smul
    ((measurable_rho k).pow_const 2).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)]

lemma integral_ew_invMetric (hk : 2 ≤ k) (f : ℂ → ℂ) :
    ∫ w, ((Surface.rho k w ^ 2)⁻¹ : ℝ) • f w ∂ewAreaMeasure k = ∫ w, f w := by
  rw [integral_ewAreaMeasure_complex]
  apply integral_congr_ae
  have hp : ∀ᵐ w : ℂ ∂volume, w ∉ Surface.punctures k :=
    ae_iff.mpr (by simpa using volume_punctures_zero hk)
  filter_upwards [hp] with w hw
  rw [smul_smul, mul_inv_cancel₀ (rho_sq_pos hk hw).ne', one_smul]

lemma integral_ew_potential (hk : 2 ≤ k) (f : ℂ → ℂ) :
    ∫ w, (Surface.absA k w ^ 2 : ℝ) • f w ∂ewAreaMeasure k =
      ∫ w, (Surface.potV k w : ℝ) • f w := by
  rw [integral_ewAreaMeasure_complex]
  apply integral_congr_ae
  have hp : ∀ᵐ w : ℂ ∂volume, w ∉ Surface.punctures k :=
    ae_iff.mpr (by simpa using volume_punctures_zero hk)
  filter_upwards [hp] with w hw
  rw [smul_smul, mul_comm, JacobiFields.absA_sq_mul_rho_sq hk hw]

lemma integrable_ewAreaMeasure_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (f : ℂ → E) :
    Integrable f (ewAreaMeasure k) ↔ Integrable (fun w => (Surface.rho k w ^ 2 : ℝ) • f w) := by
  rw [ewAreaMeasure, integrable_withDensity_iff_integrable_smul'
    ((measurable_rho k).pow_const 2).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)]

lemma integrable_ew_invMetric_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hk : 2 ≤ k) (f : ℂ → E) :
    Integrable (fun w => ((Surface.rho k w ^ 2)⁻¹ : ℝ) • f w) (ewAreaMeasure k) ↔
      Integrable f := by
  rw [integrable_ewAreaMeasure_iff]
  apply integrable_congr
  have hp : ∀ᵐ w : ℂ ∂volume, w ∉ Surface.punctures k :=
    ae_iff.mpr (by simpa using volume_punctures_zero hk)
  filter_upwards [hp] with w hw
  rw [smul_smul, mul_inv_cancel₀ (rho_sq_pos hk hw).ne', one_smul]

lemma integrable_ew_potential_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hk : 2 ≤ k) (f : ℂ → E) :
    Integrable (fun w => (Surface.absA k w ^ 2 : ℝ) • f w) (ewAreaMeasure k) ↔
      Integrable (fun w => (Surface.potV k w : ℝ) • f w) := by
  rw [integrable_ewAreaMeasure_iff]
  apply integrable_congr
  have hp : ∀ᵐ w : ℂ ∂volume, w ∉ Surface.punctures k :=
    ae_iff.mpr (by simpa using volume_punctures_zero hk)
  filter_upwards [hp] with w hw
  rw [smul_smul, mul_comm, JacobiFields.absA_sq_mul_rho_sq hk hw]

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)
  (G H : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)

/-- Weighted Dirichlet pairing minus weighted curvature pairing, summed over
all ordered copies with no averaging factor. -/
def ewJacobiB : ℂ :=
  let u := encodeDiskFunction (R.diskFunctionPullback G)
  let v := encodeDiskFunction (R.diskFunctionPullback H)
  ∑ n : ZMod (2*m),
    ((∫ w, ((Surface.rho k w ^ 2)⁻¹ : ℝ) • GradOrtho.gradInner (u n) (v n) w
        ∂ewAreaMeasure k) -
      ∫ w, (Surface.absA k w ^ 2 : ℝ) • ((starRingEnd ℂ) (u n w) * v n w)
        ∂ewAreaMeasure k)

lemma ewJacobiB_eq_model :
    ewJacobiB R G H = SurfaceForm.jacobiB k m
      (encodeDiskFunction (R.diskFunctionPullback G))
      (encodeDiskFunction (R.diskFunctionPullback H)) := by
  unfold ewJacobiB SurfaceForm.jacobiB
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_ew_invMetric h.out, integral_ew_potential h.out]
  congr 1
  · apply integral_eq_disk_of_exterior
    intro w hw
    simp [GradOrtho.gradInner,
      fderiv_eq_zero_of_exterior _ (encodeDiskFunction_exterior _ n) hw]
  · simp only [Complex.real_smul, mul_assoc]
    apply integral_eq_disk_of_exterior
    intro w hw
    simp [encodeDiskFunction_exterior _ n w hw]

lemma ewJacobiB_self (hG : Continuous G)
    (hu : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.CcSmooth k m) :
    ewJacobiB R G G = (ewJacobiQ R G : ℂ) := by
  rw [R.ewJacobiB_eq_model, SurfaceForm.jacobiB_self h.out,
    R.ewJacobiQ_eq_model G hG hu]

lemma ewJacobiB_modelTestFunction (u v : ZMod (2*m) → ℂ → ℂ) :
    ewJacobiB R (R.modelTestFunction u) (R.modelTestFunction v) =
      SurfaceForm.jacobiB k m u v := by
  rw [R.ewJacobiB_eq_model, R.modelTestFunction_encoding, R.modelTestFunction_encoding]
  unfold SurfaceForm.jacobiB
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  · apply integral_congr_ae
    apply ae_restrict_of_forall_mem SurfaceForm.measurableSet_disk
    intro w hw
    simp only [GradOrtho.gradInner, FaithfulInjection.testTrace_fderiv_on_disk u n hw,
      FaithfulInjection.testTrace_fderiv_on_disk v n hw]
  · apply integral_congr_ae
    apply ae_restrict_of_forall_mem SurfaceForm.measurableSet_disk
    intro w hw
    dsimp only
    rw [FaithfulInjection.testTrace_eqOn_disk (k := k) u n hw,
      FaithfulInjection.testTrace_eqOn_disk (k := k) v n hw]

lemma encoding_pairing_integrable
    (hu : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.CcSmooth k m)
    (hv : encodeDiskFunction (R.diskFunctionPullback H) ∈ Surface.CcSmooth k m)
    (n : ZMod (2*m)) :
    let u := encodeDiskFunction (R.diskFunctionPullback G) n
    let v := encodeDiskFunction (R.diskFunctionPullback H) n
    Integrable (fun w => ((Surface.rho k w ^ 2)⁻¹ : ℝ) • GradOrtho.gradInner u v w)
      (ewAreaMeasure k) ∧
    Integrable (fun w => (Surface.absA k w ^ 2 : ℝ) • ((starRingEnd ℂ) (u w) * v w))
      (ewAreaMeasure k) := by
  dsimp only
  constructor
  · apply (integrable_ew_invMetric_iff h.out _).mpr
    have hi := SurfaceForm.integrableOn_gradInner (SurfaceForm.regular_of_mem hu)
      (SurfaceForm.regular_of_mem hv) n
    apply (hi.integrable_indicator SurfaceForm.measurableSet_disk).congr
    apply (ae_eq_disk_indicator _ ?_).symm
    intro w hw
    simp [GradOrtho.gradInner,
      fderiv_eq_zero_of_exterior _ (encodeDiskFunction_exterior _ n) hw]
  · apply (integrable_ew_potential_iff h.out _).mpr
    simp only [Complex.real_smul, ← mul_assoc]
    have hi := SurfaceForm.integrableOn_potDens (k := k) (SurfaceForm.regular_of_mem hu)
      (SurfaceForm.regular_of_mem hv) n
    apply (hi.integrable_indicator SurfaceForm.measurableSet_disk).congr
    apply (ae_eq_disk_indicator _ ?_).symm
    intro w hw
    simp [encodeDiskFunction_exterior _ n w hw]

open scoped ContDiff Manifold ParameterAtlas
lemma compactSmooth_pairing_integrable :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G → HasCompactSupport G →
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ H → HasCompactSupport H →
    ∀ n : ZMod (2*m),
    let u := encodeDiskFunction (R.diskFunctionPullback G) n
    let v := encodeDiskFunction (R.diskFunctionPullback H) n
    Integrable (fun w => ((Surface.rho k w ^ 2)⁻¹ : ℝ) • GradOrtho.gradInner u v w)
      (ewAreaMeasure k) ∧
    Integrable (fun w => (Surface.absA k w ^ 2 : ℝ) • ((starRingEnd ℂ) (u w) * v w))
      (ewAreaMeasure k) := by
  intro hg hgc hh hhc n
  exact R.encoding_pairing_integrable G H
    ((R.compactSmooth_iff_encoding_mem_CcSmooth G).mp ⟨hg, hgc⟩)
    ((R.compactSmooth_iff_encoding_mem_CcSmooth H).mp ⟨hh, hhc⟩) n

lemma encoding_weighted_energy_integrable
    (hu : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.CcSmooth k m)
    (n : ZMod (2*m)) :
    Integrable (fun w => (Surface.rho k w ^ 2)⁻¹ *
      Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n) w) (ewAreaMeasure k) ∧
    Integrable (fun w => Surface.absA k w ^ 2 *
      ‖encodeDiskFunction (R.diskFunctionPullback G) n w‖ ^ 2) (ewAreaMeasure k) := by
  exact ⟨(integrable_ew_invMetric_iff h.out _).mpr (R.encoding_energy_integrable G hu n).1,
    (integrable_ew_potential_iff h.out _).mpr (R.encoding_energy_integrable G hu n).2⟩

lemma ewJacobiB_conj : ewJacobiB R H G = (starRingEnd ℂ) (ewJacobiB R G H) := by
  rw [R.ewJacobiB_eq_model, R.ewJacobiB_eq_model, SurfaceForm.jacobiB_conj]

lemma ewJacobiB_eq_integral
    (hu : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.CcSmooth k m)
    (hv : encodeDiskFunction (R.diskFunctionPullback H) ∈ Surface.CcSmooth k m) :
    ewJacobiB R G H =
    ∑ n : ZMod (2*m), ∫ w,
      ((Surface.rho k w ^ 2)⁻¹ : ℝ) •
        GradOrtho.gradInner (encodeDiskFunction (R.diskFunctionPullback G) n)
          (encodeDiskFunction (R.diskFunctionPullback H) n) w -
      (Surface.absA k w ^ 2 : ℝ) •
        ((starRingEnd ℂ) (encodeDiskFunction (R.diskFunctionPullback G) n w) *
          encodeDiskFunction (R.diskFunctionPullback H) n w) ∂ewAreaMeasure k := by
  unfold ewJacobiB
  apply Finset.sum_congr rfl
  intro n _
  exact (integral_sub (R.encoding_pairing_integrable G H hu hv n).1
    (R.encoding_pairing_integrable G H hu hv n).2).symm

lemma encode_pullback_add :
    encodeDiskFunction (R.diskFunctionPullback (G + H)) =
      encodeDiskFunction (R.diskFunctionPullback G) + encodeDiskFunction (R.diskFunctionPullback H) := by
  funext n w
  simp only [encodeDiskFunction, diskFunctionPullback, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
  split_ifs <;> simp

lemma encode_pullback_smul (c : ℂ) :
    encodeDiskFunction (R.diskFunctionPullback (c • G)) =
      c • encodeDiskFunction (R.diskFunctionPullback G) := by
  funext n w
  simp only [encodeDiskFunction, diskFunctionPullback, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

lemma ewJacobiB_add_right
    (K : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hu : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.CcSmooth k m)
    (hv : encodeDiskFunction (R.diskFunctionPullback H) ∈ Surface.CcSmooth k m)
    (hw : encodeDiskFunction (R.diskFunctionPullback K) ∈ Surface.CcSmooth k m) :
    ewJacobiB R G (H + K) = ewJacobiB R G H + ewJacobiB R G K := by
  simp only [R.ewJacobiB_eq_model, R.encode_pullback_add]
  exact SurfaceForm.jacobiB_add_right (SurfaceForm.regular_of_mem hu)
    (SurfaceForm.regular_of_mem hv) (SurfaceForm.regular_of_mem hw)

lemma ewJacobiB_smul_right (c : ℂ)
    (hv : encodeDiskFunction (R.diskFunctionPullback H) ∈ Surface.CcSmooth k m) :
    ewJacobiB R G (c • H) = c * ewJacobiB R G H := by
  rw [R.ewJacobiB_eq_model, R.ewJacobiB_eq_model, R.encode_pullback_smul]
  exact SurfaceForm.jacobiB_smul_right c (SurfaceForm.regular_of_mem hv)

lemma ewJacobiB_add_left
    (K : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hu : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.CcSmooth k m)
    (hv : encodeDiskFunction (R.diskFunctionPullback H) ∈ Surface.CcSmooth k m)
    (hw : encodeDiskFunction (R.diskFunctionPullback K) ∈ Surface.CcSmooth k m) :
    ewJacobiB R (G + H) K = ewJacobiB R G K + ewJacobiB R H K := by
  simp only [R.ewJacobiB_eq_model, R.encode_pullback_add]
  exact SurfaceForm.jacobiB_add_left (SurfaceForm.regular_of_mem hu)
    (SurfaceForm.regular_of_mem hv) (SurfaceForm.regular_of_mem hw)

lemma ewJacobiB_smul_left (c : ℂ)
    (hu : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.CcSmooth k m) :
    ewJacobiB R (c • G) H = (starRingEnd ℂ) c * ewJacobiB R G H := by
  rw [R.ewJacobiB_conj H (c • G), R.ewJacobiB_smul_right H G c hu, map_mul,
    ← R.ewJacobiB_conj H G]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
