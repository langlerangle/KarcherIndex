module

public import KsIndexLean.EndFieldWitness
public import KsIndexLean.EndChartEnergyAssembly

@[expose] public section


/-! Connection of the actual radius-corrected end field to the energy suppliers. -/
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped ContDiff
namespace KsIndex.EndField
open KsIndex.Surface KsIndex.EndChart KsIndex.B2 KsIndex.FaithfulInjection

lemma endIdx_locally_constant_off_circle {m : ℕ} (p : ℂ) (hp : ‖p‖ = 1)
    (c : ZMod (2*m)) {z : ℂ} (hz : z ≠ 0) (hr : ‖z‖^m < 1)
    (hc : ‖endChart p m z‖ ≠ 1) :
    ∀ᶠ w in 𝓝 z, endIdx m c p w = endIdx m c p z := by
  have hlift : ∃ θ : ℂ → ℝ, ContinuousAt θ z ∧
      (∀ᶠ w in 𝓝 z, ∃ q : ℤ, θ w = Complex.arg w + 2*Real.pi*(q:ℝ)) := by
    by_cases hcut : 0 < z.re ∨ z.im ≠ 0
    · refine ⟨Complex.arg, Complex.continuousAt_arg hcut, ?_⟩
      exact Filter.Eventually.of_forall (fun w => ⟨0, by simp⟩)
    · have hneg : z.re < 0 := by
        push Not at hcut
        have hn : z.re ≠ 0 := fun h => hz (Complex.ext h hcut.2)
        exact lt_of_le_of_ne hcut.1 hn
      refine ⟨fun w => Complex.arg (-w) + Real.pi, argLift_continuousAt (Or.inl hneg), ?_⟩
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact argLift_arg_eq hw
  obtain ⟨θ, hθ, hq⟩ := hlift
  apply endIdx_eventuallyEq_of_lift θ hθ hq
  intro j hj
  obtain ⟨q, he⟩ := hq.self_of_nhds
  have hcos := cos_lift_eq (m := m) (p := p) he
  have he0 : (m:ℝ)*θ z - Complex.arg p - angA m z - 2*Real.pi*(j:ℝ) = 0 := by
    rw [div_eq_iff (by positivity)] at hj
    linear_combination hj
  exact hc (norm_endChart_eq_one_gen hp (le_of_lt (lt_trans hr one_lt_two)) hcos he0)

lemma endField_fderiv_inside_energy {m : ℕ} {u : ZMod (2*m) → ℂ → ℂ}
    (hu : IsSmooth 3 m u) (p : ℂ) (hp : ‖p‖ = 1) (c : ZMod (2*m))
    {z : ℂ} (hz : z ≠ 0) (hr : ‖z‖^m < 1) (hin : ‖endChart p m z‖ < 1) :
    fderiv ℝ (endFieldWith p u (endIdx m c p)) z =
      (fderiv ℝ (u (endIdx m c p z)) (endChart p m z)).comp (endDeriv m z) := by
  have hi := endIdx_locally_constant_off_circle p hp c hz hr hin.ne
  have hEc : ContinuousAt (fun w => ‖endChart p m w‖) z := by
    unfold endChart
    fun_prop
  have heq : endFieldWith p u (endIdx m c p) =ᶠ[𝓝 z]
      (fun w => u (endIdx m c p z) (endChart p m w)) := by
    filter_upwards [hi, hEc.eventually (gt_mem_nhds hin)] with w hw hwin
    rw [endFieldWith_inside p u _ hwin.le, hw]
  rw [heq.fderiv_eq]
  have hmem : endChart p m z ∈ disk := by
    simpa [disk, Metric.mem_ball, dist_zero_right] using hin
  exact (hasFDerivAt_comp_endChart p m z
    (((hu.1 _).contDiffAt (Metric.isOpen_ball.mem_nhds hmem)).differentiableAt
      (by simp)).hasFDerivAt).fderiv

lemma endField_fderiv_outside_energy {m : ℕ} {u : ZMod (2*m) → ℂ → ℂ}
    (hu : IsSmooth 3 m u) (p : ℂ) (hp : ‖p‖ = 1) (c : ZMod (2*m))
    {z : ℂ} (hz : z ≠ 0) (hr : ‖z‖^m < 1) (hout : 1 < ‖endChart p m z‖) :
    fderiv ℝ (endFieldWith p u (endIdx m c p)) z =
      ((fderiv ℝ (u (endIdx m c p z + 1)) (Bracket.σ (endChart p m z))).comp
        (fderiv ℝ Bracket.σ (endChart p m z))).comp (endDeriv m z) := by
  have hi := endIdx_locally_constant_off_circle p hp c hz hr hout.ne'
  have hEc : ContinuousAt (fun w => ‖endChart p m w‖) z := by
    unfold endChart
    fun_prop
  have heq : endFieldWith p u (endIdx m c p) =ᶠ[𝓝 z]
      (fun w => u (endIdx m c p z + 1) (Bracket.σ (endChart p m w))) := by
    filter_upwards [hi, hEc.eventually (lt_mem_nhds hout)] with w hw hwout
    rw [endFieldWith_outside p u _ hwout, hw]
  rw [heq.fderiv_eq]
  have hmem : Bracket.σ (endChart p m z) ∈ disk := by
    have hn : ‖Bracket.σ (endChart p m z)‖ < 1 := by
      rw [Bracket.norm_σ]
      exact inv_lt_one_of_one_lt₀ hout
    simpa [disk, Metric.mem_ball, dist_zero_right] using hn
  have hu' := ((hu.1 (endIdx m c p z + 1)).contDiffAt (Metric.isOpen_ball.mem_nhds hmem)).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hσ := (SigmaDeriv.hasFDerivAt_sigmaR
    (norm_pos_iff.mp (lt_trans zero_lt_one hout))).differentiableAt.hasFDerivAt
  exact ((hu'.hasFDerivAt.comp _ hσ).comp z (hasFDerivAt_endChart p m z)).fderiv

/-- The actual end field has all three full-chart L² inputs, with fixed
radius 1/4. No additional energy or branch-identity hypotheses remain. -/
theorem endField_memLp_bundle {m : ℕ} (hm : 0 < m)
    (u : EnergySmooth 3 m) (p : ℂ) (hp : p ∈ punctures 3) (c : ZMod (2*m))
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p^3).im) :
    MemLp (endFieldWith p u.val (endIdx m c p)) 2
      (volume.restrict (Metric.ball (0 : ℂ) (1/4))) ∧
    MemLp (KsIndex.PunctureRemoval.gradEnc
      (fun z => (endFieldWith p u.val (endIdx m c p) z).re)) 2
      (volume.restrict (Metric.ball (0 : ℂ) (1/4))) ∧
    MemLp (KsIndex.PunctureRemoval.gradEnc
      (fun z => (endFieldWith p u.val (endIdx m c p) z).im)) 2
      (volume.restrict (Metric.ball (0 : ℂ) (1/4))) := by
  have hp1 := norm_eq_one_of_mem_punctures hp
  have hsmall : ∀ z : ℂ, ‖z‖ < (1/2 : ℝ) → ‖z‖^m < 1 := by
    intro z hz
    exact pow_lt_one₀ (norm_nonneg z) (lt_trans hz (by norm_num)) hm.ne'
  apply memLp_complex_jet_of_branch_derivatives hm (esToGrad u) p
    (r₀ := (1/2 : ℝ)) (by norm_num) (by norm_num)
  · intro z hz hzr
    exact endField_contDiffAt_punctured p hp1 hp u.property.1 u.property.2.2.2.2
      c hbit z (norm_pos_iff.mp hz) (hsmall z hzr)
  · intro z hz hi
    exact ⟨endIdx m c p z, endField_fderiv_inside_energy u.property.1 p hp1 c
      (norm_pos_iff.mp hz.1) (hsmall z (lt_of_le_of_lt hz.2 (by norm_num))) hi⟩
  · intro z hz ho
    exact ⟨endIdx m c p z + 1, endField_fderiv_outside_energy u.property.1 p hp1 c
      (norm_pos_iff.mp hz.1) (hsmall z (lt_of_le_of_lt hz.2 (by norm_num))) ho⟩

end KsIndex.EndField
