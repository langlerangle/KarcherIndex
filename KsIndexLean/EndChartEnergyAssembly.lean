module

public import KsIndexLean.EndChartBaseEnergy
public import KsIndexLean.EndChartReflectionEnergy
public import KsIndexLean.EndChartNullSets
public import KsIndexLean.EndChartL2Jet
public import KsIndexLean.SphericalInversionMeasure

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.EndChart
open KsIndex.FaithfulInjection

/-- A finite choice of finite-energy densities still has finite energy;
the choice function itself need not be measurable. -/
lemma lintegral_ne_top_of_finite_choices {ι : Type*} [Fintype ι]
    {μ : Measure ℂ} (f : ℂ → ℝ≥0∞) (g : ι → ℂ → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) (hfin : ∀ i, (∫⁻ z, g i z ∂μ) ≠ ⊤)
    (hchoice : ∀ᵐ z ∂μ, ∃ i, f z ≤ g i z) :
    (∫⁻ z, f z ∂μ) ≠ ⊤ := by
  classical
  have hb : (∫⁻ z, f z ∂μ) ≤ ∑ i, ∫⁻ z, g i z ∂μ := by
    rw [← lintegral_finsetSum Finset.univ (fun i _ => hg i)]
    apply lintegral_mono_ae
    filter_upwards [hchoice] with z hz
    obtain ⟨i, hi⟩ := hz
    exact hi.trans (Finset.single_le_sum (f := fun j => g j z) (fun j _ => bot_le) (Finset.mem_univ i))
  apply ne_top_of_le_ne_top _ hb
  exact ENNReal.sum_ne_top.mpr (fun i _ => hfin i)

def directEnergy {m : ℕ} (u : ZMod (2*m) → ℂ → ℂ) (L : ℂ →L[ℝ] ℝ)
    (p : ℂ) (n : ZMod (2*m)) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖(L.comp (fderiv ℝ (u n) (endChart p m z))).comp (endDeriv m z)‖^2)

def reflectedEnergy {m : ℕ} (u : ZMod (2*m) → ℂ → ℂ) (L : ℂ →L[ℝ] ℝ)
    (p : ℂ) (n : ZMod (2*m)) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖((L.comp (fderiv ℝ (u n) (Bracket.σ (endChart p m z)))).comp
    (fderiv ℝ Bracket.σ (endChart p m z))).comp (endDeriv m z)‖^2)

lemma measurable_endDeriv (m : ℕ) : Measurable (endDeriv m) := by
  have heq : endDeriv m = fderiv ℝ (endChart 0 m) := by
    funext z
    exact (hasFDerivAt_endChart 0 m z).fderiv.symm
  rw [heq]
  exact measurable_fderiv ℝ _

lemma measurable_directEnergy {m : ℕ} (u : ZMod (2*m) → ℂ → ℂ)
    (L : ℂ →L[ℝ] ℝ) (p : ℂ) (n : ZMod (2*m)) :
    Measurable (directEnergy u L p n) := by
  have hE : Measurable (endChart p m) := by unfold endChart; fun_prop
  have hD := (measurable_fderiv ℝ (u n)).comp hE
  have hd := measurable_endDeriv m
  unfold directEnergy
  fun_prop

lemma measurable_reflectedEnergy {m : ℕ} (u : ZMod (2*m) → ℂ → ℂ)
    (L : ℂ →L[ℝ] ℝ) (p : ℂ) (n : ZMod (2*m)) :
    Measurable (reflectedEnergy u L p n) := by
  have hE : Measurable (endChart p m) := by unfold endChart; fun_prop
  have hD := (measurable_fderiv ℝ (u n)).comp (KsIndex.Spherical.measurable_sigma.comp hE)
  have hs := (measurable_fderiv ℝ Bracket.σ).comp hE
  have hd := measurable_endDeriv m
  unfold reflectedEnergy
  fun_prop

lemma directEnergy_ne_top {k m : ℕ} (hm : 0 < m) (u : GradEnergySmooth k m)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (p : ℂ) (n : ZMod (2*m))
    {A : Set ℂ} (hA : MeasurableSet A)
    (hAin : ∀ z ∈ A, ‖endChart p m z‖ < 1) :
    (∫⁻ z in A, directEnergy u.val L p n z ∂volume) ≠ ⊤ := by
  have hb := lintegral_energy_comp_endChart_le p hm hA
    (N := (KsIndex.WeakH1.disk : Set ℂ))
    (by rintro _ ⟨z, hz, rfl⟩; simpa [KsIndex.WeakH1.disk, Metric.mem_ball, dist_zero_right] using hAin z hz)
    (fun w => L.comp (fderiv ℝ (u.val n) w))
  apply ne_top_of_le_ne_top _ hb
  exact ENNReal.mul_ne_top (by simp) (energySmooth_projected_energy_ne_top u n L hL)

lemma reflectedEnergy_ne_top {k m : ℕ} (hm : 0 < m) (u : GradEnergySmooth k m)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (p : ℂ) (n : ZMod (2*m))
    {A : Set ℂ} (hA : MeasurableSet A)
    (hAout : ∀ z ∈ A, 1 < ‖endChart p m z‖) :
    (∫⁻ z in A, reflectedEnergy u.val L p n z ∂volume) ≠ ⊤ := by
  let N : Set ℂ := {w | 1 < ‖w‖}
  have hN : MeasurableSet N := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hb := lintegral_energy_reflected_endChart_le p hm hA hN
    (by rintro _ ⟨z, hz, rfl⟩; exact hAout z hz)
    (by intro w hw; exact norm_pos_iff.mp (lt_trans zero_lt_one hw))
    (fun w => L.comp (fderiv ℝ (u.val n) w))
  have hsub : Bracket.σ '' N ⊆ (KsIndex.WeakH1.disk : Set ℂ) := by
    rintro _ ⟨w, hw, rfl⟩
    have hn : ‖Bracket.σ w‖ < 1 := by
      rw [Bracket.norm_σ]
      exact inv_lt_one_of_one_lt₀ hw
    simpa [KsIndex.WeakH1.disk, Metric.mem_ball, dist_zero_right] using hn
  have hfin : (∫⁻ w in Bracket.σ '' N,
      ENNReal.ofReal (‖L.comp (fderiv ℝ (u.val n) w)‖^2) ∂volume) ≠ ⊤ :=
    ne_top_of_le_ne_top (energySmooth_projected_energy_ne_top u n L hL)
      (lintegral_mono_set hsub)
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hfin) hb

/-- Assemble finite energy from the actual derivative's direct/reflected
branch identities. The pulled-back circle is discarded only via its proved nullity. -/
theorem energy_ne_top_of_branch_derivatives {k m : ℕ} (hm : 0 < m)
    (u : GradEnergySmooth k m) (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (p : ℂ) (R : ℝ)
    (D : ℂ → (ℂ →L[ℝ] ℝ))
    (hdi : ∀ z ∈ puncturedDisk R, ‖endChart p m z‖ < 1 → ∃ n,
      D z = (L.comp (fderiv ℝ (u.val n) (endChart p m z))).comp (endDeriv m z))
    (hdo : ∀ z ∈ puncturedDisk R, 1 < ‖endChart p m z‖ → ∃ n,
      D z = ((L.comp (fderiv ℝ (u.val n) (Bracket.σ (endChart p m z)))).comp
        (fderiv ℝ Bracket.σ (endChart p m z))).comp (endDeriv m z)) :
    (∫⁻ z in puncturedDisk R, ENNReal.ofReal (‖D z‖^2) ∂volume) ≠ ⊤ := by
  let : NeZero (2*m) := ⟨by omega⟩
  let A := puncturedDisk R ∩ {z | ‖endChart p m z‖ < 1}
  let B := puncturedDisk R ∩ {z | 1 < ‖endChart p m z‖}
  have hc : Continuous (fun z => ‖endChart p m z‖) := by unfold endChart; fun_prop
  have hA : MeasurableSet A :=
    (measurableSet_puncturedDisk R).inter (isOpen_lt hc continuous_const).measurableSet
  have hB : MeasurableSet B :=
    (measurableSet_puncturedDisk R).inter (isOpen_lt continuous_const hc).measurableSet
  have hfinA : (∫⁻ z in A, ENNReal.ofReal (‖D z‖^2) ∂volume) ≠ ⊤ := by
    apply lintegral_ne_top_of_finite_choices _ (directEnergy u.val L p)
      (measurable_directEnergy u.val L p)
      (fun n => directEnergy_ne_top hm u L hL p n hA (fun z hz => hz.2))
    filter_upwards [ae_restrict_mem hA] with z hz
    obtain ⟨n, hn⟩ := hdi z hz.1 hz.2
    exact ⟨n, by rw [hn]; exact le_rfl⟩
  have hfinB : (∫⁻ z in B, ENNReal.ofReal (‖D z‖^2) ∂volume) ≠ ⊤ := by
    apply lintegral_ne_top_of_finite_choices _ (reflectedEnergy u.val L p)
      (measurable_reflectedEnergy u.val L p)
      (fun n => reflectedEnergy_ne_top hm u L hL p n hB (fun z hz => hz.2))
    filter_upwards [ae_restrict_mem hB] with z hz
    obtain ⟨n, hn⟩ := hdo z hz.1 hz.2
    exact ⟨n, by rw [hn]; exact le_rfl⟩
  have heq : puncturedDisk R =ᵐ[volume] A ∪ B := by
    have hae : ∀ᵐ z : ℂ ∂volume, ‖endChart p m z‖ ≠ 1 :=
      compl_mem_ae_iff.mpr (volume_endChart_seam_eq_zero p hm)
    filter_upwards [hae] with z hz
    apply propext
    constructor
    · intro h
      rcases lt_or_gt_of_ne hz with hi | ho
      · exact Or.inl ⟨h, hi⟩
      · exact Or.inr ⟨h, ho⟩
    · rintro (h | h) <;> exact h.1
  rw [Measure.restrict_congr_set heq]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfinA, hfinB⟩)
    (lintegral_union_le _ A B)

/-- The complete analytic bundle for a field whose derivatives agree with
the actual finite family of copy pullbacks off the seam. -/
theorem memLp_complex_jet_of_branch_derivatives {k m : ℕ} (hm : 0 < m)
    (u : GradEnergySmooth k m) (p : ℂ) {R r₀ : ℝ} (hR : 0 < R) (hRr : R < r₀)
    (F : ℂ → ℂ)
    (hsm : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r₀ → ContDiffAt ℝ 2 F z)
    (hdi : ∀ z ∈ puncturedDisk R, ‖endChart p m z‖ < 1 → ∃ n,
      fderiv ℝ F z = (fderiv ℝ (u.val n) (endChart p m z)).comp (endDeriv m z))
    (hdo : ∀ z ∈ puncturedDisk R, 1 < ‖endChart p m z‖ → ∃ n,
      fderiv ℝ F z = ((fderiv ℝ (u.val n) (Bracket.σ (endChart p m z))).comp
        (fderiv ℝ Bracket.σ (endChart p m z))).comp (endDeriv m z)) :
    MemLp F 2 (volume.restrict (Metric.ball (0 : ℂ) R)) ∧
    MemLp (KsIndex.PunctureRemoval.gradEnc (fun z => (F z).re)) 2
      (volume.restrict (Metric.ball (0 : ℂ) R)) ∧
    MemLp (KsIndex.PunctureRemoval.gradEnc (fun z => (F z).im)) 2
      (volume.restrict (Metric.ball (0 : ℂ) R)) := by
  have hproj : ∀ L : ℂ →L[ℝ] ℝ, ‖L‖ ≤ 1 →
      (∫⁻ z in puncturedDisk R, ENNReal.ofReal
        (‖fderiv ℝ (fun w => L (F w)) z‖^2) ∂volume) ≠ ⊤ := by
    intro L hL
    have hdf : ∀ z ∈ puncturedDisk R,
        fderiv ℝ (fun w => L (F w)) z = L.comp (fderiv ℝ F z) := by
      intro z hz
      exact (L.hasFDerivAt.comp z
        ((hsm z hz.1 (lt_of_le_of_lt hz.2 hRr)).differentiableAt
          (by norm_num)).hasFDerivAt).fderiv
    apply energy_ne_top_of_branch_derivatives hm u L hL p R
    · intro z hz hi
      obtain ⟨n, hn⟩ := hdi z hz hi
      exact ⟨n, by rw [hdf z hz, hn]; rfl⟩
    · intro z hz ho
      obtain ⟨n, hn⟩ := hdo z hz ho
      exact ⟨n, by rw [hdf z hz, hn]; rfl⟩
  have hRe : ‖Complex.reCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa using Complex.abs_re_le_norm z
  have hIm : ‖Complex.imCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa using Complex.abs_im_le_norm z
  apply memLp_complex_jet_ball_of_component_energy hR hRr F hsm
  · simpa [ENNReal.ofReal_pow, enorm] using hproj Complex.reCLM hRe
  · simpa [ENNReal.ofReal_pow, enorm] using hproj Complex.imCLM hIm

end KsIndex.EndChart
