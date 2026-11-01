module

public import KsIndexLean.WeakRealEquation
public import KsIndexLean.GammaRemovability
public import KsIndexLean.GammaAssembly

@[expose] public section


/-! Finite-energy punctured solutions have bounded representatives near the puncture.
This connects removability to the proved interior Sobolev regularity engine. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BoundedContinuousFunction

namespace KsIndex.PunctureRemoval

theorem exists_boundedContinuous_cutoff_of_smooth_punctured
    {Ω : Opens ℂ} {z₀ : ℂ} {V f : ℂ → ℝ} {C : ℝ}
    (hV : ∀ z ∈ Ω.carrier, |V z| ≤ C) (hVm : Measurable V)
    (hsm : ∀ z ∈ Ω.carrier \ {z₀}, ContDiffAt ℝ 2 f z)
    (heq : ∀ z ∈ Ω.carrier \ {z₀}, lapReal f z + V z * f z = 0)
    (hu2 : MemLp f 2 (volume.restrict Ω.carrier))
    (hg2 : MemLp (gradEnc f) 2 (volume.restrict Ω.carrier))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ω.carrier) :
    ∃ g : ℂ →ᵇ ℂ, (fun z => χ z • (f z : ℂ)) =ᵐ[volume] g := by
  obtain ⟨u, hsol, hval, _⟩ := exists_w1p_isWeakSolOn_of_smooth_punctured
    (fun K hK _ => ⟨C, fun z hz => hV z (hK hz)⟩) hVm hsm heq hu2 hg2
  have hq : MemLp (fun z => V z * TauCeti.W1p.value u z) 2
      (volume.restrict (Ω : Set ℂ)) := by
    apply (Lp.memLp (TauCeti.W1p.value u)).of_le_mul (c := C)
      (hVm.aestronglyMeasurable.mul (Lp.memLp (TauCeti.W1p.value u)).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with z hz
    change ‖V z * TauCeti.W1p.value u z‖ ≤ C * ‖TauCeti.W1p.value u z‖
    rw [norm_mul, Real.norm_eq_abs (V z)]
    exact mul_le_mul_of_nonneg_right (hV z hz) (norm_nonneg _)
  obtain ⟨g, hgu⟩ := Weq.exists_boundedContinuous_cutoff_of_isWeakSolOn u hq hsol hχ hc hs
  refine ⟨g, Filter.EventuallyEq.trans ?_ hgu⟩
  have hv := (ae_restrict_iff' Ω.isOpen.measurableSet).mp hval
  filter_upwards [hv] with z hz
  by_cases hzΩ : z ∈ Ω.carrier
  · rw [hz hzΩ]
  · have hzχ : z ∉ tsupport χ := fun ht => hzΩ (hs ht)
    simp [image_eq_zero_of_notMem_tsupport hzχ]

/-- A cutoff equal to one on an open punctured neighborhood transfers the
continuous representative's bound to the original classical solution pointwise. -/
theorem bounded_on_cutoff_of_smooth_punctured
    {Ω : Opens ℂ} {z₀ : ℂ} {V f : ℂ → ℝ} {C : ℝ}
    (hV : ∀ z ∈ Ω.carrier, |V z| ≤ C) (hVm : Measurable V)
    (hsm : ∀ z ∈ Ω.carrier \ {z₀}, ContDiffAt ℝ 2 f z)
    (heq : ∀ z ∈ Ω.carrier \ {z₀}, lapReal f z + V z * f z = 0)
    (hu2 : MemLp f 2 (volume.restrict Ω.carrier))
    (hg2 : MemLp (gradEnc f) 2 (volume.restrict Ω.carrier))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ω.carrier) {S : Set ℂ} (hS : IsOpen S)
    (hSΩ : S ⊆ Ω.carrier \ {z₀}) (hχone : ∀ z ∈ S, χ z = 1) :
    ∃ M : ℝ, ∀ z ∈ S, |f z| ≤ M := by
  obtain ⟨g, hg⟩ := exists_boundedContinuous_cutoff_of_smooth_punctured
    hV hVm hsm heq hu2 hg2 hχ hc hs
  have hfg : (fun z => (f z : ℂ)) =ᵐ[volume.restrict S] g := by
    filter_upwards [ae_restrict_of_ae hg, ae_restrict_mem hS.measurableSet] with z hz hzS
    simpa only [hχone z hzS, one_smul] using hz
  have hf : ContinuousOn (fun z => (f z : ℂ)) S :=
    fun z hz => (Complex.continuous_ofReal.continuousAt.comp
      (hsm z (hSΩ hz)).continuousAt).continuousWithinAt
  have he := Measure.eqOn_open_of_ae_eq hfg hS hf g.continuous.continuousOn
  refine ⟨‖g‖, fun z hz => ?_⟩
  have hb := g.norm_coe_le_norm z
  rw [← he hz] at hb
  simpa using hb

/-- Local boundedness near the removed point, with precisely the local-potential
and finite-energy assumptions of the removability theorem. The cutoff and the
smaller neighborhood are constructed, rather than assumed. -/
theorem bounded_near_of_smooth_punctured
    {Ω : Opens ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω.carrier) {V f : ℂ → ℝ}
    (hV : ∀ K, K ⊆ Ω.carrier → IsCompact K → ∃ C, ∀ z ∈ K, |V z| ≤ C)
    (hVm : Measurable V)
    (hsm : ∀ z ∈ Ω.carrier \ {z₀}, ContDiffAt ℝ 2 f z)
    (heq : ∀ z ∈ Ω.carrier \ {z₀}, lapReal f z + V z * f z = 0)
    (hu2 : MemLp f 2 (volume.restrict Ω.carrier))
    (hg2 : MemLp (gradEnc f) 2 (volume.restrict Ω.carrier)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ z, dist z z₀ < δ → z ≠ z₀ → |f z| ≤ M := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds hz₀)
  let Ω' : Opens ℂ := ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩
  have hΩ : Ω'.carrier ⊆ Ω.carrier := Metric.ball_subset_closedBall.trans hsub
  obtain ⟨C, hC⟩ := hV (Metric.closedBall z₀ r) hsub (isCompact_closedBall _ _)
  let χ : ContDiffBump z₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hχs : tsupport (χ : ℂ → ℝ) ⊆ Ω'.carrier := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by change r / 2 < r; linarith)
  let S := Metric.ball z₀ (r / 4) \ {z₀}
  have hS : IsOpen S := Metric.isOpen_ball.sdiff isClosed_singleton
  have hSΩ : S ⊆ Ω'.carrier \ {z₀} := by
    intro z hz
    exact ⟨Metric.ball_subset_ball (by linarith) hz.1, hz.2⟩
  have hsm' : ∀ z ∈ Ω'.carrier \ {z₀}, ContDiffAt ℝ 2 f z :=
    fun z hz => hsm z ⟨hΩ hz.1, hz.2⟩
  obtain ⟨M, hM⟩ := bounded_on_cutoff_of_smooth_punctured
    (Ω := Ω') (fun z hz => hC z (Metric.ball_subset_closedBall hz)) hVm hsm'
    (fun z hz => heq z ⟨hΩ hz.1, hz.2⟩)
    (hu2.mono_measure (Measure.restrict_mono hΩ le_rfl))
    (hg2.mono_measure (Measure.restrict_mono hΩ le_rfl))
    χ.contDiff χ.hasCompactSupport hχs hS hSΩ
    (fun z hz => χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz.1))
  exact ⟨r / 4, by positivity, M, fun z hz hne => hM z ⟨hz, hne⟩⟩

/-- The componentwise version used by complex Jacobi end fields. -/
theorem bounded_near_complex_of_smooth_punctured
    {Ω : Opens ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Ω.carrier) {V : ℂ → ℝ} {F : ℂ → ℂ}
    (hV : ∀ K, K ⊆ Ω.carrier → IsCompact K → ∃ C, ∀ z ∈ K, |V z| ≤ C)
    (hVm : Measurable V)
    (hsm : ∀ z ∈ Ω.carrier \ {z₀}, ContDiffAt ℝ 2 F z)
    (hre : ∀ z ∈ Ω.carrier \ {z₀},
      lapReal (fun w => (F w).re) z + V z * (F z).re = 0)
    (him : ∀ z ∈ Ω.carrier \ {z₀},
      lapReal (fun w => (F w).im) z + V z * (F z).im = 0)
    (hu2 : MemLp F 2 (volume.restrict Ω.carrier))
    (hgr : MemLp (gradEnc (fun z => (F z).re)) 2 (volume.restrict Ω.carrier))
    (hgi : MemLp (gradEnc (fun z => (F z).im)) 2 (volume.restrict Ω.carrier)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ z, dist z z₀ < δ → z ≠ z₀ → ‖F z‖ ≤ M := by
  have hsr : ∀ z ∈ Ω.carrier \ {z₀}, ContDiffAt ℝ 2 (fun w => (F w).re) z :=
    fun z hz => Complex.reCLM.contDiff.contDiffAt.comp z (hsm z hz)
  have hsi : ∀ z ∈ Ω.carrier \ {z₀}, ContDiffAt ℝ 2 (fun w => (F w).im) z :=
    fun z hz => Complex.imCLM.contDiff.contDiffAt.comp z (hsm z hz)
  obtain ⟨δr, hδr, Mr, hMr⟩ := bounded_near_of_smooth_punctured hz₀ hV hVm hsr hre hu2.re hgr
  obtain ⟨δi, hδi, Mi, hMi⟩ := bounded_near_of_smooth_punctured hz₀ hV hVm hsi him hu2.im hgi
  refine ⟨min δr δi, lt_min hδr hδi, Mr + Mi, fun z hz hne => ?_⟩
  exact (Complex.norm_le_abs_re_add_abs_im (F z)).trans
    (add_le_add (hMr z (lt_of_lt_of_le hz (min_le_left _ _)) hne)
      (hMi z (lt_of_lt_of_le hz (min_le_right _ _)) hne))

end KsIndex.PunctureRemoval
