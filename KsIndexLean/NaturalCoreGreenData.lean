module

public import KsIndexLean.SmoothDiskGreen

@[expose] public section


noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk KsIndex.GradOrtho KsIndex.Surface

lemma weakJacobi_C1_test_green (V : BoundedRealPotential)
    (u v : ℂ → ℂ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ 1 v)
    (vH1 : ComplexH1)
    (hval : valueCLM vH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] v)
    (hdx : dxCLM vH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun w => fderiv ℝ v w 1))
    (hdy : dyCLM vH1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun w => fderiv ℝ v w Complex.I))
    (hjac : ∀ w ∈ (WeakH1.disk : Set ℂ), laplacian u w + (V.V w : ℂ) * u w = 0) :
    weakJacobi V (globalSmoothH1 u hu) vH1 =
      ∫ w : Circle₁, (starRingEnd ℂ) (fderiv ℝ u w w) * v w ∂circleMeasure := by
  have hp : Integrable (fun w => (V.V w : ℂ) * (starRingEnd ℂ) (u w) * v w)
      (volume.restrict (WeakH1.disk : Set ℂ)) := by
    apply (potential_integrable V (globalSmoothH1 u hu) vH1).congr
    filter_upwards [globalSmoothH1_value u hu, hval] with w h1 h2
    rw [h1, h2]
  have hg : Integrable (gradInner u v) (volume.restrict (WeakH1.disk : Set ℂ)) := by
    apply (dirichlet_integrable (globalSmoothH1 u hu) vH1).congr
    filter_upwards [globalSmoothH1_dx u hu, globalSmoothH1_dy u hu,
      hdx, hdy] with w h1 h2 h3 h4
    simp only [gradInner, h1, h2, h3, h4]
  rw [weakJacobi_integral_representatives V _ _ (globalSmoothH1_value u hu)
    (hval) (globalSmoothH1_dx u hu) (globalSmoothH1_dy u hu)
    (hdx) (hdy)]
  change (∫ w in (WeakH1.disk : Set ℂ), gradInner u v w) - _ = _
  rw [← integral_sub hg hp, ← first_green_global u v hu hv]
  apply setIntegral_congr_fun WeakH1.disk.isOpen.measurableSet
  intro w hw
  have hl : laplacian u w = -((V.V w : ℂ) * u w) := eq_neg_of_add_eq_zero_left (hjac w hw)
  dsimp only
  rw [hl, map_neg, map_mul, Complex.conj_ofReal]
  ring

/-- The existing natural-core extension supplies precisely the C1 data needed
for testing Green's identity: actual weak value, both derivatives, and trace. -/
lemma naturalCoreH1_C1_representative {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool}
    (f : NatCc k b1 b0) :
    ∃ G : ℂ → ℂ, ContDiff ℝ 1 G ∧
      (valueCLM (naturalCoreH1 hk f) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] G) ∧
      (dxCLM (naturalCoreH1 hk f) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
        (fun w => fderiv ℝ G w 1)) ∧
      (dyCLM (naturalCoreH1 hk f) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
        (fun w => fderiv ℝ G w Complex.I)) ∧
      ((diskTraceCLM (naturalCoreH1 hk f) : Circle₁ → ℂ) =ᵐ[circleMeasure]
        (fun w => G w)) := by
  obtain ⟨G, hG, he⟩ := KsIndex.SeamUpper.natCc_extension hk f.property
  have hd : ∀ w ∈ (WeakH1.disk : Set ℂ), fderiv ℝ f.val w = fderiv ℝ G w := by
    intro w hw
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [WeakH1.disk.isOpen.mem_nhds hw] with z hz
    exact he z hz
  have hv : valueCLM (naturalCoreH1 hk f) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] G := by
    filter_upwards [naturalCoreH1_value_ae hk f,
      ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with w hw hmem
    exact hw.trans (he w hmem)
  refine ⟨G, hG, hv, ?_, ?_, diskTrace_coe_ae hG.continuous.continuousOn hv⟩
  · filter_upwards [naturalCoreH1_dx_ae hk f,
      ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with w hw hmem
    exact hw.trans (congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) (hd w hmem))
  · filter_upwards [naturalCoreH1_dy_ae hk f,
      ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with w hw hmem
    exact hw.trans (congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) (hd w hmem))

/-- The vertical flux identity on every actual natural-core test, with its
true weak trace. This core is the input to the established density theorem. -/
lemma verticalThree_naturalCore_green {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool}
    (f : NatCc k b1 b0) :
    weakJacobi (surfacePotential 3) verticalThreeH1 (naturalCoreH1 hk f) =
      (2 : ℂ) * ∫ w : Circle₁, diskTraceCLM (naturalCoreH1 hk f) w ∂circleMeasure := by
  obtain ⟨G, hG, hv, hx, hy, ht⟩ := naturalCoreH1_C1_representative hk f
  have h := weakJacobi_C1_test_green (surfacePotential 3) (JacobiFields.nu3 3) G
    (JacobiFields.nu3_contDiff 3 (by decide)) hG (naturalCoreH1 hk f) hv hx hy
    (fun w _ => JacobiFields.jacobi_nu3 3 (by decide) w)
  change weakJacobi (surfacePotential 3)
    (globalSmoothH1 (JacobiFields.nu3 3) (JacobiFields.nu3_contDiff 3 (by decide))) _ = _
  rw [h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ht] with w hw
  rw [hw, verticalThree_normal (by simpa [Metric.mem_sphere, dist_zero_right] using w.property),
    map_ofNat]

end KsIndex.Trace
