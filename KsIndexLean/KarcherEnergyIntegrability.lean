module

public import KsIndexLean.KarcherGlobalForm
public import KsIndexLean.KarcherTestFunctionTransport

@[expose] public section


/-! Integrability of the disk-coordinate energy densities of compact smooth
quotient functions. Zero extension across the circle is used only almost
 everywhere; no smoothness of that extension on the circle is asserted. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace KsIndex.KarcherData

lemma ae_norm_ne_one : ∀ᵐ w : ℂ ∂volume, ‖w‖ ≠ 1 := by
  apply ae_iff.mpr
  simpa only [not_not, ← mem_sphere_zero_iff_norm, Set.ofPred_mem_eq] using
    (Measure.addHaar_sphere (volume : Measure ℂ) 0 1)

lemma ae_eq_disk_indicator {E : Type*} [Zero E] (f : ℂ → E)
    (he : ∀ w, 1 < ‖w‖ → f w = 0) :
    f =ᵐ[volume] Surface.disk.indicator f := by
  filter_upwards [ae_norm_ne_one] with w hw
  by_cases hd : w ∈ Surface.disk
  · simp [hd]
  · have hgt : 1 < ‖w‖ := lt_of_le_of_ne
      (le_of_not_gt (fun h => hd ((show w ∈ Surface.disk from by simpa [Surface.disk, Metric.mem_ball, dist_zero_right] using h)))) hw.symm
    simp [hd, he w hgt]

lemma fderiv_eq_zero_of_exterior (f : ℂ → ℂ)
    (he : ∀ z, 1 < ‖z‖ → f z = 0) {w : ℂ} (hw : 1 < ‖w‖) :
    fderiv ℝ f w = 0 := by
  have hnb : ∀ᶠ z in 𝓝 w, 1 < ‖z‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hw
  have hg : f =ᶠ[𝓝 w] (fun _ => (0 : ℂ)) := hnb.mono fun z hz => he z hz
  rw [hg.fderiv_eq]
  simp

lemma integrable_gradSq_of_regular {m : ℕ} {u : ZMod (2*m) → ℂ → ℂ}
    (hu : SurfaceForm.Regular u) (he : ∀ n w, 1 < ‖w‖ → u n w = 0)
    (n : ZMod (2*m)) : Integrable (Surface.gradSq (u n)) := by
  have hi : IntegrableOn (Surface.gradSq (u n)) Surface.disk := by
    have h := (SurfaceForm.integrableOn_gradInner hu hu n).re
    change IntegrableOn (fun w => (GradOrtho.gradInner (u n) (u n) w).re) Surface.disk at h
    simpa only [GradOrtho.gradInner_self, Complex.ofReal_re] using h
  apply (hi.integrable_indicator Metric.isOpen_ball.measurableSet).congr
  apply (ae_eq_disk_indicator _ ?_).symm
  intro w hw
  simp [Surface.gradSq, fderiv_eq_zero_of_exterior (u n) (he n) hw]

lemma integrable_potential_of_regular {k m : ℕ} {u : ZMod (2*m) → ℂ → ℂ}
    (hu : SurfaceForm.Regular u) (he : ∀ n w, 1 < ‖w‖ → u n w = 0)
    (n : ZMod (2*m)) : Integrable (fun w => Surface.potV k w * ‖u n w‖ ^ 2) := by
  have hi : IntegrableOn (fun w => Surface.potV k w * ‖u n w‖ ^ 2) Surface.disk := by
    have h := (SurfaceForm.integrableOn_potDens (k := k) hu hu n).re
    have hid : (fun w => ((Surface.potV k w : ℂ) * (starRingEnd ℂ) (u n w) * u n w).re)
        = (fun w => Surface.potV k w * ‖u n w‖ ^ 2) := by
      funext w
      rw [mul_assoc, Complex.conj_mul']
      norm_cast
    change IntegrableOn (fun w => ((Surface.potV k w : ℂ) * (starRingEnd ℂ) (u n w) * u n w).re) Surface.disk at h
    rwa [hid] at h
  apply (hi.integrable_indicator Metric.isOpen_ball.measurableSet).congr
  apply (ae_eq_disk_indicator _ ?_).symm
  intro w hw
  simp [he n w hw]

namespace PaperHalfPeriodRealization
open scoped ContDiff Manifold ParameterAtlas
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)
  (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)

lemma encoding_energy_integrable
    (hu : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.CcSmooth k m)
    (n : ZMod (2*m)) :
    Integrable (Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n)) ∧
    Integrable (fun w => Surface.potV k w *
      ‖encodeDiskFunction (R.diskFunctionPullback G) n w‖ ^ 2) := by
  have hr := SurfaceForm.regular_of_mem hu
  exact ⟨integrable_gradSq_of_regular hr (encodeDiskFunction_exterior _) n,
    integrable_potential_of_regular hr (encodeDiskFunction_exterior _) n⟩

lemma compactSmooth_energy_integrable :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G → HasCompactSupport G →
    ∀ n : ZMod (2*m),
    Integrable (Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n)) ∧
    Integrable (fun w => Surface.potV k w *
      ‖encodeDiskFunction (R.diskFunctionPullback G) n w‖ ^ 2) := by
  intro hs hc n
  exact R.encoding_energy_integrable G
    ((R.compactSmooth_iff_encoding_mem_CcSmooth G).mp ⟨hs, hc⟩) n

lemma encoding_energy_lt_top
    (hu : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.CcSmooth k m) :
    ewDirichletEnergyFlat R G < ⊤ ∧ ewPotentialEnergyFlat R G < ⊤ := by
  constructor
  · apply ENNReal.sum_lt_top.mpr
    intro n _
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun w => ?_)).mp
      (R.encoding_energy_integrable G hu n).1.hasFiniteIntegral
    unfold Surface.gradSq
    positivity
  · apply ENNReal.sum_lt_top.mpr
    intro n _
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun w => ?_)).mp
      (R.encoding_energy_integrable G hu n).2.hasFiniteIntegral
    exact mul_nonneg (SurfaceForm.potV_nonneg k w) (sq_nonneg _)

lemma compactSmooth_energy_lt_top :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G → HasCompactSupport G →
    ewDirichletEnergyGeom R G < ⊤ ∧ ewPotentialEnergyGeom R G < ⊤ := by
  let := HeightLift.periodChartedSpace R.hC m
  intro hs hc
  rw [R.ewDirichletEnergyGeom_eq_flat G, R.ewPotentialEnergyGeom_eq_flat G hs.continuous]
  exact R.encoding_energy_lt_top G
    ((R.compactSmooth_iff_encoding_mem_CcSmooth G).mp ⟨hs, hc⟩)

end PaperHalfPeriodRealization
end KsIndex.KarcherData
