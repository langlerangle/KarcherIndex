module

public import KsIndexLean.KarcherEnergyIntegrability

@[expose] public section


/-! The signed copywise Jacobi form on actual quotient functions. Equality
with intrinsic quotient integration is a separate geometric compatibility result. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace KsIndex.KarcherData

lemma integral_eq_disk_of_exterior {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℂ → E)
    (he : ∀ w, 1 < ‖w‖ → f w = 0) :
    ∫ w, f w = ∫ w in Surface.disk, f w := by
  rw [integral_congr_ae (ae_eq_disk_indicator f he),
    integral_indicator SurfaceForm.measurableSet_disk]

namespace PaperHalfPeriodRealization
open scoped ContDiff Manifold ParameterAtlas
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)
  (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)

/-- Difference of the two real energies. On the compact smooth domain both
extended-real inputs are finite, as proved in `compactSmooth_energy_lt_top`. -/
def ewJacobiQ : ℝ := (ewDirichletEnergyGeom R G).toReal - (ewPotentialEnergyGeom R G).toReal

lemma flat_dirichlet_toReal
    (hu : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.CcSmooth k m) :
    (ewDirichletEnergyFlat R G).toReal = ∑ n : ZMod (2*m),
      ∫ w in Surface.disk, Surface.gradSq (encodeDiskFunction (R.diskFunctionPullback G) n) w := by
  unfold ewDirichletEnergyFlat
  rw [ENNReal.toReal_sum (fun n _ => ?_)]
  · apply Finset.sum_congr rfl
    intro n _
    rw [← integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall (fun w => by unfold Surface.gradSq; positivity))
      (R.encoding_energy_integrable G hu n).1.aestronglyMeasurable]
    apply integral_eq_disk_of_exterior
    intro w hw
    simp [Surface.gradSq, fderiv_eq_zero_of_exterior _ (encodeDiskFunction_exterior _ n) hw]
  · exact ne_of_lt ((hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall (fun w => by unfold Surface.gradSq; positivity))).mp
        (R.encoding_energy_integrable G hu n).1.hasFiniteIntegral)

lemma flat_potential_toReal
    (hu : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.CcSmooth k m) :
    (ewPotentialEnergyFlat R G).toReal = ∑ n : ZMod (2*m),
      ∫ w in Surface.disk, Surface.potV k w *
        ‖encodeDiskFunction (R.diskFunctionPullback G) n w‖ ^ 2 := by
  unfold ewPotentialEnergyFlat
  rw [ENNReal.toReal_sum (fun n _ => ?_)]
  · apply Finset.sum_congr rfl
    intro n _
    rw [← integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall (fun w => mul_nonneg (SurfaceForm.potV_nonneg k w) (sq_nonneg _)))
      (R.encoding_energy_integrable G hu n).2.aestronglyMeasurable]
    apply integral_eq_disk_of_exterior
    intro w hw
    simp [encodeDiskFunction_exterior _ n w hw]
  · exact ne_of_lt ((hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall (fun w => mul_nonneg (SurfaceForm.potV_nonneg k w) (sq_nonneg _)))).mp
        (R.encoding_energy_integrable G hu n).2.hasFiniteIntegral)

lemma ewJacobiQ_eq_model (hG : Continuous G)
    (hu : encodeDiskFunction (R.diskFunctionPullback G) ∈ Surface.CcSmooth k m) :
    ewJacobiQ R G = Surface.jacobiQ k m (encodeDiskFunction (R.diskFunctionPullback G)) := by
  rw [ewJacobiQ, R.ewDirichletEnergyGeom_eq_flat G, R.ewPotentialEnergyGeom_eq_flat G hG,
    R.flat_dirichlet_toReal G hu, R.flat_potential_toReal G hu, ← Finset.sum_sub_distrib]
  unfold Surface.jacobiQ
  apply Finset.sum_congr rfl
  intro n _
  exact (Surface.dirichletG_sub_potentialG h.out _).symm

lemma compactSmooth_ewJacobiQ_eq_model :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G → HasCompactSupport G →
    ewJacobiQ R G = Surface.jacobiQ k m (encodeDiskFunction (R.diskFunctionPullback G)) := by
  let := HeightLift.periodChartedSpace R.hC m
  intro hs hc
  exact R.ewJacobiQ_eq_model G hs.continuous
    ((R.compactSmooth_iff_encoding_mem_CcSmooth G).mp ⟨hs, hc⟩)

lemma ewJacobiQ_modelTestFunction (u : Surface.CcSmooth k m) :
    ewJacobiQ R (R.modelTestFunction u.val) = Surface.jacobiQ k m u.val := by
  have hu := R.modelTestFunction_compactSmooth u
  rw [R.compactSmooth_ewJacobiQ_eq_model _ hu.1 hu.2, R.modelTestFunction_modelForm]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
