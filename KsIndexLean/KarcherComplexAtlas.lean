module

public import KsIndexLean.KarcherActualChartOverlap
public import KsIndexLean.KarcherConformalOrientation

@[expose] public section


/-! Complex differentiability of the actual lifted finite/infinity atlas. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData.ParameterAtlas

scoped instance sphereComplexManifold : IsManifold 𝓘(ℂ, ℂ) ∞ Spherical.Sphere := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ ({finite, infinity} : Set _) at he
  change e' ∈ ({finite, infinity} : Set _) at he'
  simp only [mem_insert_iff, mem_singleton_iff] at he he'
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl
  · intro z hz
    simp only [mfld_simps] at hz ⊢
    have he : (fun w => finite (finite.symm w)) = fun w : ℂ => w := by
      funext w; exact finite_apply w
    simp only [Function.comp_def]
    rw [he]
    exact contDiffAt_id.contDiffWithinAt
  · intro z hz
    simp only [mfld_simps] at hz ⊢
    have hn : z ≠ 0 := by rintro rfl; exact finite_zero_not_infinity hz.2
    exact ((contDiffAt_id.inv hn).contDiffWithinAt).congr
      (fun w hw => infinity_finite_change hw.2) (infinity_finite_change hz.2)
  · intro z hz
    simp only [mfld_simps] at hz ⊢
    have hn : z ≠ 0 := by rintro rfl; exact infinity_zero_not_finite hz.2
    exact ((contDiffAt_id.inv hn).contDiffWithinAt).congr
      (fun w hw => finite_infinity_change hw.2) (finite_infinity_change hz.2)
  · intro z hz
    simp only [mfld_simps] at hz ⊢
    have he : (fun w => infinity (infinity.symm w)) = fun w : ℂ => w := by
      funext w; exact infinity_apply w
    simp only [Function.comp_def]
    rw [he]
    exact contDiffAt_id.contDiffWithinAt

scoped instance parameterComplexManifold {k : ℕ} [h : Fact (2 ≤ k)] :
    IsManifold 𝓘(ℂ, ℂ) ∞ (ParameterSphere k) :=
  inferInstanceAs (IsManifold 𝓘(ℂ, ℂ) ∞ (parameterOpen h.out))

end KsIndex.KarcherData.ParameterAtlas

namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} [TopologicalSpace P] [ChartedSpace ℂ P]
variable {F : P → PeriodTarget} (hF : Continuous F)

theorem liftComplexManifold [IsManifold 𝓘(ℂ, ℂ) ∞ P] :
    @IsManifold ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ, ℂ) ∞ (HeightLift F) _ (liftChartedSpace hF) := by
  let := liftChartedSpace hF
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨r, rfl⟩ := he'
  intro z hz
  simp only [mfld_simps] at hz ⊢
  have hzq : z ∈ (chartAt ℂ (projection q)).target := hz.1.1
  have hzr : (chartAt ℂ (projection q)).symm z ∈ (chartAt ℂ (projection r)).source := by
    have hr := hz.2.2
    simp only [Set.mem_preimage, OpenPartialHomeomorph.symm_symm,
      IsLocalHomeomorph.localInverseAt_symm] at hr
    rwa [liftChart_symm_projection hF hz.1] at hr
  have h1 := (contMDiffOn_chart_symm (I := 𝓘(ℂ, ℂ)) (n := ∞) (x := projection q)).contMDiffAt
    ((chartAt ℂ (projection q)).open_target.mem_nhds hzq)
  have h2 := (contMDiffOn_chart (I := 𝓘(ℂ, ℂ)) (n := ∞) (x := projection r)).contMDiffAt
    ((chartAt ℂ (projection r)).open_source.mem_nhds hzr)
  have hs := (h2.comp z h1).contDiffAt
  apply hs.contDiffWithinAt.congr
  · intro w hw
    exact liftChart_transition hF hw
  · exact liftChart_transition hF hz

end KsIndex.KarcherData.HeightLift

open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

theorem chartTransition_complex_contDiffAt (R : PaperHalfPeriodRealization k)
    (q r : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) {z : ℂ}
    (hz : z ∈ ((HeightLift.liftChart R.hC q).symm.trans
      (HeightLift.liftChart R.hC r)).source) :
    ContDiffAt ℂ ∞ (HeightLift.liftChart R.hC r ∘ (HeightLift.liftChart R.hC q).symm) z := by
  let := HeightLift.liftChartedSpace R.hC
  let := HeightLift.liftComplexManifold R.hC
  have hi := (contMDiffOn_chart_symm (I := 𝓘(ℂ, ℂ)) (n := ∞) (x := q)).contMDiffAt
    ((HeightLift.liftChart R.hC q).open_target.mem_nhds hz.1)
  have hj := (contMDiffOn_chart (I := 𝓘(ℂ, ℂ)) (n := ∞) (x := r)).contMDiffAt
    ((HeightLift.liftChart R.hC r).open_source.mem_nhds hz.2)
  exact (hj.comp z hi).contDiffAt

/-- The actual transition has a nonzero complex derivative, as follows from
its holomorphic inverse on the registered overlap. -/
theorem chartTransition_deriv_ne_zero (R : PaperHalfPeriodRealization k)
    (q r : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) {z : ℂ}
    (hz : z ∈ ((HeightLift.liftChart R.hC q).symm.trans
      (HeightLift.liftChart R.hC r)).source) :
    deriv (HeightLift.liftChart R.hC r ∘ (HeightLift.liftChart R.hC q).symm) z ≠ 0 := by
  let e := HeightLift.liftChart R.hC q
  let f := HeightLift.liftChart R.hC r
  have hz' : z ∈ e.target ∧ e.symm z ∈ f.source := hz
  have hrev : f (e.symm z) ∈ (f.symm.trans e).source := by
    refine ⟨f.map_source hz'.2, ?_⟩
    change f.symm (f (e.symm z)) ∈ e.source
    rw [f.left_inv hz'.2]
    exact e.map_target hz'.1
  have hd := (R.chartTransition_complex_contDiffAt q r hz).differentiableAt (by simp)
  have hi := (R.chartTransition_complex_contDiffAt r q hrev).differentiableAt (by simp)
  have he : ((e ∘ f.symm) ∘ (f ∘ e.symm)) =ᶠ[𝓝 z] (fun w : ℂ => w) := by
    filter_upwards [(e.symm.trans f).open_source.mem_nhds hz] with w hw
    have hw' : w ∈ e.target ∧ e.symm w ∈ f.source := hw
    exact (congrArg e (f.left_inv hw'.2)).trans (e.right_inv hw'.1)
  have hh := (hi.hasDerivAt.comp z hd.hasDerivAt).deriv
  rw [he.deriv_eq, deriv_id''] at hh
  intro hn
  rw [hn, mul_zero] at hh
  exact one_ne_zero hh

/-- The oriented normal agrees on every actual registered chart overlap. -/
theorem chartUnitNormal_chart_overlap (R : PaperHalfPeriodRealization k)
    (q r : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) {z : ℂ}
    (hz : z ∈ ((HeightLift.liftChart R.hC q).symm.trans
      (HeightLift.liftChart R.hC r)).source) :
    chartUnitNormal (R.centeredChart q) z =
      chartUnitNormal (R.centeredChart r)
        (HeightLift.liftChart R.hC r ((HeightLift.liftChart R.hC q).symm z)) := by
  let c := HeightLift.liftChart R.hC r ∘ (HeightLift.liftChart R.hC q).symm
  have hd := (R.chartTransition_complex_contDiffAt q r hz).differentiableAt (by simp)
  have hX := (R.centeredChart_contDiffAt r
    ((HeightLift.liftChart R.hC r).map_source hz.2)).differentiableAt (by simp)
  rw [chartUnitNormal_germ (R.centeredChart_overlap_germ q r hz)]
  apply chartUnitNormal_comp_complex hX (hd.restrictScalars ℝ)
    (R.chartTransition_deriv_ne_zero q r hz)
  intro v
  rw [(hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp [mul_comm]

/-- The normal of an actual chart agrees with the global normal throughout
its target, not only at the selected chart center. -/
theorem chartUnitNormal_eq_global (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) {z : ℂ}
    (hz : z ∈ (HeightLift.liftChart R.hC q).target) :
    chartUnitNormal (R.centeredChart q) z =
      R.normal ((HeightLift.liftChart R.hC q).symm z) := by
  let p := (HeightLift.liftChart R.hC q).symm z
  have hp := HeightLift.liftChart_mem R.hC p
  have he := R.chartUnitNormal_chart_overlap q p (show z ∈
    ((HeightLift.liftChart R.hC q).symm.trans (HeightLift.liftChart R.hC p)).source
    from ⟨hz, hp⟩)
  exact he.trans (R.normal_eq_centeredChart p).symm

end KsIndex.KarcherData.PaperHalfPeriodRealization
