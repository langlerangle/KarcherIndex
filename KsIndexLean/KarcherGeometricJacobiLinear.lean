module

public import KsIndexLean.KarcherGeometricJacobi

@[expose] public section


/-! Complex linear structure of bounded smooth geometric Jacobi fields. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)
local instance quotientCharted : ChartedSpace ℂ
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :=
  HeightLift.periodChartedSpace R.hC m
local instance quotientSmooth : IsManifold 𝓘(ℝ, ℂ) ∞
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :=
  HeightLift.periodSmoothManifold R.hC m

lemma smooth_quotient_chart_pullback
    (u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    ContDiffAt ℝ ∞
      (u ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm)
      (R.chartCenter q) := by
  let x := HeightLift.periodQuotientMap m q
  have hc : R.chartCenter q = (chartAt ℂ x) x := by
    change HeightLift.liftChart R.hC q q = HeightLift.periodChart R.hC m x x
    rw [HeightLift.liftChart_apply, HeightLift.periodChart_apply]
    rfl
  rw [hc]
  have hs := (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := x)).contMDiffAt
    ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
  exact ((hu _).comp _ hs).contDiffAt

lemma geometricJacobiAt_add
    (u v : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ v)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.geometricJacobiAt (u + v) q = R.geometricJacobiAt u q + R.geometricJacobiAt v q := by
  simp only [R.geometricJacobiAt_eq, Surface.laplacianG]
  change _ * Surface.laplacian
    ((u ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm) +
     (v ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm)) _ + _ = _
  rw [Surface.laplacian_add (R.smooth_quotient_chart_pullback u hu q)
    (R.smooth_quotient_chart_pullback v hv q)]
  simp only [Pi.add_apply]
  ring

lemma geometricJacobiAt_smul
    (c : ℂ)
    (u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.geometricJacobiAt (c • u) q = c * R.geometricJacobiAt u q := by
  simp only [R.geometricJacobiAt_eq, Surface.laplacianG]
  change _ * Surface.laplacian
    (c • (u ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm)) _ + _ = _
  rw [Surface.laplacian_smul c (R.smooth_quotient_chart_pullback u hu q)]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma isBoundedGeometricJacobi_zero :
    R.IsBoundedGeometricJacobi
      (0 : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) := by
  refine ⟨contMDiff_const, ⟨0, fun x => by simp⟩, ?_⟩
  intro q
  simp [R.geometricJacobiAt_eq, Function.comp_def, Surface.laplacianG, Surface.laplacian]

lemma IsBoundedGeometricJacobi.add
    {u v : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ}
    (hu : R.IsBoundedGeometricJacobi u) (hv : R.IsBoundedGeometricJacobi v) :
    R.IsBoundedGeometricJacobi (u + v) := by
  obtain ⟨hsu, ⟨C, hC⟩, hju⟩ := hu
  obtain ⟨hsv, ⟨D, hD⟩, hjv⟩ := hv
  refine ⟨hsu.add hsv, ⟨C + D, ?_⟩, ?_⟩
  · intro x
    exact (norm_add_le _ _).trans (add_le_add (hC x) (hD x))
  · intro q
    rw [R.geometricJacobiAt_add u v hsu hsv q, hju q, hjv q, zero_add]

lemma IsBoundedGeometricJacobi.smul
    (c : ℂ)
    {u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ}
    (hu : R.IsBoundedGeometricJacobi u) : R.IsBoundedGeometricJacobi (c • u) := by
  obtain ⟨hsu, ⟨C, hC⟩, hju⟩ := hu
  have hc : ContDiff ℝ ∞ (fun z : ℂ => c * z) := contDiff_const.mul contDiff_id
  refine ⟨hc.contMDiff.comp hsu, ⟨‖c‖ * C, ?_⟩, ?_⟩
  · intro x
    simpa only [Pi.smul_apply, norm_smul] using
      mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
  · intro q
    rw [R.geometricJacobiAt_smul c u hsu q, hju q, mul_zero]

/-- The complex vector space of bounded smooth Jacobi fields on the actual
EW quotient. No integrability or support condition is included. -/
def boundedGeometricJacobi : Submodule ℂ
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) where
  carrier := {u | R.IsBoundedGeometricJacobi u}
  zero_mem' := R.isBoundedGeometricJacobi_zero
  add_mem' := fun hu hv => IsBoundedGeometricJacobi.add R hu hv
  smul_mem' := fun c _ hu => IsBoundedGeometricJacobi.smul R c hu

@[simp] lemma mem_boundedGeometricJacobi
    (u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    u ∈ R.boundedGeometricJacobi ↔ R.IsBoundedGeometricJacobi u := Iff.rfl

end KsIndex.KarcherData.PaperHalfPeriodRealization
