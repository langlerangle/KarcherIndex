module

public import KsIndexLean.HalfDiskGreen
public import KsIndexLean.MixedHalfDiskFiniteEnergy
public import KsIndexLean.WeakH1Integration

@[expose] public section


/-! Finite energy of bounded classical half-period Jacobi fields, derived
from their equation and one-sided pure boundary conditions. -/
noncomputable section
open Set MeasureTheory Filter Topology Complex Real
namespace KsIndex.Trace.ClassicalHalfDiskJacobi
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.PunctureCutoff KsIndex.FaithfulInjection
variable {k : ℕ} {b : Bool} (u : ClassicalHalfDiskJacobi k b)

/-- The truncated energies have a common bound as puncture cutoffs shrink. -/
theorem uniform_cutoff_energy_bound (hk : 2 ≤ k) :
    ∃ K : ℝ, ∀ {ε : ℝ}, 0 < ε → ε ≤ Real.exp (-1) →
      ∫ w in disk, (cutP k ε w)^(2 : ℕ) * gradSq u.value w ≤ K := by
  exact (ClassicalMixedHalfDiskJacobi.ofPure u).uniform_cutoff_energy_bound hk

/-- No finite-energy assumption is required: it follows by Fatou from the
uniform cutoff estimate. -/
theorem finite_dirichlet_energy (hk : 2 ≤ k) : IntegrableOn (gradSq u.value) disk := by
  exact (ClassicalMixedHalfDiskJacobi.ofPure u).finite_dirichlet_energy hk

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

end KsIndex.Trace.ClassicalHalfDiskJacobi
