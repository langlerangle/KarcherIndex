module

public import KsIndexLean.FiniteDimensionalFourierSupport
public import KsIndexLean.DiskWeakMultiplicity
public import KsIndexLean.SphericalEigenPotential
public import KsIndexLean.DiskRotationForms
public import KsIndexLean.DiskTraceCovariance

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Spectral

lemma weightedDisk_mass_diskRotation (θ : ℝ) (u v : ComplexH1) :
    inner ℂ (weightedDiskValueCLM (diskRotation θ u)) (weightedDiskValueCLM (diskRotation θ v)) =
      inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v) := by
  rw [weightedDisk_mass_eq_potential, weightedDisk_mass_eq_potential]
  apply potential_diskRotation
  filter_upwards [] with z
  change stereoAreaDensity (planeRotation θ z) = stereoAreaDensity z
  simp only [stereoAreaDensity_eq, (planeRotation θ).norm_map]

lemma sphericalEigen_rotation (D : Submodule ℂ ComplexH1)
    (hD : ∀ θ : ℝ, ∀ v ∈ D, diskRotation θ v ∈ D)
    (k : ℕ) (lam θ : ℝ) (u : ComplexH1)
    (hu : ∀ v ∈ D, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    ∀ v ∈ D, weakJacobi (surfacePotential k) (diskRotation θ u) v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM (diskRotation θ u)) (weightedDiskValueCLM v) := by
  intro v hv
  have he : diskRotation θ (diskRotation (-θ) v) = v := by
    rw [← diskRotation_add, add_neg_cancel, diskRotation_zero]
  have hq := surfaceJacobi_diskRotation k θ u (diskRotation (-θ) v)
  have hm := weightedDisk_mass_diskRotation θ u (diskRotation (-θ) v)
  rw [he] at hq hm
  rw [hq, hm]
  exact hu _ (hD (-θ) v hv)

variable (D : Submodule ℂ ComplexH1) [CompleteSpace D]
local instance traceEigenInner : InnerProductSpace ℂ D := diskDomain_innerProductSpace D

lemma diskWeakEigenspace_rotation
    (hD : ∀ θ : ℝ, ∀ v ∈ D, diskRotation θ v ∈ D)
    (k : ℕ) (lam θ : ℝ) (u : D) (hu : u ∈ diskWeakEigenspace D (surfacePotential k) lam) :
    (⟨diskRotation θ u, hD θ u u.property⟩ : D) ∈ diskWeakEigenspace D (surfacePotential k) lam := by
  by_cases hL : lam + ((surfacePotential k).C + 1) = 0
  · rw [diskWeakEigenspace_exceptional D (surfacePotential k) lam hL] at hu ⊢
    have hz : u = 0 := hu
    simp [hz]
  · apply (mem_diskWeakEigenspace D (surfacePotential k) lam hL _).mpr
    have hu' := (mem_diskWeakEigenspace D (surfacePotential k) lam hL u).mp hu
    intro v
    exact sphericalEigen_rotation D hD k lam θ u
      (fun w hw => hu' ⟨w, hw⟩) v v.property

/-- Boundary traces of the actual weak eigenspace. -/
def diskWeakEigenTraceSpace (k : ℕ) (lam : ℝ) : Submodule ℂ (Lp ℂ 2 circleMeasure) :=
  (diskWeakEigenspace D (surfacePotential k) lam).map (diskTraceCLM.toLinearMap.comp D.subtype)

lemma diskWeakEigenTraceSpace_finiteDimensional (k : ℕ) (lam : ℝ) :
    FiniteDimensional ℂ (diskWeakEigenTraceSpace D k lam) := by
  let := diskWeakEigenspace_finiteDimensional D (surfacePotential k) lam
  unfold diskWeakEigenTraceSpace
  infer_instance

lemma diskWeakEigenTraceSpace_rotation
    (hD : ∀ θ : ℝ, ∀ v ∈ D, diskRotation θ v ∈ D)
    (k : ℕ) (lam θ : ℝ) (f : Lp ℂ 2 circleMeasure) (hf : f ∈ diskWeakEigenTraceSpace D k lam) :
    boundaryRotation θ f ∈ diskWeakEigenTraceSpace D k lam := by
  obtain ⟨u, hu, rfl⟩ := hf
  refine ⟨⟨diskRotation θ u, hD θ u u.property⟩,
    diskWeakEigenspace_rotation D hD k lam θ u hu, ?_⟩
  exact diskTrace_rotation θ u

/-- Uniform finite angular support for traces of every weak eigenspace of an
actual rotation-invariant disk domain. -/
theorem diskWeakEigenTraceSpace_finite_fourier_support
    (hD : ∀ θ : ℝ, ∀ v ∈ D, diskRotation θ v ∈ D) (k : ℕ) (lam : ℝ) :
    {n : ℤ | ∃ f ∈ diskWeakEigenTraceSpace D k lam, circleFourierCoeff f n ≠ 0}.Finite := by
  let := diskWeakEigenTraceSpace_finiteDimensional D k lam
  exact finite_fourier_support_of_rotation_invariance (diskWeakEigenTraceSpace D k lam)
    (fun θ f hf => diskWeakEigenTraceSpace_rotation D hD k lam θ f hf)

/-- Finite Fourier support for the actual boundary trace of a weak eigenfunction. -/
theorem sphericalEigen_trace_finite_support
    (hD : ∀ θ : ℝ, ∀ v ∈ D, diskRotation θ v ∈ D) (k : ℕ) (lam : ℝ)
    (u : ComplexH1) (huD : u ∈ D)
    (hu : ∀ v ∈ D, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    {n : ℤ | circleFourierCoeff (diskTraceCLM u) n ≠ 0}.Finite := by
  have he : (⟨u, huD⟩ : D) ∈ diskWeakEigenspace D (surfacePotential k) lam :=
    (mem_diskWeakEigenspace_all D (surfacePotential k) lam _).mpr
      (fun v => hu v v.property)
  apply (diskWeakEigenTraceSpace_finite_fourier_support D hD k lam).subset
  intro n hn
  exact ⟨diskTraceCLM u, ⟨⟨u, huD⟩, he, rfl⟩, hn⟩

/-- No rotation-invariance hypothesis is required from full Neumann consumers. -/
theorem sphericalEigen_neumann_trace_finite_support (k : ℕ) (lam : ℝ) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    {n : ℤ | circleFourierCoeff (diskTraceCLM u) n ≠ 0}.Finite := by
  let : CompleteSpace (⊤ : Submodule ℂ ComplexH1) :=
    (show IsClosed ((⊤ : Submodule ℂ ComplexH1) : Set ComplexH1) from isClosed_univ).completeSpace_coe
  exact sphericalEigen_trace_finite_support (⊤ : Submodule ℂ ComplexH1)
    (fun _ _ _ => Submodule.mem_top) k lam u Submodule.mem_top (fun v _ => hu v)

end KsIndex.Trace
