module

public import KsIndexLean.SignedDiskPair

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.SingleDisk

/-- The closed even or odd eigenspace of actual equatorial reflection. -/
def sphereReflectionDomain (k : ℕ) (b : Bool) : Submodule ℂ (SphericalSlitNeumannSpace k) :=
  let R := (sphereChartReflectionEquiv (isOpen_boundaryArc k 1)).toContinuousLinearEquiv
  LinearMap.ker (R.toContinuousLinearMap -
    sgn b • ContinuousLinearMap.id ℂ (SphericalSlitNeumannSpace k)).toLinearMap

lemma isClosed_sphereReflectionDomain (k : ℕ) (b : Bool) :
    IsClosed (sphereReflectionDomain k b : Set (SphericalSlitNeumannSpace k)) := by
  let R := (sphereChartReflectionEquiv (isOpen_boundaryArc k 1)).toContinuousLinearEquiv
  exact (R.toContinuousLinearMap -
    sgn b • ContinuousLinearMap.id ℂ (SphericalSlitNeumannSpace k)).isClosed_ker

lemma mem_sphereReflectionDomain_iff (k : ℕ) (b : Bool) (q : SphericalSlitNeumannSpace k) :
    q ∈ sphereReflectionDomain k b ↔
      (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) q).2 =
        sgn b • (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) q).1 := by
  change sphereChartReflectionEquiv (isOpen_boundaryArc k 1) q - sgn b • q = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    have he := congrArg (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)) h
    rw [sphereChartReflection_coordinates, map_smul] at he
    exact congrArg Prod.fst he
  · intro h
    apply sphereDiskCoordinates_injective (isOpen_boundaryArc k 1)
    rw [sphereChartReflection_coordinates, map_smul]
    apply Prod.ext h
    change _ = sgn b • (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) q).2
    rw [h, smul_smul, sgn_mul_sgn, one_smul]

/-- Phase and reflection conditions whose restriction gives the two mixed boundary signs. -/
def sphericalSignedDomain (k : ℕ) (b1 b0 : Bool) :
    Submodule ℂ (SphericalSlitNeumannSpace k) :=
  sphericalPhaseDomain k (sgn b1 * sgn b0) ⊓ sphereReflectionDomain k b1

lemma signedSphere_first_mem_mixed (k : ℕ) (b1 b0 : Bool) (q : sphericalSignedDomain k b1 b0) :
    (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) q.val).1 ∈ mixedTraceDomain k b1 b0 := by
  apply (signedDiskPair_mem_slit_iff k b1 b0 _).mp
  have hs := (mem_sphereReflectionDomain_iff k b1 q.val).mp q.property.2
  have he : signedDiskPair b1 (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) q.val).1 =
      sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) q.val := Prod.ext rfl hs.symm
  rw [he, mem_slitTraceDomain]
  exact ⟨(chartDiskPair (isOpen_boundaryArc k 1) q.val).property, q.property.1⟩

end KsIndex.Spherical
