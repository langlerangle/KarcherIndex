module

public import KsIndexLean.NormalizedDiskGluing
public import KsIndexLean.EndFieldDomain

@[expose] public section


/-! Boundary values for a paper disk pair: arc0 has phase `c`, arc1 has phase
one, and deleted punctures carry the canonical zero representative. -/
noncomputable section
namespace KsIndex.Trace

def paperBoundary (F0 F1 : ℂ → ℂ) (z : ℂ) : ℂ :=
  if (z ^ 3).re < 0 then F0 z else if 0 < (z ^ 3).re then F1 z else 0

lemma paperBoundary_arc0 (F0 F1 : ℂ → ℂ) {z : ℂ} (hz : z ∈ Surface.arc 3 0) :
    paperBoundary F0 F1 z = F0 z := by
  have hr : (z ^ 3).re < 0 := by simpa using hz.2
  exact ite_eq_left hr

lemma paperBoundary_arc1 (F0 F1 : ℂ → ℂ) {z : ℂ} (hz : z ∈ Surface.arc 3 1) :
    paperBoundary F0 F1 z = F1 z := by
  have hr : 0 < (z ^ 3).re := by simpa using hz.2
  simp only [paperBoundary, ite_eq_right (not_lt.mpr hr.le), ite_eq_left hr]

lemma paperBoundary_puncture (F0 F1 : ℂ → ℂ) {z : ℂ} (hz : z ∈ Surface.punctures 3) :
    paperBoundary F0 F1 z = 0 := by
  simp [paperBoundary, (EndField.cube_re_im hz).1]

lemma filledDisk_paper_puncture (f F0 F1 : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ Surface.punctures 3) : filledDisk f (paperBoundary F0 F1) z = 0 := by
  rw [filledDisk_eq_boundary f _ (EndChart.norm_eq_one_of_mem_punctures hz)]
  exact paperBoundary_puncture F0 F1 hz

/-- The normalized upper and lower circle values have the exact paper phase jump. -/
lemma filledDisk_paper_arc0_match (c : ℂ) (hc : c ≠ 0) (f g F0 F1 : ℂ → ℂ)
    {z : ℂ} (hz : z ∈ Surface.arc 3 0) :
    filledDisk f (paperBoundary F0 F1) z =
      c * filledDisk g (paperBoundary (fun w => c⁻¹ * F0 w) F1) z := by
  rw [filledDisk_eq_boundary f _ hz.1, filledDisk_eq_boundary g _ hz.1,
    paperBoundary_arc0 F0 F1 hz, paperBoundary_arc0 _ F1 hz]
  simp [hc]

lemma filledDisk_paper_arc1_match (c : ℂ) (f g F0 F1 : ℂ → ℂ)
    {z : ℂ} (hz : z ∈ Surface.arc 3 1) :
    filledDisk f (paperBoundary F0 F1) z =
      filledDisk g (paperBoundary (fun w => c⁻¹ * F0 w) F1) z := by
  rw [filledDisk_eq_boundary f _ hz.1, filledDisk_eq_boundary g _ hz.1,
    paperBoundary_arc1 F0 F1 hz, paperBoundary_arc1 _ F1 hz]

end KsIndex.Trace
