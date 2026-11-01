module

public import KsIndexLean.JacobiExtensionOperator
public import KsIndexLean.JacobiWeakTrace

@[expose] public section


/-! Full half-order boundary data admit weak H¹ lifts on the disk.
The lift combines a mean-zero Jacobi extension with a constant function;
no Jacobi equation is asserted for the resulting full lift. -/
noncomputable section
open MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.CircleSobolev
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- A weak H¹ representative of the constant function one. -/
def constantOneH1 : ComplexH1 :=
  globalSmoothH1 (fun _ : ℂ => (1 : ℂ)) contDiff_const

lemma constantOneH1_coeff_zero :
    coeff (1 / 2 : ℝ) (halfDiskTraceCLM constantOneH1) 0 = 1 := by
  rw [halfDiskTraceCLM_apply, coeff_halfDiskTrace]
  have h := circleFourierCoeff_congr_ae
    (globalSmoothH1_trace (fun _ : ℂ => (1 : ℂ)) contDiff_const)
  change circleFourierCoeff (diskTraceCLM
    (globalSmoothH1 (fun _ : ℂ => (1 : ℂ)) contDiff_const)) 0 = _
  rw [congrFun h 0, ← fourierCoeff_geometric_pullback]
  have he : (fun _ : AddCircle (2 * Real.pi) => (1 : ℂ)) = fourier 0 := by
    ext x
    simp
  rw [he, fourierCoeff_fourier]
  simp

/-- The actual half-order disk trace is surjective, including its constant mode. -/
theorem halfDiskTraceCLM_surjective : Function.Surjective halfDiskTraceCLM := by
  intro f
  let c : ℂ := coeff (1 / 2 : ℝ) f 0
  let f0 : Space (1 / 2 : ℝ) := halfDiskTraceCLM constantOneH1
  have hg : f - c • f0 ∈ dotted (1 / 2 : ℝ) := by
    change coeffLinear (1 / 2 : ℝ) 0 (f - c • f0) = 0
    rw [map_sub, map_smul]
    change c - c * coeff (1 / 2 : ℝ) (halfDiskTraceCLM constantOneH1) 0 = 0
    rw [constantOneH1_coeff_zero, mul_one, sub_self]
  refine ⟨jacobiExtensionCLM (show 2 ≤ 3 by norm_num) ⟨f - c • f0, hg⟩ +
    c • constantOneH1, ?_⟩
  rw [map_add, map_smul, jacobiExtensionCLM_halfTrace]
  exact sub_add_cancel _ _

/-- Every half-order datum is realized by the genuine L²-valued disk trace. -/
theorem exists_diskTrace_eq_toL2 (f : Space (1 / 2 : ℝ)) :
    ∃ u : ComplexH1, diskTraceCLM u = toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) f := by
  obtain ⟨u, hu⟩ := halfDiskTraceCLM_surjective f
  refine ⟨u, ?_⟩
  rw [← toL2_halfDiskTrace, ← halfDiskTraceCLM_apply, hu]

end KsIndex.Trace
