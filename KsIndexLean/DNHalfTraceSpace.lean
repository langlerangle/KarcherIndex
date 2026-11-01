module

public import KsIndexLean.HalfOrderDiskTrace
public import KsIndexLean.CircleSobolevArc
public import KsIndexLean.CircleSobolevRotation
public import KsIndexLean.WeakBoundaryDomains

@[expose] public section


/-! The paper's global half-order DN trace space, using the existing arc family. -/
noncomputable section
open MeasureTheory Set
namespace KsIndex.CircleSobolev
open KsIndex.Trace KsIndex.WeakH1

/-- The paper imposes zero boundary values on arc 0, leaving arc 1 free. -/
def dnSpace (k : ℕ) : Submodule ℂ (Space (1 / 2 : ℝ)) :=
  arcZero (show (0 : ℝ) ≤ 1 / 2 by norm_num) (boundaryArc k 0)

theorem isClosed_dnSpace (k : ℕ) : IsClosed (dnSpace k : Set (Space (1 / 2 : ℝ))) :=
  isClosed_arcZero _ _

theorem mem_dnSpace_iff_norm (k : ℕ) (v : Space (1 / 2 : ℝ)) :
    v ∈ dnSpace k ↔
      ‖arcRestriction (show (0 : ℝ) ≤ 1 / 2 by norm_num) (boundaryArc k 0) v‖ = 0 :=
  mem_arcZero_iff_norm _ _ _

/-- Restricting the half-order trace is exactly the existing weak arcTrace. -/
theorem arcRestriction_halfDiskTrace (A : Set Circle₁) (u : ComplexH1) :
    arcRestriction (show (0 : ℝ) ≤ 1 / 2 by norm_num) A (halfDiskTraceCLM u) = arcTrace A u := by
  change boundaryRestrictCLM A (toL2 _ (halfDiskTrace u)) = _
  rw [toL2_halfDiskTrace]
  rfl

theorem halfDiskTrace_mem_dnSpace_iff (k : ℕ) (u : ComplexH1) :
    halfDiskTraceCLM u ∈ dnSpace k ↔ arcTrace (boundaryArc k 0) u = 0 := by
  change arcRestriction _ (boundaryArc k 0) (halfDiskTraceCLM u) = 0 ↔ _
  rw [arcRestriction_halfDiskTrace]

/-- Exact agreement with the existing natural mixed boundary domain. -/
theorem halfDiskTrace_mem_dnSpace_iff_mixed (k : ℕ) (u : ComplexH1) :
    halfDiskTraceCLM u ∈ dnSpace k ↔ u ∈ mixedTraceDomain k true false := by
  rw [halfDiskTrace_mem_dnSpace_iff]
  simp only [mixedTraceDomain, naturalArcDomain, Bool.false_eq_true, ite_false, ite_true,
    top_inf_eq]
  rfl

/-- The paper's DN character subspace uses the same -j+kZ convention. -/
def dnCharacterSpace (k : ℕ) (j : ℤ) : Submodule ℂ (Space (1 / 2 : ℝ)) :=
  dnSpace k ⊓ character (1 / 2 : ℝ) j (k : ℤ)

theorem halfDiskTrace_mem_dnCharacterSpace {k r : ℕ} (hk : 0 < k) {u : ComplexH1}
    (hu : u ∈ mixedCharacterDomain k r true false) :
    halfDiskTraceCLM u ∈ dnCharacterSpace k (r : ℤ) := by
  refine ⟨(halfDiskTrace_mem_dnSpace_iff_mixed k u).mpr hu.1, ?_⟩
  apply (mem_character_iff_boundaryRotation (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    k hk (r : ℤ) (halfDiskTraceCLM u)).mpr
  simp only [halfDiskTraceCLM_apply, toL2_halfDiskTrace, zpow_natCast]
  exact trace_character hu.2

end KsIndex.CircleSobolev
