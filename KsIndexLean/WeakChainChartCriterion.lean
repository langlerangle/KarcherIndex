module

public import KsIndexLean.InversionJetTransition
public import KsIndexLean.WeakDiskChain

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma seamBoundary_eq_boundaryArc (k m : ℕ) (n : ZMod (2 * m)) :
    seamBoundary k m n = boundaryArc k (Surface.parity m (n + 1)).val := rfl

lemma isOpen_seamBoundary (k m : ℕ) (n : ZMod (2 * m)) :
    IsOpen (seamBoundary k m n) := by
  rw [seamBoundary_eq_boundaryArc]
  exact isOpen_boundaryArc _ _

lemma joinedDiskValue_eq_surface_glue {m : ℕ} (u : ZMod (2 * m) → ComplexH1)
    (n : ZMod (2 * m)) :
    joinedDiskValue (u n) (u (n + 1)) 1 =
      Surface.glue (fun j => (valueCLM (u j) : ℂ → ℂ)) n := by
  funext z
  simp only [joinedDiskValue_sigma_formula, one_smul, Surface.glue, KsIndex.Bracket.σ]

/-- The trace-kernel chain is exactly finite-energy weak gluing
in the original surface chart formulas at every incident seam. -/
theorem mem_weakDiskChain_iff_surface_charts (k m : ℕ) [NeZero m]
    (u : ZMod (2 * m) → ComplexH1) :
    u ∈ weakDiskChain k m ↔ ∀ n, ∃ J : ℂ → ℂ →L[ℝ] ℂ,
      TauCeti.HasWeakFDerivOn volume
        (extendedSeamDomain (seamBoundary k m n) (isOpen_seamBoundary k m n))
        (Surface.glue (fun j => (valueCLM (u j) : ℂ → ℂ)) n) J ∧
      MemLp J 2 (volume.restrict
        (extendedSeamDomain (seamBoundary k m n) (isOpen_seamBoundary k m n) : Set ℂ)) := by
  rw [mem_weakDiskChain]
  constructor
  · intro h n
    refine ⟨joinedDiskJet (u n) (u (n + 1)) 1, ?_,
      extendedSeamDomain_jet_memLp _ _ _ _⟩
    rw [← joinedDiskValue_eq_surface_glue]
    exact extendedSeamDomain_weak _ _ _ _ (by simpa using h n)
  · intro h n
    obtain ⟨J, hJ, _⟩ := h n
    rw [← joinedDiskValue_eq_surface_glue] at hJ
    simpa using (extendedSeamDomain_weak_iff_trace (isOpen_seamBoundary k m n)
      (u n) (u (n + 1)) 1).mp ⟨J, hJ⟩

lemma surface_chart_value_memLp {m : ℕ} (k : ℕ) (u : ZMod (2 * m) → ComplexH1)
    (n : ZMod (2 * m)) :
    MemLp (Surface.glue (fun j => (valueCLM (u j) : ℂ → ℂ)) n) 2
      (volume.restrict
        (extendedSeamDomain (seamBoundary k m n) (isOpen_seamBoundary k m n) : Set ℂ)) := by
  rw [← joinedDiskValue_eq_surface_glue]
  exact extendedSeamDomain_value_memLp _ _ _ _

end KsIndex.Trace
