module

public import KsIndexLean.FullBoundaryMatching
public import KsIndexLean.WeakBoundaryDomains
public import KsIndexLean.BoundaryRestriction
public import KsIndexLean.CharDecomp

@[expose] public section


/-!
# Pure Dirichlet character domain

For `k ≥ 1`, imposing zero trace on both boundary arcs is equivalent to zero
trace on the full boundary. Intersecting with the same weak character condition
identifies `mixedCharacterDomain k j false false` with the full zero-trace
character domain, for every natural `j`.

The identity uses boundary matching and submodule membership alone, so it is
available to both ground-state and spectral positivity arguments.
-/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FormIndex

/-- The pure-Dirichlet mixed-character block (`false false`) equals the full zero-trace domain
intersected with the quasi-periodic character domain. -/
lemma mixedDD_eq_fullDirichletCharacter {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    mixedCharacterDomain k j false false =
      zeroTraceDomain Set.univ ⊓ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) := by
  ext u
  simp only [mixedCharacterDomain, mixedTraceDomain, naturalArcDomain, Bool.false_eq_true,
    ↓reduceIte, Submodule.mem_inf]
  have he := full_trace_eq_iff_arcs hk u (0 : ComplexH1)
  simp only [map_zero] at he
  change (arcTrace (boundaryArc k 1) u = 0 ∧ arcTrace (boundaryArc k 0) u = 0) ∧ _ ↔
    arcTrace Set.univ u = 0 ∧ _
  rw [he]

end KsIndex.Trace
