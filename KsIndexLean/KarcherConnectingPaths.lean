module

public import KsIndexLean.ContourConnectingPaths
public import KsIndexLean.KarcherPathComparison

@[expose] public section


/-! Actual connecting chains in the finite punctured plane. Paths may leave the unit disk.
This is path existence only, not a quotient map, covering, or disk/seam identification. -/
noncomputable section
namespace KsIndex.KarcherData
open Piecewise

theorem exists_connecting_chain {k : ℕ} (hk : 2 ≤ k) {x y : ℂ}
    (hx : x ∉ Surface.punctures k) (hy : y ∉ Surface.punctures k) :
    ∃ C : Chain, C.start = x ∧ C.finish = y ∧
      (∀ z ∈ Surface.punctures k, C.Avoids z) := by
  obtain ⟨C, hs, ht, hA⟩ := exists_chain_avoiding_finset (punctureFinset k) x y
    (fun h => hx ((mem_punctureFinset hk).mp h))
    (fun h => hy ((mem_punctureFinset hk).mp h))
  exact ⟨C, hs, ht, fun z hz => hA z ((mem_punctureFinset hk).mpr hz)⟩

end KsIndex.KarcherData
