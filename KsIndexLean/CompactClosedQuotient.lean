module

public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section


/-! Hausdorff quotients of compact Hausdorff spaces by closed equivalence relations. -/
open Set Topology

/-- Closed equivalence relations on compact Hausdorff spaces give proper
quotient maps and Hausdorff quotient spaces. -/
theorem proper_quotient_of_closed_relation {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (s : Setoid X)
    (hs : IsClosed {p : X × X | s p.1 p.2}) :
    IsProperMap (Quotient.mk s) := by
  have hclosed : IsClosedMap (Quotient.mk s) := by
    intro A hA
    apply isQuotientMap_quotient_mk'.isClosed_preimage.mp
    have hc := (hs.inter (hA.preimage continuous_snd)).isCompact
    convert (hc.image continuous_fst).isClosed using 1
    ext x
    simp only [mem_preimage, mem_image, Prod.exists, mem_inter_iff, mem_ofPred_eq,
      exists_and_right, exists_eq_right]
    constructor
    · rintro ⟨y, hy, he⟩
      exact ⟨y, s.symm (Quotient.exact he), hy⟩
    · rintro ⟨y, hxy, hy⟩
      exact ⟨y, hy, (Quotient.sound hxy).symm⟩
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨continuous_quotient_mk', hclosed, ?_⟩
  intro y
  induction y using Quotient.inductionOn with
  | h y =>
    have hc := hs.preimage (continuous_id.prodMk continuous_const :
      Continuous (fun x : X => (x,y)))
    convert hc.isCompact using 1
    ext x
    exact Quotient.eq

/-- The product of the proper quotient map takes the closed diagonal to the
quotient diagonal, giving Hausdorffness without assuming it in advance. -/
theorem t2Space_quotient_of_closed_relation {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (s : Setoid X)
    (hs : IsClosed {p : X × X | s p.1 p.2}) : T2Space (Quotient s) := by
  have hp := proper_quotient_of_closed_relation s hs
  apply t2_iff_isClosed_diagonal.mpr
  convert (hp.prodMap hp).isClosedMap _ (isClosed_diagonal (X := X)) using 1
  ext p
  constructor
  · intro he
    obtain ⟨x, hx⟩ := Quotient.mk_surjective p.1
    exact ⟨(x,x), rfl, by simpa only [Prod.map_apply, hx] using (Prod.ext rfl he : (p.1, p.1) = p)⟩
  · rintro ⟨⟨x,y⟩, he, rfl⟩
    exact congrArg (Quotient.mk s) he
