module

public import KsIndexLean.KarcherPieceLift

@[expose] public section


noncomputable section
open Set
namespace KsIndex.KarcherData
open Piecewise

/-- A certified piece can be lifted from any point over its starting parameter. -/
theorem joined_piece_from {k : ℕ} (hk : 2 ≤ k) (base : PuncturedPlane k) (C : PeriodTarget)
    (p : Piece) (hA : ∀ z ∈ Surface.punctures k, p.Avoids z)
    (q : PeriodicEWCarrier hk base C)
    (hq : HeightLift.projection q = finiteParameter
      ⟨p.start, fun hz => p.start_ne (hA _ hz) rfl⟩) :
    ∃ r : PeriodicEWCarrier hk base C, Joined q r ∧
      HeightLift.projection r = finiteParameter ⟨p.finish, fun hz => p.finish_ne (hA _ hz) rfl⟩ ∧
      HeightLift.height r = HeightLift.height q + (p.contour (coeff3 k)).re := by
  have hz : (HeightLift.height q : AddCircle (2 * Real.pi)) =
      (descendedIntegral hk base ⟨p.start, fun hz => p.start_ne (hA _ hz) rfl⟩).2.2 := by
    have hh := q.property
    change (HeightLift.height q : AddCircle (2 * Real.pi)) =
      (extendedEWMap hk base C (HeightLift.projection q)).2.2 at hh
    erw [hq, extendedEWMap_finite] at hh
    exact hh
  let L := pieceLift hk base C p hA (HeightLift.height q) hz
  have hs : L ⟨p.a, le_rfl, p.lt.le⟩ = q := by
    apply Subtype.ext
    apply Prod.ext
    · exact hq.symm
    · simp [L, pieceLift, pieceIntegral, HeightLift.height]
  refine ⟨L ⟨p.b, p.lt.le, le_rfl⟩, ?_, rfl, rfl⟩
  rw [← hs]
  exact joined_pieceLift_endpoints hk base C p hA (HeightLift.height q) hz

/-- Whole certified chains lift to continuous paths, with the exact summed
 vertical contour integral as their endpoint height change. -/
theorem joined_chain_from {k : ℕ} (hk : 2 ≤ k) (base : PuncturedPlane k) (C : PeriodTarget)
    (D : Chain) (hA : ∀ z ∈ Surface.punctures k, D.Avoids z)
    (q : PeriodicEWCarrier hk base C)
    (hq : HeightLift.projection q = finiteParameter
      ⟨D.start, fun hz => D.start_ne (hA _ hz) rfl⟩) :
    ∃ r : PeriodicEWCarrier hk base C, Joined q r ∧
      HeightLift.projection r = finiteParameter ⟨D.finish, fun hz => D.finish_ne (hA _ hz) rfl⟩ ∧
      HeightLift.height r = HeightLift.height q + (D.contour (coeff3 k)).re := by
  rcases D with ⟨n, p, hm⟩
  induction n generalizing q with
  | zero =>
    obtain ⟨r, hj, hp, hh⟩ := joined_piece_from hk base C (p 0) (fun z hz => hA z hz 0) q hq
    refine ⟨r, hj, hp, ?_⟩
    simpa [Chain.contour] using hh
  | succ n ih =>
    let T : Chain := ⟨n, fun i => p i.succ, fun i => hm i.succ⟩
    have hT : ∀ z ∈ Surface.punctures k, T.Avoids z := fun z hz i => hA z hz i.succ
    obtain ⟨r, hj, hp, hh⟩ := joined_piece_from hk base C (p 0) (fun z hz => hA z hz 0) q hq
    have hrt : HeightLift.projection r = finiteParameter
        ⟨T.start, fun hz => T.start_ne (hT _ hz) rfl⟩ := by
      rw [hp]
      apply congrArg finiteParameter
      apply Subtype.ext
      exact hm 0
    obtain ⟨s, hjs, hps, hhs⟩ := ih r (fun i => p i.succ) (fun i => hm i.succ) hT hrt
    refine ⟨s, hj.trans hjs, hps, ?_⟩
    rw [hhs, hh]
    simp only [Chain.contour, Fin.sum_univ_succ, Complex.add_re]
    dsimp [T, Chain.contour]
    ring

/-- Any two points over finite parameters are joined in the intrinsic lift,
 including points on arbitrarily different integral sheets. -/
theorem joined_finite_lifts {k : ℕ} (hk : 2 ≤ k)
    (base b w : PuncturedPlane k) (C : PeriodTarget)
    (q r : PeriodicEWCarrier hk base C)
    (hq : HeightLift.projection q = finiteParameter b)
    (hr : HeightLift.projection r = finiteParameter w) : Joined q r := by
  obtain ⟨D, hs, ht, hA, hv⟩ := exists_chain_between_finite_lifts hk base b w C q r hq hr
  have hqs : HeightLift.projection q = finiteParameter
      ⟨D.start, fun hz => D.start_ne (hA _ hz) rfl⟩ := by
    rw [hq]
    apply congrArg finiteParameter
    exact Subtype.ext hs.symm
  obtain ⟨s, hj, hp, hh⟩ := joined_chain_from hk base C D hA q hqs
  have hs : s = r := by
    apply Subtype.ext
    apply Prod.ext
    · change HeightLift.projection s = HeightLift.projection r
      rw [hp, hr]
      apply congrArg finiteParameter
      exact Subtype.ext ht
    · change HeightLift.height s = HeightLift.height r
      have hvz := congrArg (fun v : AmbientTriple => v.2.2) hv
      change (D.contour (coeff3 k)).re = HeightLift.height r - HeightLift.height q at hvz
      rw [hh, hvz]
      ring
  exact hs ▸ hj

end KsIndex.KarcherData
