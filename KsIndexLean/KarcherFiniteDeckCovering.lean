module

public import KsIndexLean.KarcherPeriodQuotientFibers
public import KsIndexLean.KarcherTranslationPullback
public import Mathlib.Topology.Covering.Quotient

@[expose] public section


/-! The actual m-period quotient is a cyclic covering of its parameter surface. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} {F : P → PeriodTarget}

lemma periodDeck_eq_iff (m : ℕ) (x : PeriodQuotient F m) (n l : ℤ) :
    periodDeck m n x = periodDeck m l x ↔ (n : ZMod m) = (l : ZMod m) := by
  induction x using Quotient.inductionOn with
  | h q => exact periodQuotientMap_deck_eq_iff m q n l

@[simp] lemma quotientProjection_periodDeck (m : ℕ) (n : ℤ) (x : PeriodQuotient F m) :
    quotientProjection m (periodDeck m n x) = quotientProjection m x := by
  induction x using Quotient.inductionOn with | h q => rfl

variable {m : ℕ} [NeZero m]

/-- The cyclic deck action uses the existing positive integer translation. -/
def cyclicDeck (z : ZMod m) : PeriodQuotient F m → PeriodQuotient F m :=
  periodDeck m (z.val : ℤ)

lemma cyclicDeck_intCast (n : ℤ) (x : PeriodQuotient F m) :
    cyclicDeck (n : ZMod m) x = periodDeck m n x := by
  exact (periodDeck_eq_iff m x _ _).mpr (by simp)

omit [NeZero m] in
@[simp] lemma cyclicDeck_zero (x : PeriodQuotient F m) : cyclicDeck (0 : ZMod m) x = x := by
  simp [cyclicDeck]

lemma cyclicDeck_add (z w : ZMod m) (x : PeriodQuotient F m) :
    cyclicDeck (z + w) x = cyclicDeck z (cyclicDeck w x) := by
  unfold cyclicDeck
  rw [← periodDeck_add]
  apply (periodDeck_eq_iff m x _ _).mpr
  simp

scoped instance cyclicDeckAction : AddAction (ZMod m) (PeriodQuotient F m) where
  vadd := cyclicDeck
  zero_vadd := cyclicDeck_zero
  add_vadd := cyclicDeck_add

lemma cyclicDeck_free (z : ZMod m) (x : PeriodQuotient F m)
    (hx : cyclicDeck z x = x) : z = 0 := by
  have he : periodDeck m (z.val : ℤ) x = periodDeck m 0 x := by
    simpa only [periodDeck_zero, cyclicDeck] using hx
  have hi := (periodDeck_eq_iff m x _ _).mp he
  simpa using hi

lemma same_quotientProjection_iff (x y : PeriodQuotient F m) :
    quotientProjection m x = quotientProjection m y ↔
      ∃ z : ZMod m, cyclicDeck z x = y := by
  induction x using Quotient.inductionOn with
  | h q =>
    induction y using Quotient.inductionOn with
    | h r =>
      constructor
      · intro he
        obtain ⟨n, hn⟩ := (same_projection_iff q r).mp he
        refine ⟨(n : ZMod m), ?_⟩
        change cyclicDeck (n : ZMod m) (periodQuotientMap m q) = periodQuotientMap m r
        rw [cyclicDeck_intCast, periodDeck_mk, hn]
      · rintro ⟨z, hz⟩
        exact (quotientProjection_periodDeck m (z.val : ℤ) (periodQuotientMap m q)).symm.trans
          (congrArg (quotientProjection (F := F) m) hz)

variable [TopologicalSpace P]
open scoped KsIndex.KarcherData.HeightLift

omit [NeZero m] in
lemma continuous_cyclicDeck (z : ZMod m) : Continuous (cyclicDeck (F := F) z) :=
  continuous_periodDeck m (z.val : ℤ)

/-- The cyclic action is free, transitive on fibers, and has disjoint local sheets. -/
theorem quotientProjection_isAddQuotientCoveringMap (hF : Continuous F) :
    IsAddQuotientCoveringMap (quotientProjection (F := F) m) (ZMod m) where
  toIsQuotientMap := (quotientProjection_isLocalHomeomorph hF m).isOpenMap.isQuotientMap
    (quotientProjection_isLocalHomeomorph hF m).continuous (quotientProjection_surjective m)
  continuous_const_vadd := continuous_cyclicDeck
  apply_eq_iff_mem_orbit := by
    intro x y
    exact eq_comm.trans (same_quotientProjection_iff y x)
  disjoint x := by
    obtain ⟨U, hx, hU⟩ :=
      isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp
        (quotientProjection_isLocalHomeomorph hF m) x
    refine ⟨U, hx, ?_⟩
    intro z hz
    obtain ⟨y, ⟨r, hr, rfl⟩, hy⟩ := hz
    have he : cyclicDeck z r = r := by
      have hi := hU.injective (a₁ := ⟨cyclicDeck z r, hy⟩) (a₂ := ⟨r, hr⟩)
        (quotientProjection_periodDeck m (z.val : ℤ) r)
      exact congrArg Subtype.val hi
    exact cyclicDeck_free z r he

/-- A genuine covering map, with exactly m points in every fiber. -/
theorem quotientProjection_isCoveringMap (hF : Continuous F) :
    IsCoveringMap (quotientProjection (F := F) m) :=
  (quotientProjection_isAddQuotientCoveringMap (m := m) hF).isCoveringMap

end KsIndex.KarcherData.HeightLift

namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open scoped KsIndex.KarcherData.ParameterAtlas
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- The actual EW m-period quotient covers the punctured parameter sphere
with m sheets, including over its regular infinity point. -/
theorem periodQuotient_covering_degree (R : PaperHalfPeriodRealization k) :
    IsCoveringMap (HeightLift.quotientProjection
      (F := extendedEWMap h.out (reflectionBasepoint k) R.C) m) ∧
    ∀ p : ParameterSphere k,
      Nat.card {x : HeightLift.PeriodQuotient
          (extendedEWMap h.out (reflectionBasepoint k) R.C) m //
        HeightLift.quotientProjection m x = p} = m :=
  ⟨HeightLift.quotientProjection_isCoveringMap R.hC,
    HeightLift.card_quotientProjection_fiber⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
