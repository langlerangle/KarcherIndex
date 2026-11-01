module

public import KsIndexLean.KarcherLiftCovering

@[expose] public section


/-! Continuous descent from the intrinsic periodic immersion to its parameter
sphere. Invariance under a SINGLE full period suffices. -/
noncomputable section
namespace KsIndex.KarcherData.HeightLift
variable {P Y : Type*} {F : P → PeriodTarget}

lemma invariant_deck_int (f : HeightLift F → Y)
    (h1 : ∀ q, f (deck 1 q) = f q) (n : ℤ) (q : HeightLift F) :
    f (deck n q) = f q := by
  have hp : ∀ m : ℕ, ∀ r : HeightLift F, f (deck (m : ℤ) r) = f r := by
    intro m
    induction m with
    | zero => intro r; simp only [Nat.cast_zero, deck_zero]
    | succ m ih =>
      intro r
      rw [Nat.cast_succ, add_comm, deck_add, h1, ih]
  have hn : ∀ m : ℕ, ∀ r : HeightLift F, f (deck (-(m : ℤ)) r) = f r := by
    intro m r
    have hh := hp m (deck (-(m : ℤ)) r)
    rw [← deck_add, add_neg_cancel, deck_zero] at hh
    exact hh.symm
  cases n with
  | ofNat m => exact hp m q
  | negSucc m => exact hn (m + 1) q

/-- A continuous full-period-invariant map descends uniquely and continuously
through the actual EW parameter projection. No covering-map classification
or injectivity of the immersion is assumed. -/
theorem existsUnique_continuous_period_descent [TopologicalSpace P] [TopologicalSpace Y]
    (hF : Continuous F) (f : HeightLift F → Y) (hf : Continuous f)
    (h1 : ∀ q, f (deck 1 q) = f q) :
    ∃! g : P → Y, Continuous g ∧ f = g ∘ projection := by
  classical
  let s : P → HeightLift F := fun p => Classical.choose (projection_surjective (F := F) p)
  have hs (p : P) : projection (s p) = p :=
    Classical.choose_spec (projection_surjective (F := F) p)
  let g : P → Y := f ∘ s
  have he : f = g ∘ projection := by
    funext q
    obtain ⟨n, hn⟩ := (same_projection_iff (s (projection q)) q).mp (hs (projection q))
    change f q = f (s (projection q))
    exact (congrArg f hn.symm).trans (invariant_deck_int f h1 n _)
  refine ⟨g, ⟨?_, he⟩, ?_⟩
  · apply (projection_isQuotientMap hF).continuous_iff.mpr
    rw [← he]
    exact hf
  · intro g' hg'
    funext p
    obtain ⟨q, rfl⟩ := projection_surjective (F := F) p
    exact (congrFun hg'.2 q).symm.trans (congrFun he q)

end KsIndex.KarcherData.HeightLift
