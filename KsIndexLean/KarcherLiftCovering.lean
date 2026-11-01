module

public import KsIndexLean.KarcherLiftManifold
public import Mathlib.Topology.Covering.Quotient

@[expose] public section


/-! The intrinsic periodic lift is a genuine integer-deck covering. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} {F : P → PeriodTarget}

/-- Integral deck translations acting on the intrinsic carrier. -/
scoped instance deckAction : AddAction ℤ (HeightLift F) where
  vadd := deck
  zero_vadd := deck_zero
  add_vadd := deck_add

open scoped KsIndex.KarcherData.HeightLift
variable [TopologicalSpace P]

omit [TopologicalSpace P] in
/-- Distinct integral translates of a single open height strip are disjoint. -/
lemma strip_translate_disjoint (a : ℝ) (n : ℤ)
    (h : ((n +ᵥ ·) '' strip (F := F) a ∩ strip a).Nonempty) : n = 0 := by
  obtain ⟨q, ⟨r, hr, rfl⟩, hn⟩ := h
  have he : (deck n r : HeightLift F) = r := by
    have hh : stripEquiv a ⟨deck n r, hn⟩ = stripEquiv a ⟨r, hr⟩ := by
      apply Subtype.ext
      rfl
    exact congrArg Subtype.val ((stripEquiv a).injective hh)
  exact deck_free he

/-- The projection is a quotient covering for the actual integral deck action. -/
theorem projection_isAddQuotientCoveringMap (hF : Continuous F) :
    IsAddQuotientCoveringMap (projection (F := F)) ℤ where
  toIsQuotientMap := projection_isQuotientMap hF
  continuous_const_vadd := continuous_deck
  apply_eq_iff_mem_orbit := by
    intro q r
    exact (eq_comm.trans (same_projection_iff r q))
  disjoint q := ⟨strip (height q - Real.pi),
    (isOpen_strip _).mem_nhds (mem_centered_strip q), strip_translate_disjoint _⟩

/-- Every base point has an evenly covered neighborhood, with integer sheets. -/
theorem projection_isCoveringMap (hF : Continuous F) :
    IsCoveringMap (projection (F := F)) :=
  (projection_isAddQuotientCoveringMap hF).isCoveringMap

end KsIndex.KarcherData.HeightLift
namespace KsIndex.KarcherData

/-- The actual EW parameter sphere is covered by the intrinsic real-height lift.
This includes the regular infinity point; connectedness is a separate claim. -/
theorem exists_periodicEW_covering {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    ∃ C : PeriodTarget,
      IsCoveringMap (HeightLift.projection (F := extendedEWMap hk b C)) := by
  obtain ⟨C, hC, _⟩ := exists_continuous_extendedEWMap hk b
  exact ⟨C, HeightLift.projection_isCoveringMap hC⟩

open scoped ContDiff Manifold ParameterAtlas PeriodicAmbient

/-- A single actual EW extension supplies both the smooth lifted immersion and
 the integer-deck covering of the punctured parameter sphere. -/
theorem exists_smooth_periodicEW_covering {k : ℕ} [h : Fact (2 ≤ k)]
    (b : PuncturedPlane k) :
    ∃ C : PeriodTarget, ∃ hC : Continuous (extendedEWMap h.out b C),
      letI := HeightLift.liftChartedSpace hC
      IsManifold 𝓘(ℝ, ℂ) ∞ (PeriodicEWCarrier h.out b C) ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞
        (HeightLift.ambient (F := extendedEWMap h.out b C)) ∧
      (∀ q : PeriodicEWCarrier h.out b C,
        IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) HeightLift.ambient q) ∧
      IsCoveringMap (HeightLift.projection (F := extendedEWMap h.out b C)) := by
  obtain ⟨C, hC, hm, hs, hi⟩ := exists_smooth_immersed_periodicEWMap b
  exact ⟨C, hC, hm, hs, hi, HeightLift.projection_isCoveringMap hC⟩

end KsIndex.KarcherData
