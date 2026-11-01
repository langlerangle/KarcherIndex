module

public import KsIndexLean.KarcherPeriodicLift
public import Mathlib.Topology.IsLocalHomeomorph

@[expose] public section


/-! Local topological charts for the intrinsic periodic lift. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.HeightLift
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {P : Type*} [TopologicalSpace P] {F : P → PeriodTarget}

/-- A single real-height strip in the lift. -/
def strip (a : ℝ) : Set (HeightLift F) :=
  height ⁻¹' (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).source

/-- The corresponding open subset of the parameter carrier. -/
def stripBase (F : P → PeriodTarget) (a : ℝ) : Set P :=
  (fun p => (F p).2.2) ⁻¹' (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).target

lemma isOpen_strip (a : ℝ) : IsOpen (strip (F := F) a) :=
  (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).open_source.preimage continuous_height

lemma isOpen_stripBase (hF : Continuous F) (a : ℝ) : IsOpen (stripBase F a) :=
  (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).open_target.preimage hF.snd.snd

/-- Projection restricts to a set equivalence on each open height strip.
Continuity of `F` upgrades this to `stripHomeomorph` below. -/
def stripEquiv (a : ℝ) :
    strip (F := F) a ≃ stripBase F a where
  toFun q := ⟨projection q.val, by
    have h := (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).map_source q.property
    change (height q.val : AddCircle (2 * Real.pi)) ∈ (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).target at h
    change (F (projection q.val)).2.2 ∈ (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).target
    simpa only [height, projection, q.val.property] using h⟩
  invFun p := ⟨⟨(p.val, (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).symm
      (F p.val).2.2), (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).right_inv p.property⟩,
    (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).map_target p.property⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).symm
        (F (projection q.val)).2.2 = height q.val
      dsimp only [projection, height]
      rw [← q.val.property]
      exact (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).left_inv q.property
  right_inv p := by rfl

/-- The strip equivalence respects the inherited topologies. -/
def stripHomeomorph (hF : Continuous F) (a : ℝ) :
    strip (F := F) a ≃ₜ stripBase F a where
  toEquiv := stripEquiv a
  continuous_toFun := (continuous_projection.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    have hc : Continuous (fun p : stripBase F a =>
        (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).symm (F p.val).2.2) :=
      (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a).continuousOn_invFun.comp_continuous
        (hF.snd.snd.comp continuous_subtype_val) (fun p => p.property)
    exact ((continuous_subtype_val.prodMk hc).subtype_mk _).subtype_mk _

omit [TopologicalSpace P] in
/-- These strip charts cover the intrinsic lift. -/
lemma mem_centered_strip (q : HeightLift F) : q ∈ strip (height q - Real.pi) := by
  change height q ∈ Set.Ioo (height q - Real.pi) (height q - Real.pi + 2 * Real.pi)
  constructor <;> linarith [Real.pi_pos]

/-- The lift projection is locally a homeomorphism. -/
theorem projection_isLocalHomeomorph (hF : Continuous F) :
    IsLocalHomeomorph (projection (F := F)) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro q
  refine ⟨strip (height q - Real.pi),
    (isOpen_strip _).mem_nhds (mem_centered_strip q), ?_⟩
  exact (isOpen_stripBase hF _).isOpenEmbedding_subtypeVal.comp
    (stripHomeomorph hF _).isOpenEmbedding

/-- The intrinsic projection has the quotient topology of its parameter carrier. -/
theorem projection_isQuotientMap (hF : Continuous F) :
    IsQuotientMap (projection (F := F)) :=
  (projection_isLocalHomeomorph hF).isOpenMap.isQuotientMap
    continuous_projection projection_surjective

/-- Orbit quotients carry their ordinary quotient topology. -/
instance periodQuotientTopology (m : ℕ) : TopologicalSpace (PeriodQuotient F m) :=
  inferInstanceAs (TopologicalSpace (Quotient (periodSetoid (F := F) m)))

/-- The one-period quotient recovers the parameter carrier topologically. -/
def onePeriodHomeomorph (hF : Continuous F) : PeriodQuotient F 1 ≃ₜ P :=
  (onePeriodEquiv (F := F)).toHomeomorph fun s => by
    have hq : IsQuotientMap (fun q : HeightLift F =>
        (Quotient.mk (periodSetoid 1) q : PeriodQuotient F 1)) :=
      isQuotientMap_quotient_mk'
    exact hq.isOpen_preimage.symm.trans (projection_isQuotientMap hF).isOpen_preimage

end KsIndex.KarcherData.HeightLift

namespace KsIndex.KarcherData

/-- The actual EW lift has local projection charts and the correct one-period
quotient topology. This does not assert connectedness or a global trivialization. -/
theorem exists_periodicEW_local_charts {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    ∃ C : PeriodTarget,
      IsLocalHomeomorph (HeightLift.projection (F := extendedEWMap hk b C)) ∧
      Nonempty (HeightLift.PeriodQuotient (extendedEWMap hk b C) 1 ≃ₜ ParameterSphere k) := by
  obtain ⟨C, hC, _⟩ := exists_continuous_extendedEWMap hk b
  exact ⟨C, HeightLift.projection_isLocalHomeomorph hC,
    ⟨HeightLift.onePeriodHomeomorph hC⟩⟩

end KsIndex.KarcherData
