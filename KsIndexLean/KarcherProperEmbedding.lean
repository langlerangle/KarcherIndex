module

public import KsIndexLean.KarcherSlabProperness

@[expose] public section


/-! Proper embeddedness of the normalized singly periodic EW surface. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open Set
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- A bounded Euclidean set meets only finitely many height periods. Together
with compactness in one slab this gives properness on the full carrier. -/
theorem isProperMap_centeredLiftAmbient (R : PaperHalfPeriodRealization k) :
    IsProperMap (centeredLiftAmbient (k := k) R.C R.t) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨R.continuous_centeredAmbient, ?_⟩
  intro K hK
  have hz : Continuous (fun v : AmbientTriple => v.2.2) := continuous_snd.snd
  obtain ⟨a, ha⟩ := (hK.image hz).bddBelow
  obtain ⟨b, hb⟩ := (hK.image hz).bddAbove
  let J := Icc (⌊a / (2 * Real.pi)⌋ : ℤ) ⌊b / (2 * Real.pi)⌋
  have : Fintype J := (Set.finite_Icc _ _).fintype
  let f := centeredLiftAmbient (k := k) R.C R.t
  let A := fun j : J => fun v : AmbientTriple =>
    (v.1, v.2.1, v.2.2 + ((-j.val : ℤ) : ℝ) * (2 * Real.pi))
  have hc := isCompact_restrict_of_finite_reductions R.continuous_centeredAmbient
    (hK.isClosed.preimage R.continuous_centeredAmbient)
    (fun _ hK => R.compact_periodSlab hK)
    (fun j : J => HeightLift.deck (-j.val)) (fun j : J => HeightLift.deck j.val) A
    (fun _ => HeightLift.continuous_deck _) (fun _ => by dsimp [A]; fun_prop)
    (fun j q => by rw [← HeightLift.deck_add, add_neg_cancel, HeightLift.deck_zero])
    (fun j q => R.centeredAmbient_deck (-j.val) q) (K := K)
  suffices hh : IsCompact (f ⁻¹' K ∩ f ⁻¹' K) by simpa only [inter_self] using hh
  apply hc ?_ hK
  intro q hq
  let z := HeightLift.height q + Real.pi
  let j : ℤ := ⌊z / (2 * Real.pi)⌋
  have hpi : 0 < 2 * Real.pi := by positivity
  have hzK : z ∈ (fun v : AmbientTriple => v.2.2) '' K := ⟨f q, hq, rfl⟩
  have hj : j ∈ J := ⟨Int.floor_mono (div_le_div_of_nonneg_right (ha hzK) hpi.le),
    Int.floor_mono (div_le_div_of_nonneg_right (hb hzK) hpi.le)⟩
  refine ⟨⟨j, hj⟩, ?_⟩
  change HeightLift.height (HeightLift.deck (-j) q) + Real.pi ∈ Icc 0 (2 * Real.pi)
  have hlo := (le_div_iff₀ hpi).mp (Int.floor_le (z / (2 * Real.pi)))
  have hhi := (div_lt_iff₀ hpi).mp (Int.lt_floor_add_one (z / (2 * Real.pi)))
  change (j : ℝ) * (2 * Real.pi) ≤ z at hlo
  change z < ((j : ℝ) + 1) * (2 * Real.pi) at hhi
  rw [HeightLift.height_deck]
  push_cast
  dsimp [z] at hlo hhi
  constructor <;> nlinarith

/-- The actual EW map is a homeomorphism onto a closed subset of Euclidean
space, not merely an injective immersion. -/
theorem isClosedEmbedding_centeredLiftAmbient (R : PaperHalfPeriodRealization k) :
    Topology.IsClosedEmbedding (centeredLiftAmbient (k := k) R.C R.t) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    R.continuous_centeredAmbient R.centeredLiftAmbient_injective
    R.isProperMap_centeredLiftAmbient.isClosedMap

open scoped ContDiff Manifold ParameterAtlas PeriodicAmbient

/-- The normalized EW construction is a proper smooth embedding: its actual
map is proper, is a topological embedding, and has injective differential
on the already constructed intrinsic atlas. -/
theorem proper_smooth_embedding (R : PaperHalfPeriodRealization k) :
    let := HeightLift.liftChartedSpace R.hC
    IsProperMap (centeredLiftAmbient (k := k) R.C R.t) ∧
      Topology.IsClosedEmbedding (centeredLiftAmbient (k := k) R.C R.t) ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞
        (centeredLiftAmbient (k := k) R.C R.t) ∧
      ∀ q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C,
        IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple)
          (centeredLiftAmbient (k := k) R.C R.t) q := by
  let := HeightLift.liftChartedSpace R.hC
  exact ⟨R.isProperMap_centeredLiftAmbient, R.isClosedEmbedding_centeredLiftAmbient,
    R.centered_geometry⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization

namespace KsIndex.KarcherData
open scoped ContDiff Manifold ParameterAtlas PeriodicAmbient

/-- For every k ≥ 2, the actual EW construction admits the normalized proper
smooth embedding. The realization is supplied by the EW construction itself. -/
theorem exists_proper_embedded_EW_realization {k : ℕ} [h : Fact (2 ≤ k)] :
    ∃ R : PaperHalfPeriodRealization k,
      let := HeightLift.liftChartedSpace R.hC
      IsProperMap (centeredLiftAmbient (k := k) R.C R.t) ∧
        Topology.IsClosedEmbedding (centeredLiftAmbient (k := k) R.C R.t) ∧
        ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞
          (centeredLiftAmbient (k := k) R.C R.t) ∧
        ∀ q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C,
          IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple)
            (centeredLiftAmbient (k := k) R.C R.t) q := by
  obtain ⟨R⟩ := exists_paperHalfPeriodRealization (k := k)
  exact ⟨R, R.proper_smooth_embedding⟩

end KsIndex.KarcherData
