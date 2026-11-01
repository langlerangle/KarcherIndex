module

public import KsIndexLean.KarcherHalfPeriodAtlasCoordinate
public import KsIndexLean.KarcherActualChartOverlap

@[expose] public section


/-! Local smooth extensions of half-period fields in the existing surface
atlas. At a boundary point equality is required only on the physical side. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Smoothness on a closed half-period means local extension in the actual
ambient surface, without prescribing an extension across its boundary. -/
def HasSmoothHalfPeriodGerm (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) : Prop :=
  letI := HeightLift.liftChartedSpace R.hC
  ∃ F : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ℂ,
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F q.val ∧
      ∀ᶠ r in 𝓝 q, f r = F r.val

/-- Coordinate form of the same local extension property. -/
def HasSmoothHalfPeriodCoordinateGerm (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) : Prop :=
  ∃ G : ℂ → ℂ, ContDiffAt ℝ ∞ G (R.diskHomeomorph q).val.val ∧
    ∀ᶠ r in 𝓝 q, f r = G (R.diskHomeomorph r).val.val

theorem smoothHalfPeriodGerm_iff_coordinate (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    R.HasSmoothHalfPeriodGerm f q ↔ R.HasSmoothHalfPeriodCoordinateGerm f q := by
  let := HeightLift.liftChartedSpace R.hC
  let := R.geometry.1
  let c := HeightLift.liftChart R.hC q.val
  have hchart : chartAt ℂ q.val = c := rfl
  have hq : q.val ∈ c.source := HeightLift.liftChart_mem R.hC q.val
  have hc : c q.val = (R.diskHomeomorph q).val.val := R.halfPeriod_liftChart_coordinate q q
  constructor
  · rintro ⟨F,hF,he⟩
    refine ⟨F ∘ c.symm,?_,?_⟩
    · rw [contMDiffAt_iff_source] at hF
      have hs : ContDiffAt ℝ ∞ (F ∘ c.symm) (c q.val) := by
        have hs' : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
            (F ∘ c.symm) Set.univ (c q.val) := by
          simpa only [mfld_simps,hchart] using hF
        exact (hs'.contMDiffAt Filter.univ_mem).contDiffAt
      rwa [hc] at hs
    · have hn : ∀ᶠ r in 𝓝 q, r.val ∈ c.source :=
        continuous_subtype_val.continuousAt (c.open_source.mem_nhds hq)
      filter_upwards [he,hn] with r hr hrs
      rw [hr,← R.halfPeriod_liftChart_coordinate q r]
      exact congrArg F (c.left_inv hrs).symm
  · rintro ⟨G,hG,he⟩
    refine ⟨G ∘ c,?_,?_⟩
    · have hs := (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := q.val)).contMDiffAt
        (c.open_source.mem_nhds hq)
      have hg : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G (c q.val) := by
        rw [hc]
        exact hG.contMDiffAt
      exact hg.comp q.val hs
    · filter_upwards [he] with r hr
      exact hr.trans (congrArg G (R.halfPeriod_liftChart_coordinate q r).symm)

end KsIndex.KarcherData.PaperHalfPeriodRealization
