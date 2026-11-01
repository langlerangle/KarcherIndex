module

public import KsIndexLean.KarcherHalfPeriodSmoothGerm

@[expose] public section


/-! Intrinsic smoothness of compact tests on the actual open half-period. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

def HasSmoothOpenHalfPeriodGerm (R : PaperHalfPeriodRealization k)
    (f : R.OpenHalfPeriod → ℂ) (q : R.OpenHalfPeriod) : Prop :=
  letI := HeightLift.liftChartedSpace R.hC
  ∃ F : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ℂ,
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F q.val.val ∧
      ∀ᶠ r in 𝓝 q, f r = F r.val.val

theorem smoothOpenHalfPeriodGerm_iff_coordinate (R : PaperHalfPeriodRealization k)
    (f : R.OpenHalfPeriod → ℂ) (q : R.OpenHalfPeriod) :
    R.HasSmoothOpenHalfPeriodGerm f q ↔
      ContDiffAt ℝ ∞ (R.openHalfPeriodCoordinate f) (R.openDiskHomeomorph q).val := by
  let := HeightLift.liftChartedSpace R.hC
  let := R.geometry.1
  let c := HeightLift.liftChart R.hC q.val.val
  have hchart : chartAt ℂ q.val.val = c := rfl
  have hq : q.val.val ∈ c.source := HeightLift.liftChart_mem R.hC q.val.val
  have hc : c q.val.val = (R.openDiskHomeomorph q).val :=
    R.openHalfPeriod_liftChart_coordinate q.val q
  constructor
  · rintro ⟨F,hF,he⟩
    let G := F ∘ c.symm
    have hG : ContDiffAt ℝ ∞ G (R.openDiskHomeomorph q).val := by
      rw [contMDiffAt_iff_source] at hF
      have hs : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G Set.univ (c q.val.val) := by
        simpa only [mfld_simps,hchart] using hF
      rw [hc] at hs
      exact (hs.contMDiffAt Filter.univ_mem).contDiffAt
    have hn : ∀ᶠ r in 𝓝 q, r.val.val ∈ c.source :=
      ((continuous_subtype_val : Continuous (fun r : PaperHalfPeriod h.out (reflectionBasepoint k) R.C => r.val)).comp
        (continuous_subtype_val : Continuous (fun r : R.OpenHalfPeriod => r.val))).continuousAt
        (c.open_source.mem_nhds hq)
    have he' : ∀ᶠ r in 𝓝 q, f r = G (R.openDiskHomeomorph r).val := by
      filter_upwards [he,hn] with r hr hrs
      rw [hr,← R.openHalfPeriod_liftChart_coordinate q.val r]
      exact congrArg F (c.left_inv hrs).symm
    have hi : IsEmbedding (fun r : R.OpenHalfPeriod => (R.openDiskHomeomorph r).val) :=
      (IsEmbedding.subtypeVal : IsEmbedding (fun z : Surface.disk => z.val)).comp
        R.openDiskHomeomorph.isEmbedding
    rw [hi.toIsInducing.nhds_eq_comap] at he'
    have hh := Filter.eventually_comap.mp he'
    apply hG.congr_of_eventuallyEq
    filter_upwards [hh,Metric.isOpen_ball.mem_nhds (R.openDiskHomeomorph q).property] with z hz hd
    let w : Surface.disk := ⟨z,hd⟩
    have hw : (R.openDiskHomeomorph (R.openDiskHomeomorph.symm w)).val = z := by
      rw [R.openDiskHomeomorph.apply_symm_apply]
    have heq := hz (R.openDiskHomeomorph.symm w) hw
    rw [hw] at heq
    exact (R.openHalfPeriodCoordinate_apply f w).trans heq
  · intro hf
    refine ⟨R.openHalfPeriodCoordinate f ∘ c,?_,?_⟩
    · have hs := (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := q.val.val)).contMDiffAt
        (c.open_source.mem_nhds hq)
      have hg : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (R.openHalfPeriodCoordinate f) (c q.val.val) := by
        rw [hc]
        exact hf.contMDiffAt
      exact hg.comp q.val.val hs
    · apply Filter.Eventually.of_forall
      intro r
      change f r = R.openHalfPeriodCoordinate f (c r.val.val)
      rw [R.openHalfPeriod_liftChart_coordinate q.val r,R.openHalfPeriodCoordinate_apply,
        Homeomorph.symm_apply_apply]

theorem mem_dirichletTests_iff_intrinsic (R : PaperHalfPeriodRealization k)
    (f : R.OpenHalfPeriod → ℂ) :
    f ∈ R.dirichletTests ↔ HasCompactSupport f ∧ ∀ q, R.HasSmoothOpenHalfPeriodGerm f q := by
  rw [R.mem_dirichletTests]
  apply and_congr_right
  intro _
  constructor
  · intro hf q
    apply (R.smoothOpenHalfPeriodGerm_iff_coordinate f q).mpr
    exact hf.contDiffAt (Metric.isOpen_ball.mem_nhds (R.openDiskHomeomorph q).property)
  · intro hf z hz
    let w : Surface.disk := ⟨z,hz⟩
    have hs := (R.smoothOpenHalfPeriodGerm_iff_coordinate f (R.openDiskHomeomorph.symm w)).mp
      (hf (R.openDiskHomeomorph.symm w))
    simp only [Homeomorph.apply_symm_apply] at hs
    exact hs.contDiffWithinAt

end KsIndex.KarcherData.PaperHalfPeriodRealization
