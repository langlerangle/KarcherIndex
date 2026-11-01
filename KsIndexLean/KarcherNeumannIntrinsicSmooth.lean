module

public import KsIndexLean.KarcherHalfPeriodSmoothGerm
public import KsIndexLean.KarcherNeumannTestSpace

@[expose] public section


/-! Compact Neumann tests admit smooth local extensions on the actual surface. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma halfPeriodCoordinate_continuous (R : PaperHalfPeriodRealization k) :
    Continuous (fun q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C =>
      (R.diskHomeomorph q).val.val) :=
  (continuous_subtype_val : Continuous (fun w : PuncturedPlane k => w.val)).comp
    ((continuous_subtype_val : Continuous (fun w : PuncturedClosedDisk k => w.val)).comp
      R.diskHomeomorph.continuous)

theorem hasSmoothHalfPeriodGerm_of_coordinate (R : PaperHalfPeriodRealization k)
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    (hsm : ContDiffOn ℝ ∞ (R.halfPeriodCoordinate f) Surface.disk)
    (hbd : ∀ w : PuncturedClosedDisk k, ‖w.val.val‖ = 1 →
      ∃ G : ℂ → ℂ, ContDiffAt ℝ ∞ G w.val.val ∧
        ∀ᶠ z in 𝓝 w.val.val, ‖z‖ ≤ 1 → R.halfPeriodCoordinate f z = G z)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    R.HasSmoothHalfPeriodGerm f q := by
  apply (R.smoothHalfPeriodGerm_iff_coordinate f q).mpr
  have he (r : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
      R.halfPeriodCoordinate f (R.diskHomeomorph r).val.val = f r := by
    exact (R.halfPeriodCoordinate_apply f (R.diskHomeomorph r)).trans
      (congrArg f (R.diskHomeomorph.symm_apply_apply r))
  by_cases hi : ‖(R.diskHomeomorph q).val.val‖ < 1
  · refine ⟨R.halfPeriodCoordinate f,?_,Filter.Eventually.of_forall (fun r => (he r).symm)⟩
    exact hsm.contDiffAt (Metric.isOpen_ball.mem_nhds (SurfaceForm.mem_disk_iff.mpr hi))
  · have hb : ‖(R.diskHomeomorph q).val.val‖ = 1 :=
      le_antisymm (R.diskHomeomorph q).property (le_of_not_gt hi)
    obtain ⟨G,hG,hge⟩ := hbd (R.diskHomeomorph q) hb
    refine ⟨G,hG,?_⟩
    have hg := R.halfPeriodCoordinate_continuous.continuousAt hge
    filter_upwards [hg] with r hr
    exact (he r).symm.trans (hr (R.diskHomeomorph r).property)

theorem neumannTest_hasSmoothGerm (R : PaperHalfPeriodRealization k)
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    (hf : R.IsNeumannTest f) (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    R.HasSmoothHalfPeriodGerm f q :=
  R.hasSmoothHalfPeriodGerm_of_coordinate hf.2.2.1 hf.2.2.2 q

theorem ClassicalHalfPeriodJacobi.hasSmoothGerm {R : PaperHalfPeriodRealization k}
    {b : Bool} (u : R.ClassicalHalfPeriodJacobi b)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    R.HasSmoothHalfPeriodGerm u.value q := by
  apply R.hasSmoothHalfPeriodGerm_of_coordinate u.smooth _ q
  intro w hw
  obtain ⟨G,hG,he,hbc⟩ := u.boundary w hw
  exact ⟨G,hG,he⟩

theorem continuous_of_smoothHalfPeriodGerms (R : PaperHalfPeriodRealization k)
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    (hf : ∀ q, R.HasSmoothHalfPeriodGerm f q) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨G,hG,he⟩ := (R.smoothHalfPeriodGerm_iff_coordinate f q).mp (hf q)
  have hc : ContinuousAt (fun r => G (R.diskHomeomorph r).val.val) q :=
    ContinuousAt.comp (f := fun r => (R.diskHomeomorph r).val.val)
      hG.continuousAt R.halfPeriodCoordinate_continuous.continuousAt
  exact hc.congr_of_eventuallyEq he

lemma smoothHalfPeriodGerm_closed_coordinate (R : PaperHalfPeriodRealization k)
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    {q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C}
    (hf : R.HasSmoothHalfPeriodGerm f q) :
    ∃ G : ℂ → ℂ, ContDiffAt ℝ ∞ G (R.diskHomeomorph q).val.val ∧
      ∀ᶠ z in 𝓝 (R.diskHomeomorph q).val.val,
        ‖z‖ ≤ 1 → R.halfPeriodCoordinate f z = G z := by
  obtain ⟨G,hG,he⟩ := (R.smoothHalfPeriodGerm_iff_coordinate f q).mp hf
  refine ⟨G,hG,?_⟩
  have hi : IsEmbedding (fun r : PaperHalfPeriod h.out (reflectionBasepoint k) R.C =>
      (R.diskHomeomorph r).val.val) :=
    (IsEmbedding.subtypeVal : IsEmbedding (fun w : PuncturedPlane k => w.val)).comp
      ((IsEmbedding.subtypeVal : IsEmbedding (fun w : PuncturedClosedDisk k => w.val)).comp
        R.diskHomeomorph.isEmbedding)
  rw [hi.toIsInducing.nhds_eq_comap] at he
  have hh := Filter.eventually_comap.mp he
  have ho : IsOpen {z : ℂ | z ∉ Surface.punctures k} :=
    isOpen_ne_fun (continuous_id.pow (2*k)) continuous_const
  filter_upwards [hh,ho.mem_nhds (R.diskHomeomorph q).val.property] with z hz hp
  intro hn
  let w : PuncturedClosedDisk k := ⟨⟨z,hp⟩,hn⟩
  have hw : (R.diskHomeomorph (R.diskHomeomorph.symm w)).val.val = z := by
    rw [R.diskHomeomorph.apply_symm_apply]
  have hh' := hz (R.diskHomeomorph.symm w) hw
  rw [hw] at hh'
  exact (R.halfPeriodCoordinate_apply f w).trans hh'

theorem smoothHalfPeriodGerms_iff (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) :
    (∀ q, R.HasSmoothHalfPeriodGerm f q) ↔
      ContDiffOn ℝ ∞ (R.halfPeriodCoordinate f) Surface.disk ∧
      ∀ w : PuncturedClosedDisk k, ‖w.val.val‖ = 1 →
        ∃ G : ℂ → ℂ, ContDiffAt ℝ ∞ G w.val.val ∧
          ∀ᶠ z in 𝓝 w.val.val, ‖z‖ ≤ 1 → R.halfPeriodCoordinate f z = G z := by
  constructor
  · intro hs
    constructor
    · intro z hz
      let w : PuncturedClosedDisk k :=
        ⟨⟨z,Surface.punctures_notMem_disk (k := k) (by have := h.out; omega) hz⟩,
          (SurfaceForm.mem_disk_iff.mp hz).le⟩
      obtain ⟨G,hG,he⟩ := R.smoothHalfPeriodGerm_closed_coordinate (hs (R.diskHomeomorph.symm w))
      have hw : (R.diskHomeomorph (R.diskHomeomorph.symm w)).val.val = z := by
        rw [R.diskHomeomorph.apply_symm_apply]
      rw [hw] at hG he
      apply (hG.congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [he,Metric.isOpen_ball.mem_nhds hz] with y hy hyd
      exact hy (SurfaceForm.mem_disk_iff.mp hyd).le
    · intro w hw
      obtain ⟨G,hG,he⟩ := R.smoothHalfPeriodGerm_closed_coordinate (hs (R.diskHomeomorph.symm w))
      simpa only [Homeomorph.apply_symm_apply] using (show ∃ G : ℂ → ℂ,
        ContDiffAt ℝ ∞ G (R.diskHomeomorph (R.diskHomeomorph.symm w)).val.val ∧
          ∀ᶠ z in 𝓝 (R.diskHomeomorph (R.diskHomeomorph.symm w)).val.val,
            ‖z‖ ≤ 1 → R.halfPeriodCoordinate f z = G z from ⟨G,hG,he⟩)
  · rintro ⟨hsm,hbd⟩
    exact R.hasSmoothHalfPeriodGerm_of_coordinate hsm hbd

theorem isNeumannTest_iff_intrinsic (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) :
    R.IsNeumannTest f ↔ HasCompactSupport f ∧ ∀ q, R.HasSmoothHalfPeriodGerm f q := by
  constructor
  · intro hf
    exact ⟨hf.2.1,R.neumannTest_hasSmoothGerm hf⟩
  · rintro ⟨hc,hs⟩
    exact ⟨R.continuous_of_smoothHalfPeriodGerms hs,hc,(R.smoothHalfPeriodGerms_iff f).mp hs⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
