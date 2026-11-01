module

public import KsIndexLean.KarcherHalfPeriodSupport
public import KsIndexLean.KarcherHalfPeriodClassicalInverse
public import KsIndexLean.NaturalCoreClosedRepresentative

@[expose] public section


/-! Compact smooth test fields on the closed geometric half-period.
Neumann here specifies the test domain, not a zero normal derivative. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.Bracket KsIndex.SingleDisk
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Smoothness up to the boundary is expressed by closed-side coordinate germs.
No Jacobi equation or normal derivative condition is imposed on test fields. -/
def IsNeumannTest (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) : Prop :=
  Continuous f ∧ HasCompactSupport f ∧
    ContDiffOn ℝ ∞ (R.halfPeriodCoordinate f) disk ∧
    ∀ w : PuncturedClosedDisk k, ‖w.val.val‖ = 1 →
      ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w.val.val ∧
        ∀ᶠ z in 𝓝 w.val.val, ‖z‖ ≤ 1 → R.halfPeriodCoordinate f z = F z

lemma neumannTest_to_nat (R : PaperHalfPeriodRealization k)
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    (hf : R.IsNeumannTest f) : R.halfPeriodCoordinate f ∈ NatCc k true true := by
  have hP := (R.halfPeriod_hasCompactSupport_iff f).mp hf.2.1
  have hb : ∀ w : ℂ, ‖w‖ = 1 → OneSided (R.halfPeriodCoordinate f) w := by
    intro w hw
    by_cases hp : w ∈ punctures k
    · obtain ⟨ε,hε,hv⟩ := hP
      refine ⟨0,contDiffAt_const,?_⟩
      filter_upwards [Metric.ball_mem_nhds w hε] with z hz hd
      exact hv z ⟨w,hp,by simpa only [Metric.mem_ball,dist_eq_norm] using hz⟩
    · obtain ⟨F,hF,he⟩ := hf.2.2.2 ⟨⟨w,hp⟩,hw.le⟩ hw
      refine ⟨F,hF,?_⟩
      filter_upwards [he] with z hz hd
      exact hz (mem_disk_iff.mp hd).le
  apply mem_NatCc.mpr
  refine ⟨hf.2.2.1,(fun w hw => hb w hw.1),(fun w hw => hb w hw.1),?_,hP⟩
  intro w hw
  classical
  simp only [halfPeriodCoordinate]
  split_ifs with hh
  · exact False.elim ((not_le_of_gt hw) hh.1)
  · rfl

/-- A continuous closed-disk representative with smooth boundary germs and
uniform end vanishing defines an actual compact smooth test field. -/
lemma neumannTest_of_closed_representative (R : PaperHalfPeriodRealization k)
    (G : ℂ → ℂ) (hG : Continuous G) (hsm : ContDiffOn ℝ ∞ G disk)
    (hB : ∀ w : ℂ, ‖w‖ = 1 → ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w ∧
      ∀ᶠ z in 𝓝 w, ‖z‖ ≤ 1 → G z = F z)
    (hends : ∃ ε > 0, ∀ z : ℂ, ‖z‖ ≤ 1 →
      (∃ p ∈ punctures k, ‖z-p‖ < ε) → G z = 0) :
    R.IsNeumannTest (R.halfPeriodOfCoordinate G) := by
  obtain ⟨ε,hε,hP⟩ := hends
  let f := R.halfPeriodOfCoordinate G
  have hd : EqOn (R.halfPeriodCoordinate f) G disk := by
    intro z hz
    exact R.halfPeriodCoordinate_ofCoordinate G (mem_disk_iff.mp hz).le
      (punctures_notMem_disk (k := k) (by have := h.out; omega) hz)
  refine ⟨?_,?_,hsm.congr (fun z hz => hd hz),?_⟩
  · have hv : IsEmbedding (fun w : PuncturedClosedDisk k => w.val.val) :=
      IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
    exact hG.comp (hv.continuous.comp R.diskHomeomorph.continuous)
  · apply (R.halfPeriod_hasCompactSupport_iff f).mpr
    refine ⟨ε,hε,fun z hz => ?_⟩
    classical
    unfold halfPeriodCoordinate
    split_ifs with hh
    · have hh' := R.halfPeriodCoordinate_ofCoordinate G hh.1 hh.2
      have hn := hP z hh.1 hz
      change f (R.diskHomeomorph.symm ⟨⟨z,hh.2⟩,hh.1⟩) = 0
      exact (R.halfPeriodCoordinate_apply f ⟨⟨z,hh.2⟩,hh.1⟩).symm.trans (hh'.trans hn)
    · rfl
  · intro w hw
    obtain ⟨F,hF,hs⟩ := hB w.val.val hw
    refine ⟨F,hF,?_⟩
    have ho : IsOpen {z : ℂ | z ∉ punctures k} :=
      isOpen_ne_fun (continuous_id.pow (2 * k)) continuous_const
    filter_upwards [hs,ho.mem_nhds w.val.property] with z hz hp
    intro hn
    exact (R.halfPeriodCoordinate_ofCoordinate G hn hp).trans (hz hn)

/-- Every raw natural Neumann test comes from a genuine compact smooth field,
with equality on the open disk. Arbitrary raw boundary values are discarded. -/
lemma exists_neumannTest_of_nat (R : PaperHalfPeriodRealization k)
    {g : ℂ → ℂ} (hg : g ∈ NatCc k true true) :
    ∃ f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ,
      R.IsNeumannTest f ∧ EqOn g (R.halfPeriodCoordinate f) disk := by
  obtain ⟨G,hG,hsm,he,hB,hP⟩ :=
    exists_closed_representative (by have := h.out; omega : 1 ≤ k) hg
  refine ⟨R.halfPeriodOfCoordinate G,
    R.neumannTest_of_closed_representative G hG hsm hB hP,?_⟩
  intro z hz
  exact (he hz).trans (R.halfPeriodCoordinate_ofCoordinate G (mem_disk_iff.mp hz).le
    (punctures_notMem_disk (k := k) (by have := h.out; omega) hz)).symm

end KsIndex.KarcherData.PaperHalfPeriodRealization
