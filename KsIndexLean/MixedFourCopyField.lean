module

public import KsIndexLean.MixedFourCopySigns
public import KsIndexLean.EnergySmooth

@[expose] public section


/-! Normalized four-copy data for the mixed continuation. Smooth seam matching
is a separate obligation; the definitions alone do not supply it. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.FaithfulInjection

/-- Four signed copies, with the surface encoding's exterior and puncture normalization. -/
def dnFourCopy (k : ℕ) (H : ℂ → ℂ) (n : ZMod 4) (z : ℂ) : ℂ := by
  classical
  exact if ‖z‖ ≤ 1 ∧ z ∉ punctures k then dnCopySign n * H z else 0

lemma dnFourCopy_punctureZero (k : ℕ) (H : ℂ → ℂ) :
    PunctureZero k (m := 2) (dnFourCopy k H) := by
  intro n z hz
  simp [dnFourCopy, hz]

lemma dnFourCopy_exterior (k : ℕ) (H : ℂ → ℂ) (n : ZMod 4)
    {z : ℂ} (hz : 1 < ‖z‖) : dnFourCopy k H n z = 0 := by
  simp [dnFourCopy, not_le_of_gt hz]

lemma dnFourCopy_antiperiodic (k : ℕ) (H : ℂ → ℂ) (n : ZMod 4) (z : ℂ) :
    dnFourCopy k H (n + 2) z = -dnFourCopy k H n z := by
  unfold dnFourCopy
  split
  · rw [dnCopySign_add_two, neg_mul]
  · simp

lemma dnFourCopy_inner {k : ℕ} (hk : 1 ≤ k) (H : ℂ → ℂ) (n : ZMod 4) :
    EqOn (dnFourCopy k H n) (dnCopySign n • H) (disk : Set ℂ) := by
  intro z hz
  have h : ‖z‖ ≤ 1 ∧ z ∉ punctures k :=
    ⟨(mem_disk_iff.mp hz).le, punctures_notMem_disk hk hz⟩
  simp only [dnFourCopy, ite_eq_left h, Pi.smul_apply, smul_eq_mul]

/-- Finite gradient energy is preserved before any boundedness theorem is applied. -/
theorem dnFourCopy_energy {k : ℕ} (hk : 1 ≤ k) (H : ℂ → ℂ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (disk : Set ℂ))
    (hE : IntegrableOn (gradSq H) (disk : Set ℂ)) (n : ZMod 4) :
    IntegrableOn (gradSq (dnFourCopy k H n)) (disk : Set ℂ) := by
  have hi := integrableOn_gradSq_smul (dnCopySign n)
    (fun z hz => (hH.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by simp)) hE
  apply hi.congr
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
  have hg : dnFourCopy k H n =ᶠ[nhds z] dnCopySign n • H :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz) (dnFourCopy_inner hk H n)
  simp only [gradSq, hg.fderiv_eq]

end KsIndex.Trace
