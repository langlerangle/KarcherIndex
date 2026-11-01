module

public import KsIndexLean.KarcherNeumannCore
public import KsIndexLean.KarcherHalfPeriodCharacters

@[expose] public section


/-! Natural Neumann test representatives preserve actual geometric rotation
characters. Continuous boundary limits retain the interior character equation. -/
noncomputable section
open Set Topology
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SingleDisk KsIndex.Trace KsIndex.FormIndex
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma continuous_disk_character_closed (θ : ℝ) (c : ℂ) {G : ℂ → ℂ}
    (hG : Continuous G)
    (hc : ∀ z ∈ disk, G (planeRotation θ z) = c * G z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, G (planeRotation θ z) = c * G z := by
  have he : EqOn (fun z => G (planeRotation θ z)) (fun z => c * G z) disk := hc
  apply he.of_subset_closure
    (hG.comp (planeRotation θ).continuous).continuousOn
    (continuous_const.mul hG).continuousOn Metric.ball_subset_closedBall
  change Metric.closedBall (0 : ℂ) 1 ⊆ closure (Metric.ball 0 1)
  rw [closure_ball (0 : ℂ) one_ne_zero]

lemma halfPeriodOfCoordinate_character (R : PaperHalfPeriodRealization k)
    (j : ℕ) (G : ℂ → ℂ)
    (hc : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      G (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * G z) :
    ∀ q, R.halfPeriodOfCoordinate G (R.halfPeriodRotation q) =
      zeta k ^ j * R.halfPeriodOfCoordinate G q := by
  intro q
  change G (R.diskHomeomorph (R.halfPeriodRotation q)).val.val =
    zeta k ^ j * G (R.diskHomeomorph q).val.val
  have hr : (R.diskHomeomorph (R.halfPeriodRotation q)).val.val =
      planeRotation (-(2 * Real.pi) / k) (R.diskHomeomorph q).val.val := by
    have hh := R.diskRotation_coordinate (R.diskHomeomorph q)
    simpa only [diskRotation,Homeomorph.symm_apply_apply,planeRotation_apply,neg_mul] using hh
  rw [hr]
  exact hc _ (by simpa only [Metric.mem_closedBall,dist_zero_right]
    using (R.diskHomeomorph q).property)

/-- Natural test functions in a character class admit actual geometric test
representatives in the same class, including their boundary values. -/
lemma exists_neumannTest_character_of_nat (R : PaperHalfPeriodRealization k)
    (j : ℕ) {g : ℂ → ℂ} (hg : g ∈ NatCc k true true)
    (hchar : ∀ z ∈ disk, g (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * g z) :
    ∃ f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ,
      R.IsNeumannTest f ∧ EqOn g (R.halfPeriodCoordinate f) disk ∧
      ∀ q, f (R.halfPeriodRotation q) = zeta k ^ j * f q := by
  obtain ⟨G,hG,hsm,he,hB,hP⟩ :=
    exists_closed_representative (by have := h.out; omega : 1 ≤ k) hg
  have hc : ∀ z ∈ disk, G (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * G z := by
    intro z hz
    have hr : planeRotation (-(2 * Real.pi) / k) z ∈ disk := by
      rw [mem_disk_iff,(planeRotation _).norm_map]
      exact mem_disk_iff.mp hz
    rw [← he hr,← he hz]
    exact hchar z hz
  refine ⟨R.halfPeriodOfCoordinate G,
    R.neumannTest_of_closed_representative G hG hsm hB hP,?_,
    R.halfPeriodOfCoordinate_character j G
      (continuous_disk_character_closed _ _ hG hc)⟩
  intro z hz
  exact (he hz).trans (R.halfPeriodCoordinate_ofCoordinate G (mem_disk_iff.mp hz).le
    (punctures_notMem_disk (k := k) (by have := h.out; omega) hz)).symm

/-- The representative theorem consumes the existing natural-core rotation
submodule directly, with the paper's negative-angle convention. -/
lemma exists_neumannTest_of_nat_character (R : PaperHalfPeriodRealization k)
    (j : ℕ) {g : ℂ → ℂ} (hg : g ∈ NatCc k true true ⊓ Erot1 k j) :
    ∃ f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ,
      R.IsNeumannTest f ∧ EqOn g (R.halfPeriodCoordinate f) disk ∧
      ∀ q, f (R.halfPeriodRotation q) = zeta k ^ j * f q := by
  apply R.exists_neumannTest_character_of_nat j hg.1
  intro z hz
  have he := congrFun (Module.End.mem_eigenspace_iff.mp hg.2) z
  simpa only [KsIndex.SingleDiskBridge.rot1_apply,Pi.smul_apply,smul_eq_mul,
    planeRotation_apply,KsIndex.SurfaceSym.rotUnit,Circle.coe_exp] using he

end KsIndex.KarcherData.PaperHalfPeriodRealization
