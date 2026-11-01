module

public import KsIndexLean.MixedDiskPatch
public import KsIndexLean.MixedFourCopyField

@[expose] public section


/-! Smooth gluing of the four-copy mixed continuation. The reflected
representative is selected separately on each open seam family. -/
noncomputable section
open Set Filter Topology
namespace KsIndex.Trace
open KsIndex.Surface KsIndex.SurfaceForm

/-- A local reflected representative identifies the actual normalized glue germ. -/
lemma dnFourCopy_glue_germ {k : ℕ} (hk : 1 ≤ k) (H f F : ℂ → ℂ)
    (n : ZMod 4) (c : ℂ) {w : ℂ} (hw : ‖w‖ = 1) (hp : w ∉ punctures k)
    (hi : EqOn H f (disk : Set ℂ)) (hg : H =ᶠ[nhds w] F)
    (ho : EqOn F (fun z => c * f (Bracket.σ z)) (annulusSet 1 2))
    (hs : dnCopySign (n + 1) = dnCopySign n * c) :
    glue (m := 2) (dnFourCopy k H) n =ᶠ[nhds w] (fun z => dnCopySign n * F z) := by
  have hb : ∀ᶠ z : ℂ in nhds w, ‖z‖ < 2 :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by
      change ‖w‖ < 2
      rw [hw]
      norm_num)
  filter_upwards [hg, hb, (JacobiFamily.isClosed_punctures k).isOpen_compl.mem_nhds hp]
    with z hg hb hp
  by_cases hz : ‖z‖ ≤ 1
  · have hh : ‖z‖ ≤ 1 ∧ z ∉ punctures k := ⟨hz, hp⟩
    simp only [glue, ite_eq_left hz, dnFourCopy, ite_eq_left hh, hg]
  · have hzgt : 1 < ‖z‖ := lt_of_not_ge hz
    have hzσ : Bracket.σ z ∈ (disk : Set ℂ) := sigma_mem_disk_of_one_lt_norm hzgt
    have hnσ : ‖Bracket.σ z‖ ≤ 1 := (mem_disk_iff.mp hzσ).le
    have hpσ := punctures_notMem_disk hk hzσ
    change (if ‖z‖ ≤ 1 then dnFourCopy k H n z
      else dnFourCopy k H (n + 1) (Bracket.σ z)) = _
    rw [ite_eq_right hz]
    have hh : ‖Bracket.σ z‖ ≤ 1 ∧ Bracket.σ z ∉ punctures k := ⟨hnσ, hpσ⟩
    simp only [dnFourCopy, ite_eq_left hh]
    rw [hi hzσ, ho ⟨hzgt, hb⟩, hs, mul_assoc]

/-- The patched representative glues smoothly across all four seams. -/
theorem dnFourCopy_patch_isSmooth {k : ℕ} (hk : 1 ≤ k) (f F0 F1 : ℂ → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (disk : Set ℂ))
    (h0 : ContDiffOn ℝ (⊤ : ℕ∞) F0
      (seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0) : Set ℂ))
    (h1 : ContDiffOn ℝ (⊤ : ℕ∞) F1
      (seamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) : Set ℂ))
    (hi0 : EqOn F0 f (annulusSet (1 / 2 : ℝ) 1))
    (hi1 : EqOn F1 f (annulusSet (1 / 2 : ℝ) 1))
    (ho0 : EqOn F0 (fun z => (-1 : ℂ) * f (Bracket.σ z)) (annulusSet 1 2))
    (ho1 : EqOn F1 (fun z => (1 : ℂ) * f (Bracket.σ z)) (annulusSet 1 2)) :
    IsSmooth k 2 (dnFourCopy k (mixedDiskPatch k f F0 F1)) := by
  let H := mixedDiskPatch k f F0 F1
  have hi : EqOn H f (disk : Set ℂ) := mixedDiskPatch_inner k f F0 F1
  refine ⟨fun n => ?_, fun n w hw => ?_, dnFourCopy_exterior k H⟩
  · refine ((contDiffOn_const (c := dnCopySign n)).mul hf).congr ?_
    intro z hz
    exact (dnFourCopy_inner hk H n hz).trans (congrArg (dnCopySign n * ·) (hi hz))
  · have hp := JacobiFamily.arc_notMem_punctures hw
    have hlt := (parity 2 (n + 1)).val_lt
    have hs := dnCopySign_successor n
    by_cases hn : (parity 2 (n + 1)).val = 1
    · have hw1 : w ∈ arc k 1 := by simpa only [seamArc, hn] using hw
      have he := dnFourCopy_glue_germ hk H f F1 n 1 hw1.1 hp hi
        (mixedDiskPatch_neumann_germ k f F0 F1 hi1 hw1) ho1
        (by simpa only [ite_eq_left hn, mul_comm] using hs)
      exact (contDiffAt_const.mul (h1.contDiffAt
        ((seamDomain _ _).isOpen.mem_nhds (arc_mem_seamDomain hw1)))).congr_of_eventuallyEq he
    · have hn0 : (parity 2 (n + 1)).val = 0 := by omega
      have hw0 : w ∈ arc k 0 := by simpa only [seamArc, hn0] using hw
      have he := dnFourCopy_glue_germ hk H f F0 n (-1) hw0.1 hp hi
        (mixedDiskPatch_dirichlet_germ k f F0 F1 hi0 hw0) ho0
        (by simpa only [ite_eq_right hn, mul_comm] using hs)
      exact (contDiffAt_const.mul (h0.contDiffAt
        ((seamDomain _ _).isOpen.mem_nhds (arc_mem_seamDomain hw0)))).congr_of_eventuallyEq he

/-- Adjacent boundary values agree: the odd seam uses the actual zero value. -/
theorem dnFourCopy_patch_seamVal (k : ℕ) (f F0 F1 : ℂ → ℂ)
    (hi0 : EqOn F0 f (annulusSet (1 / 2 : ℝ) 1))
    (hzero : ∀ w ∈ arc k 0, F0 w = 0) :
    SeamVal k (m := 2) (dnFourCopy k (mixedDiskPatch k f F0 F1)) := by
  intro n w hw
  have hp := JacobiFamily.arc_notMem_punctures hw
  have hh : ‖w‖ ≤ 1 ∧ w ∉ punctures k := ⟨hw.1.le, hp⟩
  simp only [dnFourCopy, ite_eq_left hh]
  have hs := dnCopySign_successor n
  by_cases hn : (parity 2 (n + 1)).val = 1
  · simpa only [hn, ite_true, one_mul] using congrArg
      (fun c => c * mixedDiskPatch k f F0 F1 w) hs
  · have hn0 : (parity 2 (n + 1)).val = 0 := by
      have := (parity 2 (n + 1)).val_lt
      omega
    have hw0 : w ∈ arc k 0 := by simpa only [seamArc, hn0] using hw
    have hz := (mixedDiskPatch_dirichlet_germ k f F0 F1 hi0 hw0).self_of_nhds
    rw [hz, hzero w hw0, mul_zero, mul_zero]

end KsIndex.Trace
