module

public import KsIndexLean.D5Discharge
public import KsIndexLean.K3IndexAssembly
public import KsIndexLean.PaperSlitIndexAssembly
public import KsIndexLean.SectorSpectralAdditivity
public import KsIndexLean.SectorPhase

@[expose] public section


/-!
# The paper's m = 2 proof of gamma(1) < 0

This companion follows `threshold_lower_bound` in ksindexi.tex. It uses the
independently established index nine, removes the zero-phase and trivial
rotation contributions, and transports both nontrivial characters through the
actual slit adapter. The spectral companion supplies the paper's block split.
The recursive dependency check in F1PaperDependencyCheck rejects the existing
direct gamma(1) proof and all threshold/staircase classification results.
-/

noncomputable section
namespace KsIndex.GammaOnePaperRoute
open KsIndex.Spectral KsIndex.FormIndex KsIndex.Sector KsIndex.SectorForm
  KsIndex.SectorReduce KsIndex.SectorIndex KsIndex.Statements

/-- The two nontrivial characters at half phase have the same actual
slit-form index. This uses the analytic adapter, not threshold counts. -/
lemma halfPhase_character_index (j : ℕ) (hj : j = 1 ∨ j = 2) :
    formIndex (SurfaceForm.Qs 3 2) (paperSmoothJointSector 2 1 j) =
      formIndex (NQform (1 / 2)) Domς := by
  rw [paperSmoothSector_index_eq_slit]
  rw [show ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = (1 / 2 : ℝ) by norm_num]
  apply KsIndex.PaperSlitAdapter.paperSlit_index_eq_sectorClass (j := j) (1 / 2)
    (by norm_num) (by norm_num)
  rcases hj with rfl | rfl <;> norm_num [KsIndex.PaperSlitAdapter.SectorClass]

/-- Paper `threshold_lower_bound`: index nine, minus the zero-phase
contribution three and the trivial-character contribution two, leaves two
in each of the equal nontrivial characters. -/
theorem halfPhase_sector_index_eq_two :
    formIndex (NQform (1 / 2)) Domς = 2 := by
  have h := indSurface_three_unresolved_sum 2
  have h9 := KsIndex.Trace.indSurface_two_val_final (k := 3) (by decide)
  norm_num at h9
  rw [h9] at h
  norm_num [halfPhase_character_index 1 (Or.inl rfl),
    halfPhase_character_index 2 (Or.inr rfl)] at h
  have hfin : formIndex (NQform (1 / 2)) Domς ≠ ⊤ := by
    intro ht
    rw [ht] at h
    norm_num at h
  lift formIndex (NQform (1 / 2)) Domς to ℕ using hfin with n hn
  norm_cast at h ⊢
  omega

/-- At half phase the tan/cot blocks both have circle parameter squared one.
The block decomposition here is the finite-dimensional spectral paper route. -/
theorem circle_index_one_eq_one : ind 1 = 1 := by
  have h := formIndex_NQform_Domς_spectral (1 / 2)
    (by norm_num [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring])
    (by norm_num [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring])
  rw [halfPhase_sector_index_eq_two] at h
  norm_num [coefT, coefC, show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring,
    KsIndex.SectorPhase.ind_neg] at h
  have hfin : ind 1 ≠ ⊤ := by
    intro ht
    rw [ht] at h
    norm_num at h
  lift ind 1 to ℕ using hfin with n hn
  norm_cast at h ⊢
  omega

/-- The paper's lower threshold bound, independently of the direct arc-test
proof in GammaOne and of the later threshold/staircase classification. -/
theorem gam_one_neg_paper : CircleQ.gam 1 < 0 :=
  (ind_eq_one_iff (by norm_num : (0 : ℝ) < 1)).mp circle_index_one_eq_one

end KsIndex.GammaOnePaperRoute
