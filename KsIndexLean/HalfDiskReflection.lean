module

public import KsIndexLean.HalfDiskWeakTests
public import KsIndexLean.GeneralBoundaryParity
public import KsIndexLean.SectorBoundaryAgreement

@[expose] public section


/-! Reflected smooth continuation of bounded classical half-period fields.
The original field is retained on the closed punctured disk. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace.ClassicalHalfDiskJacobi
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.WeakH1 KsIndex.FormIndex
variable {k : ℕ} {b : Bool} (u : ClassicalHalfDiskJacobi k b)

/-- A character equation in the open disk suffices for the actual weak character;
no condition on an arbitrary exterior representative is needed. -/
lemma toH1_character (hk : 2 ≤ k) (θ : ℝ) (c : ℂ)
    (hchar : ∀ w ∈ Surface.disk, u.value (planeRotation θ w) = c * u.value w) :
    u.toH1 hk ∈ weakCharacterDomain θ c := by
  apply (mem_weakCharacterDomain θ c _).mpr
  apply valueCLM_injective
  rw [map_smul]
  apply Lp.ext
  have hr := (measurePreserving_planeRotation_disk θ).quasiMeasurePreserving.ae_eq_comp
    (u.toH1_value_ae hk)
  filter_upwards [diskRotation_value_ae θ (u.toH1 hk), hr, u.toH1_value_ae hk,
    Lp.coeFn_smul c (valueCLM (u.toH1 hk)), ae_restrict_mem WeakH1.disk.isOpen.measurableSet]
      with w hrot hrw huw hcw hw
  rw [hrot,hcw]
  change valueCLM (u.toH1 hk) (planeRotation θ w) = c * valueCLM (u.toH1 hk) w
  change valueCLM (u.toH1 hk) (planeRotation θ w) = u.value (planeRotation θ w) at hrw
  rw [hrw,huw,hchar w hw]

/-- Almost-everywhere agreement with a smooth disk-neighborhood representative
upgrades to equality on the original closed punctured disk. -/
lemma closed_punctured_eq_of_ae (hk : 2 ≤ k) {H : ℂ → ℂ}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball (0 : ℂ) 2))
    (ha : valueCLM (u.toH1 hk) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H) :
    EqOn u.value H (Metric.closedBall (0 : ℂ) 1 \ punctures k) := by
  have hi : EqOn u.value H (WeakH1.disk : Set ℂ) :=
    Measure.eqOn_open_of_ae_eq ((u.toH1_value_ae hk).symm.trans ha) WeakH1.disk.isOpen
      u.smooth.continuousOn (hH.continuousOn.mono (Metric.ball_subset_ball (by norm_num)))
  intro w hw
  have hn : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall,dist_zero_right] using hw.1
  rcases lt_or_eq_of_le hn with hlt | he
  · exact hi (mem_disk_iff.mpr hlt)
  · obtain ⟨F,hF,hs,_⟩ := u.boundary w he hw.2
    apply KsIndex.NullityDecomp.boundary_eq_of_inner_eq he hF.continuousAt
      (hH.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds ?_)) hs hi
    simp [Metric.mem_ball,dist_zero_right,he]

/-- Odd continuation of a classical Dirichlet character field, with all
weak-equation and finite-energy inputs derived from its original data. -/
theorem dirichlet_reflected_extension (u : ClassicalHalfDiskJacobi k false)
    (hk : 2 ≤ k) (j : ℕ)
    (hc : ∀ w ∈ Surface.disk, u.value (planeRotation (-(2 * Real.pi) / k) w) =
      zeta k ^ j * u.value w) :
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      EqOn u.value H (Metric.closedBall (0 : ℂ) 1 \ punctures k) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C) ∧
      (∀ z ∈ seamDomain Set.univ isOpen_univ, H (Bracket.σ z) = -H z) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * H z := by
  obtain ⟨H,hH,ha,hP,hB,hr,hcH⟩ := dirichlet_radical_reflected_disk hk j (u.toH1 hk)
    (u.dirichlet_mem_zeroTrace hk) (u.toH1_character hk _ _ hc)
    (fun v hv => u.dirichlet_tests_zero hk v hv.1)
  exact ⟨H,hH,u.closed_punctured_eq_of_ae hk hH ha,hP,hB,hr,hcH⟩

/-- Even continuation of a classical Neumann character field. -/
theorem neumann_reflected_extension (u : ClassicalHalfDiskJacobi k true)
    (hk : 2 ≤ k) (j : ℕ)
    (hc : ∀ w ∈ Surface.disk, u.value (planeRotation (-(2 * Real.pi) / k) w) =
      zeta k ^ j * u.value w) :
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      EqOn u.value H (Metric.closedBall (0 : ℂ) 1 \ punctures k) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C) ∧
      (∀ z ∈ seamDomain Set.univ isOpen_univ, H (Bracket.σ z) = H z) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * H z := by
  obtain ⟨H,hH,ha,hP,hB,hr,hcH⟩ := neumann_radical_reflected_disk hk j (u.toH1 hk)
    (u.toH1_character hk _ _ hc) (fun v _ => u.neumann_tests_zero hk v)
  exact ⟨H,hH,u.closed_punctured_eq_of_ae hk hH ha,hP,hB,hr,hcH⟩

end KsIndex.Trace.ClassicalHalfDiskJacobi
