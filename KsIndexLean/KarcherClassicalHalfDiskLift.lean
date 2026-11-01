module

public import KsIndexLean.HalfDiskReflection
public import KsIndexLean.KarcherPureReflectedLift

@[expose] public section


/-! Bounded classical half-period coordinate fields extend to the actual
EW quotient with prescribed reflection and rotation characters. -/
noncomputable section
open Set
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Surface KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- The odd geometric lift retains the original Dirichlet field on its
entire closed punctured half-period. -/
theorem classical_dirichlet_geometric_lift (R : PaperHalfPeriodRealization k)
    (u : ClassicalHalfDiskJacobi k false) (j : ℕ)
    (hc : ∀ w ∈ Surface.disk, u.value (planeRotation (-(2 * Real.pi) / k) w) =
      zeta k ^ j * u.value w) :
    ∃ G : R.boundedGeometricJacobi (m := m),
      (∀ w : PuncturedClosedDisk k, (R.diskFunctionPullback G.val).val (0,w) = u.value w.val.val) ∧
      (∀ q, G.val (HeightLift.periodDeck m 1 q) = G.val q) ∧
      (∀ q, G.val (R.periodRotation m q) = zeta k ^ j * G.val q) ∧
      ∀ q, G.val (R.periodHeightReflection m q) = -G.val q := by
  obtain ⟨H,hH,he,hP,hB,hr,hcH⟩ := u.dirichlet_reflected_extension h.out j hc
  obtain ⟨G,hG,hT,hR,hS⟩ := R.reflected_disk_geometric_lift (m := m) (-1) (zeta k ^ j)
    (Or.inr rfl) H hH (fun w hw => by simpa only [neg_one_mul] using hr w hw)
    hB (fun w hw => hP w (Metric.ball_subset_ball (by norm_num) hw)) hcH
  refine ⟨G,?_,hT,hR,?_⟩
  · intro w
    exact (hG w).trans (he ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using w.property,w.val.property⟩).symm
  · simpa only [neg_one_mul] using hS

/-- The even geometric lift retains the original Neumann field. -/
theorem classical_neumann_geometric_lift (R : PaperHalfPeriodRealization k)
    (u : ClassicalHalfDiskJacobi k true) (j : ℕ)
    (hc : ∀ w ∈ Surface.disk, u.value (planeRotation (-(2 * Real.pi) / k) w) =
      zeta k ^ j * u.value w) :
    ∃ G : R.boundedGeometricJacobi (m := m),
      (∀ w : PuncturedClosedDisk k, (R.diskFunctionPullback G.val).val (0,w) = u.value w.val.val) ∧
      (∀ q, G.val (HeightLift.periodDeck m 1 q) = G.val q) ∧
      (∀ q, G.val (R.periodRotation m q) = zeta k ^ j * G.val q) ∧
      ∀ q, G.val (R.periodHeightReflection m q) = G.val q := by
  obtain ⟨H,hH,he,hP,hB,hr,hcH⟩ := u.neumann_reflected_extension h.out j hc
  obtain ⟨G,hG,hT,hR,hS⟩ := R.reflected_disk_geometric_lift (m := m) 1 (zeta k ^ j)
    (Or.inl rfl) H hH (fun w hw => by simpa only [one_mul] using hr w hw)
    hB (fun w hw => hP w (Metric.ball_subset_ball (by norm_num) hw)) hcH
  refine ⟨G,?_,hT,hR,?_⟩
  · intro w
    exact (hG w).trans (he ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using w.property,w.val.property⟩).symm
  · simpa only [one_mul] using hS

end KsIndex.KarcherData.PaperHalfPeriodRealization
