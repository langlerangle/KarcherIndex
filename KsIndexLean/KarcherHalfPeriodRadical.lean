module

public import KsIndexLean.KarcherHalfPeriodCharacters
public import KsIndexLean.PureBoundaryClassicalEquivalence

@[expose] public section


/-! Exact correspondence between actual classical pure-boundary half-period
character fields and their full-test weak Jacobi radicals. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex KsIndex.Spectral KsIndex.Surface
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma halfPeriodWeakRadical_classical {j : ℕ} {b : Bool}
    (u : halfPeriodWeakRadical k j b) :
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      valueCLM u.val.val =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → if b then fderiv ℝ H z z = 0 else H z = 0) ∧
      (∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * H z := by
  have hQ := (mem_formRadical _ _).mp u.property
  cases b
  · have hi : mixedCharacterDomain k j false false ≤
        zeroTraceDomain Set.univ ⊓ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) :=
      (mixedDD_eq_fullDirichletCharacter (by have := h.out; omega) j).le
    have hu := hi u.val.property
    have he := (dirichlet_radical_iff_classical h.out j u.val.val hu.2).mp
      ⟨hu.1,fun v hv => hQ ⟨v,by
        rw [mixedDD_eq_fullDirichletCharacter (by have := h.out; omega)]
        exact hv⟩⟩
    simpa only [Bool.false_eq_true,ite_false] using he
  · have he := (neumann_radical_iff_classical h.out j u.val.val u.val.property.2).mp
      (fun v hv => hQ ⟨v,⟨(mixedTraceDomain_NN k).symm ▸ Submodule.mem_top,hv⟩⟩)
    simpa only [ite_true] using he

/-- Every weak kernel element is the weak representative of an actual bounded
classical field with the same geometric rotation character. -/
theorem classicalHalfPeriodToRadical_surjective (R : PaperHalfPeriodRealization k)
    (b : Bool) (j : ℕ) : Function.Surjective (R.classicalHalfPeriodToRadical b j) := by
  intro u
  obtain ⟨H,hH,ha,hP,hBC,⟨C,hC⟩,hc⟩ := halfPeriodWeakRadical_classical u
  let v : ClassicalHalfDiskJacobi k b := {
    value := H
    smooth := hH.mono (Metric.ball_subset_ball (by norm_num))
    bounded := ⟨C,fun z hz _ => hC z (by simpa [Metric.mem_closedBall,dist_zero_right] using hz)⟩
    equation := fun z hz => hP z (Metric.ball_subset_ball (by norm_num) hz)
    boundary := fun z hz _ => ⟨H,hH.contDiffAt (Metric.isOpen_ball.mem_nhds
      (by simp [Metric.mem_ball,dist_zero_right,hz])),
      Filter.Eventually.of_forall (fun _ _ => rfl),hBC z hz⟩ }
  have hv : v.toH1 h.out = u.val.val :=
    valueCLM_injective (Lp.ext ((v.toH1_value_ae h.out).trans ha.symm))
  let V := R.classicalCharacterOfDisk j v hc
  have he : (R.classicalHalfPeriodToRadical b j V).val.val = u.val.val :=
    (R.classicalHalfPeriodToRadical_value b j V).trans
      ((R.classicalCharacterOfDisk_toH1 j v hc).trans hv)
  exact ⟨V,Subtype.ext (Subtype.ext he)⟩

/-- The equivalence uses the actual coordinate weak representative as its
forward map; its inverse is supplied by proved regularity and boundary data. -/
def classicalHalfPeriodRadicalEquiv (R : PaperHalfPeriodRealization k) (b : Bool) (j : ℕ) :
    R.classicalHalfPeriodCharacter b j ≃ₗ[ℂ] halfPeriodWeakRadical k j b :=
  LinearEquiv.ofBijective (R.classicalHalfPeriodToRadical b j)
    ⟨R.classicalHalfPeriodToRadical_injective b j,R.classicalHalfPeriodToRadical_surjective b j⟩

/-- Exact nullity equality with the pure-boundary disk weak problem. -/
theorem classical_halfPeriod_nullity_eq (R : PaperHalfPeriodRealization k) (b : Bool) (j : ℕ) :
    Cardinal.toENat (Module.rank ℂ (R.classicalHalfPeriodCharacter b j)) =
      (diskWeakNullity (mixedCharacterDomain k j b b) (surfacePotential k) : ℕ∞) := by
  have hf : FiniteDimensional ℂ (halfPeriodWeakRadical k j b) := diskRadical_finiteDimensional _ _
  rw [(R.classicalHalfPeriodRadicalEquiv b j).rank_eq,
    ← Module.finrank_eq_rank ℂ (halfPeriodWeakRadical k j b)]
  simp [diskWeakNullity,halfPeriodWeakRadical]

end KsIndex.KarcherData.PaperHalfPeriodRealization
