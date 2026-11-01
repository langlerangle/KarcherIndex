module

public import KsIndexLean.KarcherPureReflectedLift
public import KsIndexLean.PureSectorRadicalEquivalence

@[expose] public section


/-! Actual pure-boundary weak radicals lift to bounded fields on the EW
quotient. The one-period case is available by specializing the period to one. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.NullityDecomp
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex KsIndex.Spectral

/-- A representative with all local data required by the geometric producer. -/
theorem pure_radical_reflected_representative {k r s : ℕ} (hk : 2 ≤ k) (hs : s < 2)
    (u : pureSectorRadical k r s) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2) ∧
      valueCLM u.val.val =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f ∧
      (∀ w ∈ (Surface.disk : Set ℂ), laplacian f w + (potV k w : ℂ) * f w = 0) ∧
      (∃ C : ℝ, ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖f w‖ ≤ C) ∧
      (∀ w ∈ seamDomain Set.univ isOpen_univ, f (Bracket.σ w) = zeta 2 ^ s * f w) ∧
      ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
        f (planeRotation (-(2 * Real.pi) / k) w) = (zeta k ^ r) * f w := by
  have hQ : ∀ v : mixedCharacterDomain k r (decide (s = 0)) (decide (s = 0)),
      weakJacobi (surfacePotential k) u.val.val v.val = 0 :=
    (mem_formRadical _ _).mp u.property
  interval_cases s
  · have hN : ∀ v : ComplexH1,
        v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r) →
        weakJacobi (surfacePotential k) u.val.val v = 0 := by
      intro v hv
      exact hQ ⟨v, ⟨(mixedTraceDomain_NN k).symm ▸ Submodule.mem_top, hv⟩⟩
    obtain ⟨f, hsm, ha, hP, hb, hf, hr⟩ :=
      neumann_radical_reflected_disk hk r u.val.val u.val.property.2 hN
    refine ⟨f, hsm, ha, ?_, hb, ?_, hr⟩
    · exact fun w hw => hP w (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hw)
    · simpa only [pow_zero, one_mul] using hf
  · have hu : u.val.val ∈ zeroTraceDomain Set.univ ⊓
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r) := by
      have h := u.val.property
      change u.val.val ∈ mixedCharacterDomain k r false false at h
      rwa [mixedDD_eq_fullDirichletCharacter (by omega)] at h
    have hD : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r) →
        weakJacobi (surfacePotential k) u.val.val v = 0 := by
      intro v hv
      apply hQ ⟨v, ?_⟩
      change v ∈ mixedCharacterDomain k r false false
      rwa [mixedDD_eq_fullDirichletCharacter (by omega)]
    obtain ⟨f, hsm, ha, hP, hb, hf, hr⟩ :=
      dirichlet_radical_reflected_disk hk r u.val.val hu.1 hu.2 hD
    refine ⟨f, hsm, ha, ?_, hb, ?_, hr⟩
    · exact fun w hw => hP w (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hw)
    · simpa only [pow_one, Bracket.zeta_two, neg_one_mul] using hf

end KsIndex.NullityDecomp
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex KsIndex.NullityDecomp
variable {k m r s : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- A weak pure-boundary kernel vector produces a genuine bounded geometric
Jacobi field, with its exact disk values and all required reflection characters. -/
theorem pure_radical_geometric_lift (R : PaperHalfPeriodRealization k) (hs : s < 2)
    (u : pureSectorRadical k r s) :
    ∃ f : ℂ → ℂ, ∃ G : R.boundedGeometricJacobi (m := m),
      ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2) ∧
      (valueCLM u.val.val =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f) ∧
      (∀ w : PuncturedClosedDisk k, (R.diskFunctionPullback G.val).val (0, w) = f w.val.val) ∧
      (∀ q, G.val (HeightLift.periodDeck m 1 q) = G.val q) ∧
      (∀ q, G.val (R.periodRotation m q) = (zeta k ^ r) * G.val q) ∧
      ∀ q, G.val (R.periodHeightReflection m q) = (zeta 2 ^ s) * G.val q := by
  obtain ⟨f, hsm, ha, hP, hb, hf, hr⟩ := pure_radical_reflected_representative h.out hs u
  have hε : zeta 2 ^ s = 1 ∨ zeta 2 ^ s = -1 := by
    interval_cases s <;> simp [Bracket.zeta_two]
  obtain ⟨G, hval, ht, hrot, href⟩ :=
    R.reflected_disk_geometric_lift (m := m) (zeta 2 ^ s) (zeta k ^ r) hε f hsm hf hb hP hr
  exact ⟨f, G, hsm, ha, hval, ht, hrot, href⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
