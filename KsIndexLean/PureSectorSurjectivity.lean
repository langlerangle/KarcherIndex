module

public import KsIndexLean.ReflectedChainCharacters

@[expose] public section


/-! Surjectivity of disk restriction for the pure reflection sectors. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.NullityDecomp
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Surface KsIndex.SurfaceSym KsIndex.JacobiFamily KsIndex.FormIndex

/-- A reflected representative lifts into the correct sector and its H1
restriction is exactly the original vector. -/
theorem exists_sector_of_reflected_disk {k r s : ℕ} (hk : 2 ≤ k) (hs : s < 2)
    (u : ComplexH1) (f : ℂ → ℂ)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2))
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f)
    (hf : ∀ w ∈ seamDomain Set.univ isOpen_univ, f (Bracket.σ w) = zeta 2 ^ s * f w)
    (hb : ∃ C : ℝ, ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖f w‖ ≤ C)
    (hP : ∀ w ∈ (Surface.disk : Set ℂ), laplacian f w + (potV k w : ℂ) * f w = 0)
    (hr : ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
      f (planeRotation (-(2 * Real.pi) / k) w) = (zeta k ^ r) * f w) :
    ∃ W : boundedJacobiSector k r s s, sectorRestrictFun hk W = u := by
  let hε : zeta 2 ^ s = 1 ∨ zeta 2 ^ s = -1 := by
    interval_cases s <;> simp [Bracket.zeta_two]
  let V := localReflectedJacobi hk 2 (zeta 2 ^ s) hε f hsm hf hb hP
  let W : boundedJacobiSector k r s s :=
    ⟨uncurryE 2 V.val, localReflectedJacobi_sector hk hs f hsm hf hb hP hr⟩
  refine ⟨W, valueCLM_injective (Lp.ext ?_)⟩
  have hc := localReflectedJacobi_copy_zero hk 2 (zeta 2 ^ s) hε f hsm hf hb hP
  filter_upwards [sectorRestrictFun_value hk W, ha,
    ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with w hw hu hd
  exact hw.trans ((hc hd).trans hu.symm)

/-- Every pure Dirichlet weak character radical is the restriction of a
bounded Jacobi field in the odd/odd sector. -/
theorem dirichlet_sector_restriction_surjective {k r : ℕ} (hk : 2 ≤ k)
    (u : ComplexH1) (hzero : u ∈ zeroTraceDomain Set.univ)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ W : boundedJacobiSector k r 1 1, sectorRestrictFun hk W = u := by
  obtain ⟨f, hsm, ha, hP, hb, hf, hr⟩ := dirichlet_radical_reflected_disk hk r u hzero hu hQ
  apply exists_sector_of_reflected_disk hk (by decide) u f hsm ha ?_ hb ?_ hr
  · simpa only [pow_one, Bracket.zeta_two, neg_one_mul] using hf
  · exact fun w hw => hP w (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hw)

/-- Every pure Neumann weak character radical is the restriction of a
bounded Jacobi field in the even/even sector. -/
theorem neumann_sector_restriction_surjective {k r : ℕ} (hk : 2 ≤ k)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r))
    (hQ : ∀ v : ComplexH1, v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ W : boundedJacobiSector k r 0 0, sectorRestrictFun hk W = u := by
  obtain ⟨f, hsm, ha, hP, hb, hf, hr⟩ := neumann_radical_reflected_disk hk r u hu hQ
  apply exists_sector_of_reflected_disk hk (by decide) u f hsm ha ?_ hb ?_ hr
  · simpa only [pow_zero, one_mul] using hf
  · exact fun w hw => hP w (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hw)

/-- Each vector in either pure-boundary weak radical has a unique sector preimage. -/
theorem pure_sector_restriction_unique {k r s : ℕ} (hk : 2 ≤ k) (hs : s < 2)
    (u : mixedCharacterDomain k r (decide (s = 0)) (decide (s = 0)))
    (hQ : ∀ v : mixedCharacterDomain k r (decide (s = 0)) (decide (s = 0)),
      weakJacobi (surfacePotential k) u.val v.val = 0) :
    ∃! W : boundedJacobiSector k r s s, sectorRestrictFun hk W = u.val := by
  have hex : ∃ W : boundedJacobiSector k r s s, sectorRestrictFun hk W = u.val := by
    interval_cases s
    · apply neumann_sector_restriction_surjective hk u.val u.property.2
      intro v hv
      exact hQ ⟨v, ⟨(mixedTraceDomain_NN k).symm ▸ Submodule.mem_top, hv⟩⟩
    · have hu : u.val ∈ zeroTraceDomain Set.univ ⊓
          weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r) := by
        have h := u.property
        change u.val ∈ mixedCharacterDomain k r false false at h
        rwa [mixedDD_eq_fullDirichletCharacter (by omega)] at h
      apply dirichlet_sector_restriction_surjective hk u.val hu.1 hu.2
      intro v hv
      apply hQ ⟨v, ?_⟩
      change v ∈ mixedCharacterDomain k r false false
      rwa [mixedDD_eq_fullDirichletCharacter (by omega)]
  obtain ⟨W, hW⟩ := hex
  exact ⟨W, hW, fun V hV => sectorRestrict_injective hk (hV.trans hW.symm)⟩

end KsIndex.NullityDecomp
