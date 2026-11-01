module

public import KsIndexLean.SeamDomainTests
public import KsIndexLean.AnnulusIntegralSplit

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped Distributions
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface

lemma joined_jet_test_integrable {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (ψ : 𝓓(seamDomain A hA, ℂ)) :
    Integrable (jetPairing (joinedDiskJet u v c) ψ) := by
  have h (d : ℂ) : LocallyIntegrableOn
      (fun z => starRingEnd ℂ (joinedDiskJet u v c z d)) (seamDomain A hA) volume := by
    have hm := (memLp_joinedDiskJet u v c).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℂ d)
    have hi := integrableOn_annulus_of_memLp (by norm_num) (by norm_num) hm
    have hc : IntegrableOn (fun z => starRingEnd ℂ (joinedDiskJet u v c z d))
        (annulusSet (1 / 2 : ℝ) 2) :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hi
    exact hc.locallyIntegrableOn.mono_set (fun z hz => hz.1)
  have hx := (Weq.derivTest ψ 1).integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) (h 1)
  have hy := (Weq.derivTest ψ Complex.I).integrable_bilin
    (ContinuousLinearMap.mul ℝ ℂ) (h Complex.I)
  change Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z 1 *
    starRingEnd ℂ (joinedDiskJet u v c z 1)) at hx
  change Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z Complex.I *
    starRingEnd ℂ (joinedDiskJet u v c z Complex.I)) at hy
  convert hx.add hy using 1 <;> first | rfl | (funext z; simp only [jetPairing, Pi.add_apply]; ring)

lemma joined_potential_test_integrable_general (k : ℕ) (hk : 2 ≤ k) {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (ψ : 𝓓(seamDomain A hA, ℂ)) :
    Integrable (fun z => (potV k z : ℂ) * starRingEnd ℂ (joinedDiskValue u v c z) * ψ z) := by
  let τ : 𝓓(seamDomain A hA, ℂ) :=
    ⟨fun z => (potV k z : ℂ) * ψ z,
      (Complex.ofRealCLM.contDiff.comp (contDiff_potV hk)).mul ψ.contDiff,
      ψ.hasCompactSupport.mul_left, tsupport_mul_subset_right.trans ψ.tsupport_subset⟩
  have hi := integrableOn_annulus_of_memLp (by norm_num) (by norm_num)
    (memLp_joinedDiskValue u v c)
  have hc : IntegrableOn (fun z => starRingEnd ℂ (joinedDiskValue u v c z))
      (annulusSet (1 / 2 : ℝ) 2) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hi
  have hloc := hc.locallyIntegrableOn.mono_set
    (show (seamDomain A hA : Set ℂ) ⊆ annulusSet (1 / 2 : ℝ) 2 from fun z hz => hz.1)
  have hh := τ.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) hloc
  convert hh using 1
  funext z
  change _ = ((potV k z : ℂ) * ψ z) * starRingEnd ℂ (joinedDiskValue u v c z)
  ring

lemma joined_potential_test_integrable {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (ψ : 𝓓(seamDomain A hA, ℂ)) :
    Integrable (fun z => (potV 3 z : ℂ) * starRingEnd ℂ (joinedDiskValue u v c z) * ψ z) :=
  joined_potential_test_integrable_general 3 (by decide) hA u v c ψ

lemma joined_integrals_split {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (ψ : 𝓓(seamDomain A hA, ℂ)) :
    (∫ z, jetPairing (joinedDiskJet u v c) ψ z) -
      (∫ z, (potV 3 z : ℂ) * starRingEnd ℂ (joinedDiskValue u v c z) * ψ z) =
    joinedHalfResidual u v c ψ innerHalfAnnulus +
      joinedHalfResidual u v c ψ outerHalfAnnulus := by
  have hz (z : ℂ) (hn : z ∉ annulusSet (1 / 2 : ℝ) 2) : z ∉ seamDomain A hA :=
    fun h => hn h.1
  have hJ := integral_split_of_annular_support
    (joined_jet_test_integrable hA u v c ψ).integrableOn
    (fun z hn => by
      have hx := seam_test_zero_of_not_mem hA (Weq.derivTest ψ 1) (hz z hn)
      have hy := seam_test_zero_of_not_mem hA (Weq.derivTest ψ Complex.I) (hz z hn)
      change fderiv ℝ (ψ : ℂ → ℂ) z 1 = 0 at hx
      change fderiv ℝ (ψ : ℂ → ℂ) z Complex.I = 0 at hy
      simp only [jetPairing, hx, hy, mul_zero, add_zero])
  have hV := integral_split_of_annular_support
    (joined_potential_test_integrable hA u v c ψ).integrableOn
    (fun z hn => by rw [seam_test_zero_of_not_mem hA ψ (hz z hn), mul_zero])
  rw [hJ, hV]
  unfold joinedHalfResidual
  ring

end KsIndex.Trace
