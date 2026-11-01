module

public import KsIndexLean.PhasePairLimitIdentification
public import KsIndexLean.A3CollarConvergence

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket

/-- Package a collar-convergent sequence of actual smooth functions into disk
H1, with a prescribed weak limit. Early terms may be replaced by zero; all
sufficiently late terms retain their exact smooth values and derivatives. -/
theorem smooth_collar_carrier_tendsto {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    {J : ℂ → ℂ →L[ℝ] ℂ} (v : ComplexH1)
    (hv : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] g)
    (hx : (dxLp v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => J z 1))
    (hy : (dyLp v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => J z Complex.I))
    (hs : ∀ᶠ n in atTop, ContDiff ℝ ∞ (f n) ∧ HasCompactSupport (f n) ∧
      tsupport (f n) ⊆ annulusSet (1 / 2 : ℝ) 2)
    (hg0 : ∀ z, ‖z‖ ≤ 1 / 2 → g z = 0)
    (hJ0 : ∀ z, ‖z‖ ≤ 1 / 2 → ∀ d, J z d = 0)
    (gv : Lp ℂ 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (gD : ℂ → Lp ℂ 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (fv : ℕ → Lp ℂ 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (fD : ℕ → ℂ → Lp ℂ 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hgv : (gv : ℂ → ℂ) =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)] g)
    (hgD : ∀ d, (gD d : ℂ → ℂ) =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)]
      (fun z => J z d))
    (hfv : ∀ n, (fv n : ℂ → ℂ) =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)] f n)
    (hfD : ∀ n d, (fD n d : ℂ → ℂ) =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)]
      (fun z => fderiv ℝ (f n) z d))
    (htv : Tendsto fv atTop (𝓝 gv))
    (htD : ∀ d, Tendsto (fun n => fD n d) atTop (𝓝 (gD d))) :
    ∃ V : ℕ → ComplexH1, Tendsto V atTop (𝓝 v) ∧
      ∀ᶠ n in atTop,
        (valueCLM (V n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f n ∧
        (dxLp (V n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (f n) z 1) ∧
        (dyLp (V n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (f n) z Complex.I) := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp hs
  have hc n (hn : N ≤ n) := smooth_compactSupport_carrier (hN n hn).1 (hN n hn).2.1
  let V : ℕ → ComplexH1 := fun n => if hn : N ≤ n then Classical.choose (hc n hn) else 0
  have hspec : ∀ᶠ n in atTop,
      (valueCLM (V n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f n ∧
      (dxLp (V n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => fderiv ℝ (f n) z 1) ∧
      (dyLp (V n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => fderiv ℝ (f n) z Complex.I) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa only [V, dite_eq_left hn] using Classical.choose_spec (hc n hn)
  have hzero : ∀ᶠ n in atTop, ∀ z, ‖z‖ ≤ 1 / 2 → z ∉ tsupport (f n) := by
    filter_upwards [hs] with n hn z hz hmem
    exact (not_lt.mpr hz) (hn.2.2 hmem).1
  refine ⟨V, complexH1_tendsto_of_components ?_ ?_ ?_, hspec⟩
  · have hd := collar_diff_tendsto hfv hgv htv
    exact component_tendsto_of_collar (hspec.mono fun n h => h.1) hv
      (hzero.mono fun n h z hz => image_eq_zero_of_notMem_tsupport (h z hz))
      hg0 (Eventually.of_forall hd.1) hd.2
  · have hd := collar_diff_tendsto (fun n => hfD n 1) (hgD 1) (htD 1)
    exact component_tendsto_of_collar (hspec.mono fun n h => h.2.1) hx
      (hzero.mono fun n h z hz => fderiv_apply_eq_zero_of_notMem_tsupport (h z hz) 1)
      (fun z hz => hJ0 z hz 1) (Eventually.of_forall hd.1) hd.2
  · have hd := collar_diff_tendsto (fun n => hfD n Complex.I) (hgD Complex.I) (htD Complex.I)
    exact component_tendsto_of_collar (hspec.mono fun n h => h.2.2) hy
      (hzero.mono fun n h z hz =>
        fderiv_apply_eq_zero_of_notMem_tsupport (h z hz) Complex.I)
      (fun z hz => hJ0 z hz Complex.I) (Eventually.of_forall hd.1) hd.2

/-- The direct component of the two-sided mollification converges in the
actual disk H1 carrier, with the original localized upper value as limit. -/
theorem localized_pair_upper_h1 {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (hm : arcTrace A u = c • arcTrace A v)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (seamDomain A hA : Set ℂ)) :
    ∃ (uχ : ComplexH1) (U : ℕ → ComplexH1),
      Tendsto U atTop (𝓝 uχ) ∧
      (valueCLM uχ : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => χ z • valueCLM u z) ∧
      ∀ n,
        (valueCLM (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          compactMollify (shrinkingMollifier n) (fun z => χ z • joinedDiskValue u v c z) ∧
        (dxLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (compactMollify (shrinkingMollifier n)
            (fun z => χ z • joinedDiskValue u v c z)) z 1) ∧
        (dyLp (U n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (compactMollify (shrinkingMollifier n)
            (fun z => χ z • joinedDiskValue u v c z)) z Complex.I) := by
  have hL d : MemLp (fun z => joinedDiskJet u v c z d) 2
      (volume.restrict (seamDomain A hA : Set ℂ)) :=
    (seamDomain_jet_memLp hA u v c).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℂ d)
  obtain ⟨uχ, g, U, hg, _, ht, huχ, hU⟩ := interior_piece_carrier_tendsto hχ hc hs
    (seamDomain_weak_gluing hA u v c hm) (seamDomain_value_memLp hA u v c) hL
  refine ⟨uχ, U, ht, ?_, ?_⟩
  · filter_upwards [huχ, ae_restrict_mem KsIndex.SurfaceForm.measurableSet_disk]
      with z hz hzd
    rw [hz, joined_value_on_disk u v c hzd]
  · intro n
    simpa only [hg n] using hU n

end KsIndex.Trace
