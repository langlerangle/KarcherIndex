module

public import KsIndexLean.WeakRealSmooth
public import KsIndexLean.WeakSmoothGluing
public import KsIndexLean.SurfacePotentialFacts
public import KsIndexLean.WeakEquationLinear
public import KsIndexLean.WeakH1Integration

@[expose] public section


/-!
# Interior regularity for the general disk Jacobi potential

For k>=2, real and complex weak solutions admit smooth interior
representatives satisfying the pointwise flat Jacobi equation. Boundary
regularity, reflection and end boundedness are separate assertions.
-/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Weq
open KsIndex.WeakH1

lemma memLp_potV_general_real {k : ℕ} (hk : 2 ≤ k) (u : RealH1) :
    MemLp (fun z => Surface.potV k z * TauCeti.W1p.value u z) 2
      (volume.restrict (disk : Set ℂ)) := by
  let V := surfacePotential k
  apply (Lp.memLp (TauCeti.W1p.value u)).of_le_mul (c := V.C)
    (V.measurable.mul (Lp.memLp (TauCeti.W1p.value u)).aestronglyMeasurable)
  filter_upwards [V.bound] with z hz
  change ‖V.V z * TauCeti.W1p.value u z‖ ≤ V.C * ‖TauCeti.W1p.value u z‖
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

/-- The actual disk potential discharges all coefficient and L²-product inputs. -/
theorem exists_smooth_near_of_general_disk_weakSol {k : ℕ} (hk : 2 ≤ k) (u : RealH1)
    (he : PunctureRemoval.IsWeakSolOn (Surface.potV k) disk u)
    {z : ℂ} (hz : z ∈ (disk : Set ℂ)) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ (disk : Set ℂ) ∧ ∃ g : ℂ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧
      (TauCeti.W1p.value u : ℂ → ℝ) =ᵐ[volume.restrict (Metric.ball z r)] g :=
  exists_smooth_near_of_isWeakSolOn u (memLp_potV_general_real hk u) he
    (Surface.contDiff_potV hk) hz

/-- Combine the real and imaginary weak solutions on a common neighborhood. -/
theorem exists_smooth_near_of_general_disk_complex_weakSol {k : ℕ} (hk : 2 ≤ k) (u : ComplexH1)
    (hr : PunctureRemoval.IsWeakSolOn (Surface.potV k) disk (rePart u))
    (hi : PunctureRemoval.IsWeakSolOn (Surface.potV k) disk (imPart u))
    {z : ℂ} (hz : z ∈ (disk : Set ℂ)) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ (disk : Set ℂ) ∧ ∃ g : ℂ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧
      value u =ᵐ[volume.restrict (Metric.ball z r)] g := by
  obtain ⟨r, hr0, hrs, f, hf, har⟩ := exists_smooth_near_of_general_disk_weakSol hk (rePart u) hr hz
  obtain ⟨s, hs0, hss, g, hg, hai⟩ := exists_smooth_near_of_general_disk_weakSol hk (imPart u) hi hz
  have hbr : Metric.ball z (min r s) ⊆ Metric.ball z r := Metric.ball_subset_ball (min_le_left _ _)
  have hbi : Metric.ball z (min r s) ⊆ Metric.ball z s := Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨min r s, lt_min hr0 hs0, hbr.trans hrs,
    fun x => (f x : ℂ) + Complex.I * (g x : ℂ),
    (Complex.ofRealCLM.contDiff.comp hf).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hg)), ?_⟩
  have har' := har.filter_mono (ae_mono (Measure.restrict_mono hbr le_rfl))
  have hai' := hai.filter_mono (ae_mono (Measure.restrict_mono hbi le_rfl))
  filter_upwards [har', hai'] with x hxr hxi
  simp only [value, hxr, hxi]

lemma general_disk_complex_weak_equation {k : ℕ} (hk : 2 ≤ k) (u : ComplexH1)
    (hr : PunctureRemoval.IsWeakSolOn (Surface.potV k) disk (rePart u))
    (hi : PunctureRemoval.IsWeakSolOn (Surface.potV k) disk (imPart u)) :
    InteriorWeakEquation disk (dxLp u) (dyLp u)
      (fun z => (Surface.potV k z : ℂ) * valueCLM u z) := by
  have er := interiorWeakEquation_of_isWeakSolOn (rePart u) (memLp_potV_general_real hk (rePart u)) hr
  have ei := interiorWeakEquation_of_isWeakSolOn (imPart u) (memLp_potV_general_real hk (imPart u)) hi
  have loc {f : ℂ → ℂ} (hf : MemLp f 2 (volume.restrict (disk : Set ℂ))) :
      LocallyIntegrableOn f disk volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable (by norm_num))
  have he := er.linear_combination ei
    (loc (Lp.memLp (TauCeti.W1p.gradient (rePart u))).re.ofReal)
    (loc (Lp.memLp (TauCeti.W1p.gradient (rePart u))).im.ofReal)
    (loc (memLp_potV_general_real hk (rePart u)).ofReal)
    (loc (Lp.memLp (TauCeti.W1p.gradient (imPart u))).re.ofReal)
    (loc (Lp.memLp (TauCeti.W1p.gradient (imPart u))).im.ofReal)
    (loc (memLp_potV_general_real hk (imPart u)).ofReal) Complex.I
  apply he.congr_ae (dxLp_ae u).symm (dyLp_ae u).symm
  filter_upwards [valueLp_ae u] with z hz
  change valueCLM u z = value u z at hz
  rw [hz]
  simp only [value, Complex.ofReal_mul]
  ring

lemma general_disk_smooth_representative_classical {k : ℕ} (hk : 2 ≤ k) (u : ComplexH1)
    (hr : PunctureRemoval.IsWeakSolOn (Surface.potV k) disk (rePart u))
    (hi : PunctureRemoval.IsWeakSolOn (Surface.potV k) disk (imPart u))
    {F : ℂ → ℂ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (disk : Set ℂ))
    (ha : valueCLM u =ᵐ[volume.restrict (disk : Set ℂ)] F) :
    ∀ z ∈ (disk : Set ℂ), Surface.laplacian F z + (Surface.potV k z : ℂ) * F z = 0 := by
  have he : InteriorWeakEquation disk
      (fun z => Dxy (dxLp u) (dyLp u) z 1)
      (fun z => Dxy (dxLp u) (dyLp u) z Complex.I)
      (fun z => (Surface.potV k z : ℂ) * valueCLM u z) := by
    simpa only [Dxy_one, Dxy_I] using general_disk_complex_weak_equation hk u hr hi
  have hh := smooth_representative_classical_equation (carrier_hasJet u) he hF ha
    (Complex.ofRealCLM.continuous.comp (Surface.contDiff_potV hk).continuous).continuousOn
  intro z hz
  exact add_eq_zero_iff_eq_neg.mpr (hh z hz)


/-- One representative on the entire open disk, with its classical equation. -/
theorem general_disk_weakSol_classical {k : ℕ} (hk : 2 ≤ k) (u : ComplexH1)
    (hr : PunctureRemoval.IsWeakSolOn (Surface.potV k) disk (rePart u))
    (hi : PunctureRemoval.IsWeakSolOn (Surface.potV k) disk (imPart u)) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) f (disk : Set ℂ) ∧
      valueCLM u =ᵐ[volume.restrict (disk : Set ℂ)] f ∧
      ∀ z ∈ (disk : Set ℂ), Surface.laplacian f z + (Surface.potV k z : ℂ) * f z = 0 := by
  obtain ⟨f, hf, ha⟩ := exists_contDiffOn_ae_of_smooth_near
    (fun z hz => exists_smooth_near_of_general_disk_complex_weakSol hk u hr hi hz)
  have hv := (valueLp_ae u).trans ha
  exact ⟨f, hf, hv, general_disk_smooth_representative_classical hk u hr hi hf hv⟩

end KsIndex.Weq
