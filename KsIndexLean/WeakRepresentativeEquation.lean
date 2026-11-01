module

public import KsIndexLean.WeakClassicalEquation

@[expose] public section


/-! Weak equations are invariant under almost-everywhere representative changes
on their open domain. Smooth representatives satisfy the classical coordinate PDE. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Distributions
namespace KsIndex.Weq

lemma InteriorWeakEquation.congr_ae {Ω : Opens ℂ} {ux uy q vx vy r : ℂ → ℂ}
    (h : InteriorWeakEquation Ω ux uy q)
    (hx : ux =ᵐ[volume.restrict (Ω : Set ℂ)] vx)
    (hy : uy =ᵐ[volume.restrict (Ω : Set ℂ)] vy)
    (hq : q =ᵐ[volume.restrict (Ω : Set ℂ)] r) :
    InteriorWeakEquation Ω vx vy r := by
  intro ψ
  have hx' := (ae_restrict_iff' Ω.isOpen.measurableSet).mp hx
  have hy' := (ae_restrict_iff' Ω.isOpen.measurableSet).mp hy
  have hq' := (ae_restrict_iff' Ω.isOpen.measurableSet).mp hq
  have hl : (∫ z, fderiv ℝ (ψ : ℂ → ℂ) z 1 * vx z +
      fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * vy z) =
      ∫ z, fderiv ℝ (ψ : ℂ → ℂ) z 1 * ux z +
        fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * uy z := by
    apply integral_congr_ae
    filter_upwards [hx', hy'] with z hxz hyz
    by_cases hz : z ∈ (Ω : Set ℂ)
    · rw [hxz hz, hyz hz]
    · have hd (d : ℂ) : fderiv ℝ (ψ : ℂ → ℂ) z d = 0 :=
        image_eq_zero_of_notMem_tsupport (f := (derivTest ψ d : ℂ → ℂ))
          (fun ht => hz ((derivTest ψ d).tsupport_subset ht))
      simp only [hd, zero_mul, add_zero]
  have hr : (∫ z, ψ z * r z) = ∫ z, ψ z * q z := by
    apply integral_congr_ae
    filter_upwards [hq'] with z hqz
    by_cases hz : z ∈ (Ω : Set ℂ)
    · rw [hqz hz]
    · have hh : ψ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hz (ψ.tsupport_subset ht))
      simp only [hh, zero_mul]
  rw [hl, hr]
  exact h ψ

/-- Any smooth representative of a genuine weak first jet satisfies the
pointwise coordinate Jacobi equation; all derivative identifications are proved. -/
theorem smooth_representative_classical_equation {Ω : Opens ℂ}
    {u F V : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume Ω u J)
    (he : InteriorWeakEquation Ω (fun z => J z 1) (fun z => J z Complex.I)
      (fun z => V z * u z))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Ω : Set ℂ))
    (ha : u =ᵐ[volume.restrict (Ω : Set ℂ)] F)
    (hV : ContinuousOn V (Ω : Set ℂ)) :
    ∀ z ∈ (Ω : Set ℂ),
      fderiv ℝ (fun w => fderiv ℝ F w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ F w Complex.I) z Complex.I = -(V z * F z) := by
  have hJ := (hw.congr_ae ha).ae_eq (smooth_hasWeakFDerivOn hF)
  have hx : (fun z => J z 1) =ᵐ[volume.restrict (Ω : Set ℂ)]
      (fun z => fderiv ℝ F z 1) := by
    filter_upwards [hJ] with z hz
    rw [hz]
  have hy : (fun z => J z Complex.I) =ᵐ[volume.restrict (Ω : Set ℂ)]
      (fun z => fderiv ℝ F z Complex.I) := by
    filter_upwards [hJ] with z hz
    rw [hz]
  have hq : (fun z => V z * u z) =ᵐ[volume.restrict (Ω : Set ℂ)]
      (fun z => V z * F z) := by
    filter_upwards [ha] with z hz
    rw [hz]
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ F) (Ω : Set ℂ) :=
    hF.fderiv_of_isOpen Ω.isOpen (by simp)
  exact classical_divergence_of_interiorWeakEquation
    (hd.clm_apply contDiffOn_const) (hd.clm_apply contDiffOn_const)
    (hV.mul hF.continuousOn) (he.congr_ae hx hy hq)

end KsIndex.Weq
