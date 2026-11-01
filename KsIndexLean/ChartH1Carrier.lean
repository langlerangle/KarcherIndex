module

public import KsIndexLean.SphericalPullbackH1

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- A genuine weak H1 function on the disk determines a unique adopted carrier. -/
theorem chartH1_disk_exists_unique {f : ℂ → ℂ} (hf : ChartH1 disk f) :
    ∃! u : ComplexH1, (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f := by
  rcases hf with ⟨hL, J, hJ, hJL⟩
  have hx := hJL.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ 1)
  have hy := hJL.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ Complex.I)
  let F := hL.toLp f
  let X := hx.toLp (fun z => J z 1)
  let Y := hy.toLp (fun z => J z Complex.I)
  have hF : (F : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f := MemLp.coeFn_toLp hL
  have hX : (X : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => J z 1) :=
    MemLp.coeFn_toLp hx
  have hY : (Y : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => J z Complex.I) :=
    MemLp.coeFn_toLp hy
  have he : J =ᵐ[volume.restrict (disk : Set ℂ)] Dxy X Y := by
    filter_upwards [hX, hY] with z hxz hyz
    ext w
    rw [Dxy_apply, hxz, hyz, realLinear_coordinates (J z) w]
  have hw : HasComplexH1Jet F X Y := (hJ.congr_ae hF.symm).congr_ae_deriv he
  refine ⟨reconstruct F X Y hw, ?_, ?_⟩
  · change (valueCLM (reconstruct F X Y hw) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f
    rw [reconstruct_value]
    exact hF
  · intro v hv
    apply valueCLM_injective
    rw [reconstruct_value]
    exact Lp.ext (hv.trans hF.symm)

lemma chartH1_mono {Ω Ω' : TopologicalSpace.Opens ℂ} {f : ℂ → ℂ}
    (hf : ChartH1 Ω f) (h : Ω' ≤ Ω) : ChartH1 Ω' f := by
  rcases hf with ⟨hL, J, hJ, hJL⟩
  have hm := Measure.restrict_mono h (le_rfl : volume ≤ volume)
  exact ⟨hL.mono_measure hm, J, hJ.mono h, hJL.mono_measure hm⟩

/-- Restricting the two actual chart pullbacks recovers unique disk carriers. -/
theorem sphere_chart_disk_carriers {A : Set Circle₁} (hA : IsOpen A) (F : Sphere → ℂ)
    (hn : ChartH1 (extendedSeamDomain A hA) (fun z => F (sphereChart z)))
    (hs : ChartH1 (extendedSeamDomain A hA) (fun z => F (southChart z))) :
    (∃! u : ComplexH1, (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => F (sphereChart z))) ∧
    (∃! v : ComplexH1, (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => F (southChart z))) :=
  ⟨chartH1_disk_exists_unique (chartH1_mono hn (disk_le_extendedSeamDomain hA)),
   chartH1_disk_exists_unique (chartH1_mono hs (disk_le_extendedSeamDomain hA))⟩

end KsIndex.Spherical
