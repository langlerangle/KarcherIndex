module

public import KsIndexLean.KarcherHeightLineMonotonicity
public import KsIndexLean.KarcherItem4Diameter

@[expose] public section


/-! Injectivity of the actual immersion on the logarithmic fundamental sector. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The strip angle equals the normalized height minus π/2 on the chosen half-period. -/
lemma heightStrip_actual_height (R : PaperHalfPeriodRealization k) {ζ : ℂ}
    (hζ : heightStrip ζ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = finiteParameter
      ⟨heightSectorParameter k ζ, heightStrip_parameter_not_puncture (by have := h.out; omega) hζ⟩)
    (hh : (centeredLiftAmbient R.C R.t q).2.2 ∈ Set.Icc 0 Real.pi) :
    (centeredLiftAmbient R.C R.t q).2.2 = Real.pi / 2 + ζ.im := by
  have hc := cos_lift_height_shift h.out (reflectionBasepoint k)
    ⟨heightSectorParameter k ζ, heightStrip_parameter_not_puncture (by have := h.out; omega) hζ⟩
    rfl R.C q hq
  rw [heightCayley_sectorParameter (by have := h.out; omega)
    (heightStrip_exp_add_one_ne hζ), Complex.exp_im, Complex.norm_exp] at hc
  have he : -(Real.exp ζ.re * Real.sin ζ.im) / Real.exp ζ.re = -Real.sin ζ.im := by
    field_simp
  rw [he] at hc
  apply Real.injOn_cos hh ⟨by linarith [hζ.2.1, Real.pi_pos], by linarith [hζ.2.2]⟩
  change Real.cos (HeightLift.height q + Real.pi) = _
  rw [hc, Real.cos_add]
  simp

/-- Intrinsic points over the logarithmic fundamental sector are separated by
 the actual ambient immersion. No ambient-image identification is assumed. -/
lemma heightStrip_ambient_injective (R : PaperHalfPeriodRealization k)
    {ζ ξ : ℂ} (hζ : heightStrip ζ) (hξ : heightStrip ξ)
    (q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = finiteParameter
      ⟨heightSectorParameter k ζ, heightStrip_parameter_not_puncture (by have := h.out; omega) hζ⟩)
    (hp : HeightLift.projection p = finiteParameter
      ⟨heightSectorParameter k ξ, heightStrip_parameter_not_puncture (by have := h.out; omega) hξ⟩)
    (hqz : (centeredLiftAmbient R.C R.t q).2.2 ∈ Set.Icc 0 Real.pi)
    (hpz : (centeredLiftAmbient R.C R.t p).2.2 ∈ Set.Icc 0 Real.pi)
    (he : centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p) : q = p := by
  have hheight := congrArg (fun v : AmbientTriple => v.2.2) he
  have hy := congrArg (fun v : AmbientTriple => v.2.1) he
  have hqY := (centeredLiftAmbient_horiz_descended R q _ hq).2
  have hpY := (centeredLiftAmbient_horiz_descended R p _ hp).2
  have hz := heightStrip_actual_height R hζ q hq hqz
  have hw := heightStrip_actual_height R hξ p hp hpz
  have hi : ζ.im = ξ.im := by linarith
  have hcoord : ζ = ξ := by
    apply heightStrip_Y_im_injective h.out (reflectionBasepoint k) hζ hξ
    apply Prod.ext
    · change horizontalY h.out (reflectionBasepoint k) (heightSectorParameter k ζ) =
        horizontalY h.out (reflectionBasepoint k) (heightSectorParameter k ξ)
      simp only [horizontalY, heightStrip_parameter_not_puncture
        (by have := h.out; omega : k ≠ 0) hζ,
        heightStrip_parameter_not_puncture (by have := h.out; omega : k ≠ 0) hξ]
      exact hqY.symm.trans (hy.trans hpY)
    · exact hi
  apply Subtype.ext
  apply Prod.ext
  · change HeightLift.projection q = HeightLift.projection p
    rw [hq, hp]
    subst ξ
    rfl
  · change HeightLift.height q = HeightLift.height p
    change HeightLift.height q + Real.pi = HeightLift.height p + Real.pi at hheight
    linarith

end PaperHalfPeriodRealization
end KsIndex.KarcherData
