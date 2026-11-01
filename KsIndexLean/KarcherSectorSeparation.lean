module

public import KsIndexLean.KarcherSectorEmbedding

@[expose] public section


/-! Separation of the fundamental sector and its reflected copy. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex Set
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma heightStripPoint_conjugation_fixed (R : PaperHalfPeriodRealization k)
    (ζ : HeightStrip) (hs : ζ.val.re = 0) :
    R.conjugationLift (R.heightStripPoint ζ).val = (R.heightStripPoint ζ).val := by
  apply Subtype.ext
  apply Prod.ext
  · change parameterConjugation (HeightLift.projection (R.heightStripPoint ζ).val) = _
    rw [R.heightStripPoint_projection]
    erw [parameterConjugation_finite]
    change finiteParameter _ = HeightLift.projection (R.heightStripPoint ζ).val
    rw [R.heightStripPoint_projection]
    congr 1
    apply Subtype.ext
    apply Complex.ext
    · simp
    · simp [heightStrip_parameter_im_zero ζ.property hs]
  · rfl

lemma heightStripImmersion_y_zero (R : PaperHalfPeriodRealization k)
    (ζ : HeightStrip) (hs : ζ.val.re = 0) : (R.heightStripImmersion ζ).2.1 = 0 := by
  have he := congrArg (fun v : AmbientTriple => v.2.1)
    (R.conjugationLift_ambient (R.heightStripPoint ζ).val)
  rw [R.heightStripPoint_conjugation_fixed ζ hs] at he
  change (R.heightStripImmersion ζ).2.1 = -(R.heightStripImmersion ζ).2.1 at he
  linarith

lemma heightStripImmersion_y_neg (R : PaperHalfPeriodRealization k)
    (ζ : HeightStrip) (hs : ζ.val.re < 0) : (R.heightStripImmersion ζ).2.1 < 0 := by
  let ξ : HeightStrip := ⟨(0 : ℂ) + (ζ.val.im : ℂ) * I,
    heightLine_mem_strip ζ.property.2.1 ζ.property.2.2 (le_refl 0)⟩
  have hy0 := R.heightStripImmersion_y_zero ξ (by simp [ξ])
  have hζy := congrArg Prod.fst (R.heightStripImmersion_yz ζ)
  have hξy := congrArg Prod.fst (R.heightStripImmersion_yz ξ)
  have hm := heightLineY_strictMonoOn h.out (reflectionBasepoint k)
    ζ.property.2.1 ζ.property.2.2 ζ.property.1 (by simp : (0 : ℝ) ∈ Iic 0) hs
  have hz : (ζ.val.re : ℂ) + (ζ.val.im : ℂ) * I = ζ.val := Complex.re_add_im ζ.val
  dsimp [heightLineY, heightLineParameter] at hm
  rw [hz] at hm
  change (R.heightStripImmersion ζ).2.1 =
    horizontalY h.out (reflectionBasepoint k) (heightSectorParameter k ζ.val) at hζy
  change (R.heightStripImmersion ξ).2.1 =
    horizontalY h.out (reflectionBasepoint k)
      (heightSectorParameter k ((0 : ℂ) + (ζ.val.im : ℂ) * I)) at hξy
  linarith

lemma heightStripImmersion_y_nonpos (R : PaperHalfPeriodRealization k) (ζ : HeightStrip) :
    (R.heightStripImmersion ζ).2.1 ≤ 0 := by
  rcases ζ.property.1.eq_or_lt with hs | hs
  · exact (R.heightStripImmersion_y_zero ζ hs).le
  · exact (R.heightStripImmersion_y_neg ζ hs).le

/-- A sector and its reflection can meet only along their shared boundary,
where the intrinsic reflection already fixes the point. -/
lemma heightStrip_reflected_collision (R : PaperHalfPeriodRealization k)
    (ζ ξ : HeightStrip)
    (he : R.heightStripImmersion ζ =
      centeredLiftAmbient R.C R.t (R.conjugationLift (R.heightStripPoint ξ).val)) :
    (R.heightStripPoint ζ).val = R.conjugationLift (R.heightStripPoint ξ).val := by
  rw [R.conjugationLift_ambient] at he
  have hy := congrArg (fun v : AmbientTriple => v.2.1) he
  change (R.heightStripImmersion ζ).2.1 = -(R.heightStripImmersion ξ).2.1 at hy
  have hζ := R.heightStripImmersion_y_nonpos ζ
  have hξ := R.heightStripImmersion_y_nonpos ξ
  have hs : ξ.val.re = 0 := by
    by_contra hn
    have hh := R.heightStripImmersion_y_neg ξ (lt_of_le_of_ne ξ.property.1 hn)
    linarith
  have hf := R.heightStripPoint_conjugation_fixed ξ hs
  have hxe : R.heightStripImmersion ξ =
      ((R.heightStripImmersion ξ).1, -(R.heightStripImmersion ξ).2.1,
        (R.heightStripImmersion ξ).2.2) := by
    have hh := R.conjugationLift_ambient (R.heightStripPoint ξ).val
    rw [hf] at hh
    exact hh
  have hsame : ζ = ξ := R.isClosedEmbedding_heightStripImmersion.injective (he.trans hxe.symm)
  subst ξ
  exact hf.symm

end PaperHalfPeriodRealization
end KsIndex.KarcherData
