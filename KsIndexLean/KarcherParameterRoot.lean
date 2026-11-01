module

public import KsIndexLean.KarcherPeriodQuotientCharts
public import KsIndexLean.KarcherEndRoot
public import KsIndexLean.KarcherGlobalNormal

@[expose] public section


/-! The rational height coordinate and its root on the actual parameter sphere
and period quotient. Finite-chart statements retain the integration basepoint. -/
noncomputable section
namespace KsIndex.KarcherData

/-- The Cayley coordinate on the punctured parameter sphere, with value -1 at
infinity. -/
def parameterCayley {k : ℕ} (p : ParameterSphere k) : ℂ :=
  if h : p.val.val 2 = 1 then -1
  else heightCayley k (finiteParameterCoordinate p h).val

@[simp] theorem parameterCayley_finite {k : ℕ} (w : PuncturedPlane k) :
    parameterCayley (finiteParameter w) = heightCayley k w.val := by
  have hn : (finiteParameter w).val.val 2 ≠ 1 := Spherical.stereoPoint_third_ne_one w.val
  rw [parameterCayley, dite_eq_right hn, finiteParameterCoordinate_finite]

@[simp] theorem parameterCayley_infinity (k : ℕ) :
    parameterCayley (infinityParameter k) = -1 :=
  dite_eq_left infinitySphereChart_zero_height

lemma parameterCayley_ne_zero {k : ℕ} (p : ParameterSphere k) : parameterCayley p ≠ 0 := by
  rcases parameterSphere_cases p with rfl | ⟨w, rfl⟩
  · simp
  · simpa using heightCayley_ne_zero w.property

lemma continuousAt_parameterCayley_finite {k : ℕ} (w : PuncturedPlane k) :
    ContinuousAt parameterCayley (finiteParameter w) := by
  apply (isOpenEmbedding_finiteParameter k).continuousAt_iff.mp
  have he : parameterCayley ∘ finiteParameter (k := k) =
      fun z : PuncturedPlane k => heightCayley k z.val := funext parameterCayley_finite
  rw [he]
  have hc : Continuous (fun z : PuncturedPlane k => heightCayley k z.val) := by
    unfold heightCayley
    exact (continuous_const.add (continuous_const.mul (continuous_subtype_val.pow k))).div
      (continuous_const.sub (continuous_const.mul (continuous_subtype_val.pow k)))
      (fun z => (height_factors_ne z.property).2)
  exact hc.continuousAt

/-- The normalized root on the actual intrinsic period quotient. -/
def parameterRoot {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b : PuncturedPlane k) (C : PeriodTarget) :
    HeightLift.PeriodQuotient (extendedEWMap hk b C) m → ℂ :=
  HeightLift.quotientHeightRoot hm (fun p => parameterCayley p / heightCayley k b.val)

/-- The concrete root's power recovers the rational coordinate on each finite
fiber of the actual quotient. -/
theorem parameterRoot_pow_finite {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b z : PuncturedPlane k) (C : PeriodTarget)
    (x : HeightLift.PeriodQuotient (extendedEWMap hk b C) m)
    (hx : HeightLift.quotientProjection m x = finiteParameter z) :
    parameterRoot hk hm b C x ^ m = heightCayley k z.val / heightCayley k b.val := by
  induction x using Quotient.inductionOn with
  | h q =>
    change HeightLift.projection q = finiteParameter z at hx
    change heightRoot m (parameterCayley (HeightLift.projection q) / heightCayley k b.val)
      (HeightLift.height q) ^ m = _
    rw [hx, parameterCayley_finite]
    exact lift_heightRoot_pow hk hm b z C q hx

lemma parameterRoot_ne_zero {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b : PuncturedPlane k) (C : PeriodTarget)
    (x : HeightLift.PeriodQuotient (extendedEWMap hk b C) m) :
    parameterRoot hk hm b C x ≠ 0 := by
  induction x using Quotient.inductionOn with
  | h q => exact heightRoot_ne_zero _ _ _

/-- Continuity on the finite parameter chart, using the nonvanishing normalized
Cayley coordinate and the continuous lifted height. -/
theorem continuousAt_parameterRoot_finite {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b z : PuncturedPlane k) (C : PeriodTarget)
    (x : HeightLift.PeriodQuotient (extendedEWMap hk b C) m)
    (hx : HeightLift.quotientProjection m x = finiteParameter z) :
    ContinuousAt (parameterRoot hk hm b C) x := by
  induction x using Quotient.inductionOn with
  | h q =>
    change HeightLift.projection q = finiteParameter z at hx
    have ho : IsOpenQuotientMap (HeightLift.periodQuotientMap
        (F := extendedEWMap hk b C) m) :=
      ⟨(HeightLift.periodQuotientMap_isQuotientMap m).surjective,
        (HeightLift.periodQuotientMap_isQuotientMap m).continuous,
        HeightLift.periodQuotientMap_isOpenMap m⟩
    apply ho.continuousAt_comp_iff.mp
    change ContinuousAt (fun q => heightRoot m
      (parameterCayley (HeightLift.projection q) / heightCayley k b.val)
      (HeightLift.height q)) q
    have hz : ContinuousAt (fun q => parameterCayley (HeightLift.projection q) /
        heightCayley k b.val) q :=
      ((hx ▸ continuousAt_parameterCayley_finite z).comp
        HeightLift.continuous_projection.continuousAt).div_const _
    have hn : parameterCayley (HeightLift.projection q) / heightCayley k b.val ≠ 0 :=
      div_ne_zero (parameterCayley_ne_zero _) (heightCayley_ne_zero b.property)
    unfold heightRoot
    apply ContinuousAt.cexp
    exact ((Complex.continuous_ofReal.continuousAt.comp
      (hz.norm.log (norm_ne_zero_iff.mpr hn))).div_const _).add
      ((continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp
        HeightLift.continuous_height.continuousAt)).div_const _)

/-- The end-specific root, now directly on the actual quotient. -/
def quotientEndRoot {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b : PuncturedPlane k) (w : ℂ) (C : PeriodTarget)
    (x : HeightLift.PeriodQuotient (extendedEWMap hk b C) m) : ℂ :=
  if w ^ k = Complex.I then parameterRoot hk hm b C x
  else (parameterRoot hk hm b C x)⁻¹

theorem quotientEndRoot_pow_finite {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b z : PuncturedPlane k) (w : ℂ) (C : PeriodTarget)
    (x : HeightLift.PeriodQuotient (extendedEWMap hk b C) m)
    (hx : HeightLift.quotientProjection m x = finiteParameter z) :
    quotientEndRoot hk hm b w C x ^ m =
      endCoordinate k w z.val / endCoordinate k w b.val := by
  rw [endCoordinate_eq_heightCayley, endCoordinate_eq_heightCayley]
  unfold quotientEndRoot
  split_ifs
  · exact parameterRoot_pow_finite hk hm b z C x hx
  · rw [inv_pow, parameterRoot_pow_finite hk hm b z C x hx]
    simp only [inv_div]
    field_simp

theorem continuousAt_quotientEndRoot_finite {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b z : PuncturedPlane k) (w : ℂ) (C : PeriodTarget)
    (x : HeightLift.PeriodQuotient (extendedEWMap hk b C) m)
    (hx : HeightLift.quotientProjection m x = finiteParameter z) :
    ContinuousAt (quotientEndRoot hk hm b w C) x := by
  unfold quotientEndRoot
  split_ifs
  · exact continuousAt_parameterRoot_finite hk hm b z C x hx
  · exact (continuousAt_parameterRoot_finite hk hm b z C x hx).inv₀
      (parameterRoot_ne_zero hk hm b C x)

/-- Every root of the normalized finite Cayley value is realized in the
corresponding actual quotient fiber. -/
theorem exists_parameterRoot_finite {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b z : PuncturedPlane k) (C : PeriodTarget) {t : ℂ}
    (ht : t ^ m = heightCayley k z.val / heightCayley k b.val) :
    ∃ x : HeightLift.PeriodQuotient (extendedEWMap hk b C) m,
      HeightLift.quotientProjection m x = finiteParameter z ∧ parameterRoot hk hm b C x = t := by
  apply HeightLift.exists_quotientHeightRoot hm
    (fun p => parameterCayley p / heightCayley k b.val) (finiteParameter z)
  · rw [parameterCayley_finite]
    exact div_ne_zero (heightCayley_ne_zero z.property) (heightCayley_ne_zero b.property)
  · intro q hq
    simpa only [parameterCayley_finite] using exp_lift_height hk b z C q hq
  · simpa only [parameterCayley_finite] using ht

/-- The signed end root realizes every algebraic root of the normalized
end coordinate, in the actual fiber over the given finite point. -/
theorem exists_quotientEndRoot_finite {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b z : PuncturedPlane k) (w : ℂ) (C : PeriodTarget) {t : ℂ}
    (ht : t ^ m = endCoordinate k w z.val / endCoordinate k w b.val) :
    ∃ x : HeightLift.PeriodQuotient (extendedEWMap hk b C) m,
      HeightLift.quotientProjection m x = finiteParameter z ∧ quotientEndRoot hk hm b w C x = t := by
  rw [endCoordinate_eq_heightCayley, endCoordinate_eq_heightCayley] at ht
  by_cases hw : w ^ k = Complex.I
  · simp only [hw, ite_true] at ht
    obtain ⟨x, hx, hr⟩ := exists_parameterRoot_finite hk hm b z C ht
    exact ⟨x, hx, by simpa only [quotientEndRoot, hw, ite_true] using hr⟩
  · simp only [hw, ite_false] at ht
    have hi : (t⁻¹) ^ m = heightCayley k z.val / heightCayley k b.val := by
      rw [inv_pow, ht]
      simp [div_eq_mul_inv, mul_comm]
    obtain ⟨x, hx, hr⟩ := exists_parameterRoot_finite hk hm b z C hi
    exact ⟨x, hx, by simp only [quotientEndRoot, hw, ite_false, hr, inv_inv]⟩

/-- The exact algebraic image of a finite quotient fiber under the end root. -/
theorem quotientEndRoot_fiber_image {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b z : PuncturedPlane k) (w : ℂ) (C : PeriodTarget) :
    quotientEndRoot hk hm b w C ''
      {x | HeightLift.quotientProjection m x = finiteParameter z} =
      {t | t ^ m = endCoordinate k w z.val / endCoordinate k w b.val} := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact quotientEndRoot_pow_finite hk hm b z w C x hx
  · intro ht
    obtain ⟨x, hx, hr⟩ := exists_quotientEndRoot_finite hk hm b z w C ht
    exact ⟨x, hx, hr⟩

lemma quotientEndRoot_fiber_injective {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b : PuncturedPlane k) (w : ℂ) (C : PeriodTarget)
    (x y : HeightLift.PeriodQuotient (extendedEWMap hk b C) m)
    (hp : HeightLift.quotientProjection m x = HeightLift.quotientProjection m y)
    (hr : quotientEndRoot hk hm b w C x = quotientEndRoot hk hm b w C y) : x = y := by
  apply HeightLift.quotientHeightRoot_fiber_injective hm
    (fun p => parameterCayley p / heightCayley k b.val) x y hp
  change parameterRoot hk hm b C x = parameterRoot hk hm b C y
  unfold quotientEndRoot at hr
  split_ifs at hr
  · exact hr
  · exact inv_injective hr

/-- On the full preimage of an injective finite base-coordinate region, the
signed root is injective across all quotient sheets. -/
theorem quotientEndRoot_injOn {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b : PuncturedPlane k) (w : ℂ) (C : PeriodTarget) (U : Set (PuncturedPlane k))
    (hi : Set.InjOn (fun z : PuncturedPlane k =>
      endCoordinate k w z.val / endCoordinate k w b.val) U) :
    Set.InjOn (quotientEndRoot hk hm b w C)
      {x | ∃ z ∈ U, HeightLift.quotientProjection m x = finiteParameter z} := by
  rintro x ⟨z, hz, hx⟩ y ⟨v, hv, hy⟩ he
  have hec : endCoordinate k w z.val / endCoordinate k w b.val =
      endCoordinate k w v.val / endCoordinate k w b.val := by
    rw [← quotientEndRoot_pow_finite hk hm b z w C x hx,
      ← quotientEndRoot_pow_finite hk hm b v w C y hy, he]
  have hzv := hi hz hv hec
  apply quotientEndRoot_fiber_injective hk hm b w C x y _ he
  rw [hx, hy, hzv]

/-- The concrete signed root is a bijection between the full quotient
preimage of an injective base region and the corresponding algebraic root
region. Topological compatibility is addressed separately. -/
theorem quotientEndRoot_bijOn {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b : PuncturedPlane k) (w : ℂ) (C : PeriodTarget) (U : Set (PuncturedPlane k))
    (hi : Set.InjOn (fun z : PuncturedPlane k =>
      endCoordinate k w z.val / endCoordinate k w b.val) U) :
    Set.BijOn (quotientEndRoot hk hm b w C)
      {x | ∃ z ∈ U, HeightLift.quotientProjection m x = finiteParameter z}
      {t | ∃ z ∈ U, t ^ m = endCoordinate k w z.val / endCoordinate k w b.val} := by
  refine ⟨?_, quotientEndRoot_injOn hk hm b w C U hi, ?_⟩
  · rintro x ⟨z, hz, hx⟩
    exact ⟨z, hz, quotientEndRoot_pow_finite hk hm b z w C x hx⟩
  · rintro t ⟨z, hz, ht⟩
    obtain ⟨x, hx, hr⟩ := exists_quotientEndRoot_finite hk hm b z w C ht
    exact ⟨x, ⟨z, hz, hx⟩, hr⟩

end KsIndex.KarcherData
