module

public import KsIndexLean.KarcherInfinityCurvature

@[expose] public section


/-! Tensorial compatibility of the actual EW geometry under w = 1/v.
The coordinate derivative is retained in both covariant slots. -/
noncomputable section
open scoped ContDiff Topology
namespace KsIndex.KarcherData

lemma infinityRealDifferential_pullback {k : ℕ} (hk : 2 ≤ k)
    {v : ℂ} (hv : v ≠ 0) (d : ℂ) :
    infinityRealDifferential k v d = ewRealDifferential k v⁻¹ (d * (-(v⁻¹) ^ 2)) := by
  have h (c : ℂ) : (d * (-(v⁻¹) ^ 2)) * c = d * (c * (-(v⁻¹) ^ 2)) := by ring
  simp only [infinityRealDifferential, ewRealDifferential, ContinuousLinearMap.prod_apply,
    realCoeffLinear_apply, h, coeff1_inv_pullback hk hv, coeff2_inv_pullback hk hv,
    coeff3_inv_pullback hk hv]

/-- First fundamental forms transform by the actual inversion derivative. -/
theorem firstFundamentalForm_inversion {k : ℕ} (hk : 2 ≤ k)
    {X Y : ℂ → AmbientTriple} {v : ℂ} (hv : v ≠ 0)
    (hX : HasFDerivAt X (ewRealDifferential k v⁻¹) v⁻¹)
    (hY : HasFDerivAt Y (infinityRealDifferential k v) v) (a b : ℂ) :
    firstFundamentalForm Y v a b =
      firstFundamentalForm X v⁻¹ (a * (-(v⁻¹) ^ 2)) (b * (-(v⁻¹) ^ 2)) := by
  unfold firstFundamentalForm
  rw [hX.fderiv, hY.fderiv, infinityRealDifferential_pullback hk hv,
    infinityRealDifferential_pullback hk hv]

lemma ew_secondFundamentalForm_weingarten {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (ha : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (ewRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) (hX : ContDiffAt ℝ 2 X w) (a b : ℂ) :
    secondFundamentalForm X w a b =
      -euclideanDot (fderiv ℝ (chartUnitNormal X) w a) (fderiv ℝ X w b) := by
  apply secondFundamentalForm_eq_neg_normal_derivative hX
    (ew_chartUnitNormal_differentiableAt hk hU ha hd hw) rfl a b
  filter_upwards [hU.mem_nhds hw] with z hz
  rw [coordinateTangent_eq (hd z hz).differentiableAt]
  obtain ⟨_, h1, hi⟩ := ew_chartUnitNormal_spec hk (ha z hz) (hd z hz)
  exact normal_orthogonal_all h1 hi b

lemma infinity_secondFundamentalForm_weingarten {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (ha : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (infinityRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) (hX : ContDiffAt ℝ 2 X w) (a b : ℂ) :
    secondFundamentalForm X w a b =
      -euclideanDot (fderiv ℝ (chartUnitNormal X) w a) (fderiv ℝ X w b) := by
  apply secondFundamentalForm_eq_neg_normal_derivative hX
    (infinity_chartUnitNormal_differentiableAt hk hU ha hd hw) rfl a b
  filter_upwards [hU.mem_nhds hw] with z hz
  rw [coordinateTangent_eq (hd z hz).differentiableAt]
  obtain ⟨_, h1, hi⟩ := infinity_chartUnitNormal_spec hk (ha z hz) (hd z hz)
  exact normal_orthogonal_all h1 hi b

lemma chartUnitNormal_inversion_eventuallyEq {k : ℕ} (hk : 2 ≤ k)
    {X Y : ℂ → AmbientTriple} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (ha : ∀ z ∈ U, z ∉ Surface.punctures k) (hb : ∀ z ∈ V, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (ewRealDifferential k z) z)
    (he : ∀ z ∈ V, HasFDerivAt Y (infinityRealDifferential k z) z)
    {v : ℂ} (hv : v ≠ 0) (hvU : v⁻¹ ∈ U) (hvV : v ∈ V) :
    chartUnitNormal Y =ᶠ[𝓝 v] (fun z => chartUnitNormal X z⁻¹) := by
  have hpre : ∀ᶠ z in 𝓝 v, z⁻¹ ∈ U :=
    (hasDerivAt_chartInversion hv).continuousAt.tendsto.eventually (hU.mem_nhds hvU)
  have hne : ∀ᶠ z in 𝓝 v, z ≠ 0 := eventually_ne_nhds hv
  filter_upwards [hV.mem_nhds hvV, hpre, hne] with z hz hzu hz0
  rw [infinity_chartUnitNormal_overlap hk (hb z hz) hz0 (he z hz),
    ew_chartUnitNormal_eq_stereoNormal hk (ha z⁻¹ hzu) (hd z⁻¹ hzu)]

/-- The differential of the normal transforms by the coordinate derivative. -/
theorem chartUnitNormal_fderiv_inversion {k : ℕ} (hk : 2 ≤ k)
    {X Y : ℂ → AmbientTriple} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (ha : ∀ z ∈ U, z ∉ Surface.punctures k) (hb : ∀ z ∈ V, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (ewRealDifferential k z) z)
    (he : ∀ z ∈ V, HasFDerivAt Y (infinityRealDifferential k z) z)
    {v : ℂ} (hv : v ≠ 0) (hvU : v⁻¹ ∈ U) (hvV : v ∈ V) (a : ℂ) :
    fderiv ℝ (chartUnitNormal Y) v a =
      fderiv ℝ (chartUnitNormal X) v⁻¹ (a * (-(v⁻¹) ^ 2)) := by
  rw [(chartUnitNormal_inversion_eventuallyEq hk hU hV ha hb hd he hv hvU hvV).fderiv_eq]
  have hn := (ew_chartUnitNormal_differentiableAt hk hU ha hd hvU).hasFDerivAt
  have hi := (hasDerivAt_chartInversion hv).hasFDerivAt.restrictScalars ℝ
  have hc := (hn.comp v hi).fderiv
  change fderiv ℝ (chartUnitNormal X ∘ (fun z : ℂ => z⁻¹)) v a = _
  rw [hc, ContinuousLinearMap.comp_apply]
  rfl

/-- The full Hessian-defined second fundamental form transforms in both slots;
this is stronger than agreement of its scalar norm. -/
theorem secondFundamentalForm_inversion {k : ℕ} (hk : 2 ≤ k)
    {X Y : ℂ → AmbientTriple} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (ha : ∀ z ∈ U, z ∉ Surface.punctures k) (hb : ∀ z ∈ V, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (ewRealDifferential k z) z)
    (he : ∀ z ∈ V, HasFDerivAt Y (infinityRealDifferential k z) z)
    {v : ℂ} (hv : v ≠ 0) (hvU : v⁻¹ ∈ U) (hvV : v ∈ V)
    (hX : ContDiffAt ℝ 2 X v⁻¹) (hY : ContDiffAt ℝ 2 Y v) (a b : ℂ) :
    secondFundamentalForm Y v a b =
      secondFundamentalForm X v⁻¹ (a * (-(v⁻¹) ^ 2)) (b * (-(v⁻¹) ^ 2)) := by
  rw [infinity_secondFundamentalForm_weingarten hk hV hb he hvV hY,
    ew_secondFundamentalForm_weingarten hk hU ha hd hvU hX,
    chartUnitNormal_fderiv_inversion hk hU hV ha hb hd he hv hvU hvV,
    (he v hvV).fderiv, (hd v⁻¹ hvU).fderiv, infinityRealDifferential_pullback hk hv]

/-- Choice of local primitive does not change II in the ew coordinate. -/
theorem ew_secondFundamentalForm_independent {k : ℕ} (hk : 2 ≤ k)
    {X Y : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (ha : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (ewRealDifferential k z) z)
    (he : ∀ z ∈ U, HasFDerivAt Y (ewRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) (hX : ContDiffAt ℝ 2 X w) (hY : ContDiffAt ℝ 2 Y w)
    (a b : ℂ) : secondFundamentalForm X w a b = secondFundamentalForm Y w a b := by
  have hn : chartUnitNormal X =ᶠ[𝓝 w] chartUnitNormal Y := by
    filter_upwards [hU.mem_nhds hw] with z hz
    rw [ew_chartUnitNormal_eq_stereoNormal hk (ha z hz) (hd z hz),
      ew_chartUnitNormal_eq_stereoNormal hk (ha z hz) (he z hz)]
  rw [ew_secondFundamentalForm_weingarten hk hU ha hd hw hX,
    ew_secondFundamentalForm_weingarten hk hU ha he hw hY,
    hn.fderiv_eq, (hd w hw).fderiv, (he w hw).fderiv]

/-- Choice of local primitive does not change II in the infinity coordinate. -/
theorem infinity_secondFundamentalForm_independent {k : ℕ} (hk : 2 ≤ k)
    {X Y : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (ha : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (infinityRealDifferential k z) z)
    (he : ∀ z ∈ U, HasFDerivAt Y (infinityRealDifferential k z) z)
    {w : ℂ} (hw : w ∈ U) (hX : ContDiffAt ℝ 2 X w) (hY : ContDiffAt ℝ 2 Y w)
    (a b : ℂ) : secondFundamentalForm X w a b = secondFundamentalForm Y w a b := by
  have hn : chartUnitNormal X =ᶠ[𝓝 w] chartUnitNormal Y := by
    filter_upwards [hU.mem_nhds hw] with z hz
    rw [infinity_chartUnitNormal_eq hk (ha z hz) (hd z hz),
      infinity_chartUnitNormal_eq hk (ha z hz) (he z hz)]
  rw [infinity_secondFundamentalForm_weingarten hk hU ha hd hw hX,
    infinity_secondFundamentalForm_weingarten hk hU ha he hw hY,
    hn.fderiv_eq, (hd w hw).fderiv, (he w hw).fderiv]

end KsIndex.KarcherData
