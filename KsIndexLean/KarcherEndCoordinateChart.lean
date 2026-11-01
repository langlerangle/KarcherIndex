module

public import KsIndexLean.KarcherEndCoordinate
public import Mathlib.Topology.IsLocalHomeomorph

@[expose] public section


/-! The inverse-function chart at an EW puncture, including its actual source
and exclusion of all other punctures. -/
noncomputable section
namespace KsIndex.KarcherData

/-- A local homeomorphism whose forward map is exactly the end coordinate. -/
def endCoordinateChart {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) : OpenPartialHomeomorph ℂ ℂ :=
  ((hasStrictDerivAt_endCoordinate hw).hasStrictFDerivAt_equiv
    (endCoordinate_deriv_ne_zero hk hw)).toOpenPartialHomeomorph (endCoordinate k w)

@[simp] theorem endCoordinateChart_apply {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) (z : ℂ) :
    endCoordinateChart hk hw z = endCoordinate k w z := rfl

lemma endCoordinateChart_mem_source {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) : w ∈ (endCoordinateChart hk hw).source :=
  ((hasStrictDerivAt_endCoordinate hw).hasStrictFDerivAt_equiv
    (endCoordinate_deriv_ne_zero hk hw)).mem_toOpenPartialHomeomorph_source

lemma endCoordinateChart_zero_mem_target {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) : (0 : ℂ) ∈ (endCoordinateChart hk hw).target := by
  simpa only [endCoordinateChart_apply, endCoordinate_self hw] using
    (endCoordinateChart hk hw).map_source (endCoordinateChart_mem_source hk hw)

/-- Totalized rational division sends every puncture to zero. Only the chosen
puncture lies in the inverse-function chart source. -/
lemma endCoordinate_at_puncture {k : ℕ} (w : ℂ) {v : ℂ}
    (hv : v ∈ Surface.punctures k) : endCoordinate k w v = 0 := by
  have hc : heightCayley k v = 0 := by
    rcases puncture_power_sign hv with hp | hp <;>
      simp [heightCayley, hp, Complex.I_mul_I]
  rw [endCoordinate_eq_heightCayley]
  simp [hc]

lemma endCoordinateChart_puncture_iff {k : ℕ} (hk : 2 ≤ k) {w v : ℂ}
    (hw : w ∈ Surface.punctures k) (hv : v ∈ (endCoordinateChart hk hw).source) :
    v ∈ Surface.punctures k ↔ v = w := by
  constructor
  · intro hp
    apply (endCoordinateChart hk hw).injOn hv (endCoordinateChart_mem_source hk hw)
    simp only [endCoordinateChart_apply, endCoordinate_at_puncture w hp,
      endCoordinate_self hw]
  · rintro rfl
    exact hw

/-- The punctured source has exactly the punctured target as its image. -/
theorem endCoordinateChart_punctured_image {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) :
    endCoordinateChart hk hw ''
      {z | z ∈ (endCoordinateChart hk hw).source ∧ z ∉ Surface.punctures k} =
      {t | t ∈ (endCoordinateChart hk hw).target ∧ t ≠ 0} := by
  let e := endCoordinateChart hk hw
  ext t
  constructor
  · rintro ⟨z, ⟨hz, hp⟩, rfl⟩
    refine ⟨e.map_source hz, ?_⟩
    intro he
    have hzw : z = w := e.injOn hz (endCoordinateChart_mem_source hk hw)
      (by change endCoordinate k w z = endCoordinate k w w
          rw [endCoordinate_self hw]
          exact he)
    exact hp (hzw ▸ hw)
  · rintro ⟨ht, hn⟩
    refine ⟨e.symm t, ⟨e.map_target ht, ?_⟩, e.right_inv ht⟩
    intro hp
    have he := endCoordinate_at_puncture w hp
    have hr := e.right_inv ht
    change endCoordinate k w (e.symm t) = t at hr
    exact hn (hr.symm.trans he)

/-- The actual base end chart after removing the EW punctures. -/
def puncturedEndCoordinateHomeomorph {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) :
    {z : ℂ // z ∈ (endCoordinateChart hk hw).source ∧ z ∉ Surface.punctures k} ≃ₜ
      {t : ℂ // t ∈ (endCoordinateChart hk hw).target ∧ t ≠ 0} :=
  (endCoordinateChart hk hw).homeomorphOfImageSubsetSource
    (fun _ hz => hz.1) (endCoordinateChart_punctured_image hk hw)

@[simp] theorem puncturedEndCoordinateHomeomorph_apply {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k)
    (z : {z : ℂ // z ∈ (endCoordinateChart hk hw).source ∧ z ∉ Surface.punctures k}) :
    (puncturedEndCoordinateHomeomorph hk hw z).val = endCoordinate k w z.val := rfl

/-- The base end coordinate is locally a homeomorphism on its source viewed
inside the actual punctured parameter plane. -/
theorem endCoordinate_isLocalHomeomorphOn_punctured {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) :
    IsLocalHomeomorphOn (fun z : PuncturedPlane k => endCoordinate k w z.val)
      {z | z.val ∈ (endCoordinateChart hk hw).source} := by
  have ho : IsOpen {z : ℂ | z ∉ Surface.punctures k} :=
    (isClosed_eq (continuous_id.pow (2 * k)) continuous_const).isOpen_compl
  have hs : IsLocalHomeomorph (fun z : PuncturedPlane k => z.val) :=
    ho.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have he : IsLocalHomeomorphOn (endCoordinate k w) (endCoordinateChart hk hw).source :=
    fun z hz => ⟨endCoordinateChart hk hw, hz, rfl⟩
  exact he.comp
    (hs.isLocalHomeomorphOn.mono (Set.subset_univ _)) (fun _ hz => hz)

lemma endCoordinate_ne_zero_at_finite {k : ℕ} (w : ℂ) (b : PuncturedPlane k) :
    endCoordinate k w b.val ≠ 0 := by
  rw [endCoordinate_eq_heightCayley]
  split_ifs
  · exact heightCayley_ne_zero b.property
  · exact inv_ne_zero (heightCayley_ne_zero b.property)

/-- Basepoint normalization preserves local invertibility of the end chart. -/
theorem normalizedEndCoordinate_isLocalHomeomorphOn_punctured {k : ℕ}
    (hk : 2 ≤ k) {w : ℂ} (hw : w ∈ Surface.punctures k) (b : PuncturedPlane k) :
    IsLocalHomeomorphOn (fun z : PuncturedPlane k =>
      endCoordinate k w z.val / endCoordinate k w b.val)
      {z | z.val ∈ (endCoordinateChart hk hw).source} := by
  let e := Homeomorph.mulRight₀ (endCoordinate k w b.val)⁻¹
    (inv_ne_zero (endCoordinate_ne_zero_at_finite w b))
  have he := e.isLocalHomeomorph.isLocalHomeomorphOn.comp
    (endCoordinate_isLocalHomeomorphOn_punctured hk hw)
    (Set.mapsTo_univ _ _)
  simpa only [e, Homeomorph.coe_mulRight₀, Function.comp_def, div_eq_mul_inv] using he

end KsIndex.KarcherData
