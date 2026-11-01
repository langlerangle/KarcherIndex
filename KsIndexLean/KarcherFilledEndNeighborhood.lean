module

public import KsIndexLean.KarcherFilledEndInverse

@[expose] public section


/-! The filled root-disk image contains a neighborhood of its added vertex. -/
noncomputable section
open Set Topology Filter
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]
variable (R : PaperHalfPeriodRealization k) {w : ℂ} (hw : w ∈ Surface.punctures k)

/-- An actual end point whose root is small lies in the filled root-disk image. -/
lemma mem_closedEndImage_of_parameter (r : ℝ)
    (hr : Metric.closedBall (0 : ℂ) r ⊆ EndRegion (m := m) hw) (hr0 : 0 < r)
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m)
    (z : PuncturedPlane k) (hz : z.val ∈ (endCoordinateChart h.out hw).source)
    (hp : HeightLift.quotientProjection m q = finiteParameter z)
    (hs : ‖endCoordinate k w z.val / endCoordinate k w (reflectionBasepoint k).val‖ < r ^ m) :
    (periodQuotientHomeomorph R q).val ∈ Set.range (closedEndInverse R hw r hr) := by
  let e := quotientEndHomeomorph h.out (NeZero.pos m) hw (reflectionBasepoint k) R.C R.hC
  let x : quotientEndSource h.out hw (reflectionBasepoint k) R.C (m := m) := ⟨q, z, hz, hp⟩
  let t := e x
  have he : t.val = quotientEndRoot h.out (NeZero.pos m) (reflectionBasepoint k) w R.C q := rfl
  have ht : ‖t.val‖ < r := by
    apply lt_of_pow_lt_pow_left₀ m hr0.le
    rw [← norm_pow, he, quotientEndRoot_pow_finite h.out (NeZero.pos m)
      (reflectionBasepoint k) z w R.C q hp]
    exact hs
  have hn : t.val ≠ 0 := by
    have hh := congrArg (fun S : Set ℂ => t.val ∈ S)
      (quotientEndTarget_eq h.out (NeZero.pos m) hw (reflectionBasepoint k))
    exact (hh.mp t.property).2
  refine ⟨⟨t.val, by simpa using ht.le⟩, ?_⟩
  simp only [closedEndInverse, filledEndInverse, dite_eq_right hn]
  have hh : e.symm t = x := e.symm_apply_apply x
  exact congrArg (fun y => (periodQuotientHomeomorph R y.val).val) hh

omit [NeZero m] in
/-- The source chart and root-size condition hold near the puncture, both for
an interior parameter and its inverse conjugate. -/
lemma exists_parameter_control (r : ℝ) (hr : 0 < r) :
    ∃ U : Set ℂ, IsOpen U ∧ w ∈ U ∧ ∀ z ∈ U,
      z ≠ 0 ∧ z ∈ (endCoordinateChart h.out hw).source ∧
      (starRingEnd ℂ z)⁻¹ ∈ (endCoordinateChart h.out hw).source ∧
      ‖endCoordinate k w z / endCoordinate k w (reflectionBasepoint k).val‖ < r ^ m ∧
      ‖endCoordinate k w ((starRingEnd ℂ z)⁻¹) /
        endCoordinate k w (reflectionBasepoint k).val‖ < r ^ m := by
  let P := fun z : ℂ => z ∈ (endCoordinateChart h.out hw).source ∧
    ‖endCoordinate k w z / endCoordinate k w (reflectionBasepoint k).val‖ < r ^ m
  have hc : ContinuousAt (endCoordinate k w) w :=
    (endCoordinateChart h.out hw).continuousOn.continuousAt
      ((endCoordinateChart h.out hw).open_source.mem_nhds (endCoordinateChart_mem_source h.out hw))
  have hn : w ≠ 0 := puncture_ne_zero h.out hw
  have hv : ∀ᶠ z in 𝓝 w, P z := by
    apply Filter.Eventually.and
    · exact (endCoordinateChart h.out hw).open_source.mem_nhds
        (endCoordinateChart_mem_source h.out hw)
    · have hh := (hc.div_const (endCoordinate k w (reflectionBasepoint k).val)).norm
      have hh0 : Tendsto (fun z =>
          ‖endCoordinate k w z / endCoordinate k w (reflectionBasepoint k).val‖)
          (𝓝 w) (𝓝 (0 : ℝ)) := by
        simpa only [endCoordinate_self hw, zero_div, norm_zero] using hh.tendsto
      exact hh0 (Iio_mem_nhds (pow_pos hr m))
  have hi : ContinuousAt (fun z : ℂ => (starRingEnd ℂ z)⁻¹) w :=
    Complex.continuous_conj.continuousAt.inv₀ ((map_ne_zero _).mpr hn)
  have he : (starRingEnd ℂ w)⁻¹ = w := by
    rw [Complex.inv_eq_conj (by simpa using puncture_norm h.out hw)]
    simp
  have hv' : ∀ᶠ z in 𝓝 w, P ((starRingEnd ℂ z)⁻¹) := hi.tendsto (he ▸ hv)
  have hne : ∀ᶠ z in 𝓝 w, z ≠ 0 := (isClosed_singleton.isOpen_compl).mem_nhds hn
  obtain ⟨U, hsub, ho, hwU⟩ := mem_nhds_iff.mp (hne.and (hv.and hv'))
  refine ⟨U, ho, hwU, ?_⟩
  intro z hz
  have hh := hsub hz
  exact ⟨hh.1, hh.2.1.1, hh.2.2.1, hh.2.1.2, hh.2.2.2⟩

lemma periodQuotientHomeomorph_ordered (i : ZMod (2 * m)) (v : PuncturedClosedDisk k) :
    (periodQuotientHomeomorph R (R.orderedDiskPoint i v)).val =
      Quotient.mk (filledSetoid k m) (i, ⟨v.val.val, v.property⟩) := by
  have he : R.gluedDiskHomeomorph.symm (R.orderedDiskPoint i v) =
      Quotient.mk (diskGluingSetoid k m) (i,v) :=
    R.gluedDiskHomeomorph.symm_apply_apply (Quotient.mk (diskGluingSetoid k m) (i,v))
  change (regularHomeomorph (R.gluedDiskHomeomorph.symm (R.orderedDiskPoint i v))).val = _
  rw [he]
  rfl

/-- The embedded closed root disk contains an ambient neighborhood of the
added vertex; nearby points on every incident sheet are included. -/
theorem closedEndImage_mem_nhds (r : ℝ) (hr0 : 0 < r)
    (hr : Metric.closedBall (0 : ℂ) r ⊆ EndRegion (m := m) hw) :
    Set.range (closedEndInverse R hw r hr) ∈ 𝓝 (vertex w hw) := by
  obtain ⟨U, hU, hwU, hcontrol⟩ := exists_parameter_control (m := m) hw r hr0
  have hopen : IsOpen {q : FilledChain k m | (coordinate q).val ∈ U} :=
    hU.preimage (continuous_subtype_val.comp continuous_coordinate)
  apply mem_of_superset (hopen.mem_nhds (by simpa using hwU))
  intro q hq
  induction q using Quotient.inductionOn with
  | h p =>
    have hc := hcontrol p.2.val hq
    by_cases hp : p.2.val ∈ Surface.punctures k
    · have he := (endCoordinateChart_puncture_iff h.out hw hc.2.1).mp hp
      have hvertex : Quotient.mk (filledSetoid k m) p = vertex w hw :=
        (coordinate_eq_vertex_iff w hw _).mp he
      rw [hvertex]
      refine ⟨⟨0, by simpa using hr0.le⟩, ?_⟩
      exact filledEndInverse_center R hw
    · let v : PuncturedClosedDisk k := ⟨⟨p.2.val, hp⟩, p.2.property⟩
      have he : (periodQuotientHomeomorph R (R.orderedDiskPoint p.1 v)).val =
          Quotient.mk (filledSetoid k m) p := periodQuotientHomeomorph_ordered R p.1 v
      rw [← he]
      obtain ⟨j, hj | hj⟩ := PaperHalfPeriodRealization.copyIndex_cases p.1
      · rw [hj, R.orderedDiskPoint_even]
        apply mem_closedEndImage_of_parameter R hw r hr hr0 _ v.val hc.2.1
        · exact R.evenDiskPoint_projection _ v
        · exact hc.2.2.2.1
      · rw [hj, R.orderedDiskPoint_odd]
        let z : PuncturedPlane k :=
          ⟨(starRingEnd ℂ p.2.val)⁻¹, inverse_conjugate_not_puncture hp⟩
        apply mem_closedEndImage_of_parameter R hw r hr hr0 _ z hc.2.2.1
        · exact (R.oddDiskPoint_projection _ v).trans
            (parameterSeamReflection_finite h.out v.val hc.1 z.property)
        · exact hc.2.2.2.2

end KsIndex.KarcherData.DiskCompactification
