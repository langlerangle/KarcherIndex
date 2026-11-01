module

public import KsIndexLean.NullityInjection
public import KsIndexLean.LocalTrace
public import KsIndexLean.WeakBoundaryDomains

@[expose] public section


/-!
# Boundary traces of the sector restriction

For an odd reflection eigenvalue (`zeta 2 ^ s = -1`), the copy-`0` field vanishes
pointwise on the corresponding open boundary arc. The reflection eigen-equation
and matching seam values give this vanishing. Seam gluing gives continuity from
the disk side; together with the exterior zero normalization, this gives continuity
on the open sign-set of the arc.

The local trace-agreement theorem and a locally-null exhaustion then give an
almost-everywhere zero Sobolev trace on that arc. Localization stays away from
puncture endpoints; no continuity assumption there is used.

For `k ≥ 2` and `s₁, s₀ < 2`, `sectorRestrict_mem` combines these trace statements
with weak rotation-character membership. The result lies in
`mixedCharacterDomain k r (decide (s₁ = 0)) (decide (s₀ = 0))`:
`s₁` controls arc `1` and `s₀` controls arc `0`. A `false` flag imposes zero trace;
a `true` flag imposes no trace restriction on this form domain.
-/

noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.SurfaceForm KsIndex.WeakH1 KsIndex.Trace
open KsIndex.FaithfulInjection Complex MeasureTheory Filter Topology
open KsIndex.FormIndex
open scoped ContDiff

variable {k r s₁ s₀ : ℕ}

/-! ### Pointwise vanishing on the fixed arc (odd parity) -/

/-- The reflection eigen-equations at copy `0`, packaged. -/
lemma sector_copy_three {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) (z : ℂ) :
    (uncurryE 2).symm W 3 z = zeta 2 ^ s₀ * (uncurryE 2).symm W 0 z := by
  change W ((3 : ZMod (2 * 2)), z) = zeta 2 ^ s₀ * W ((0 : ZMod (2 * 2)), z)
  have h := congrFun (sector_reflNeg_eigen hW) ((0 : ZMod (2 * 2)), z)
  change W ((-1 : ZMod (2 * 2)) - 0, z) = (zeta 2 ^ s₀ • W) (0, z) at h
  rw [show (-1 : ZMod (2 * 2)) - 0 = 3 from by decide] at h
  simpa [Pi.smul_apply, smul_eq_mul] using h

lemma sector_copy_one {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) (z : ℂ) :
    (uncurryE 2).symm W 1 z = zeta 2 ^ s₁ * (uncurryE 2).symm W 0 z := by
  change W ((1 : ZMod (2 * 2)), z) = zeta 2 ^ s₁ * W ((0 : ZMod (2 * 2)), z)
  have h := congrFun (sector_reflOne_eigen hW) ((0 : ZMod (2 * 2)), z)
  change W ((1 : ZMod (2 * 2)) - 0, z) = (zeta 2 ^ s₁ • W) (0, z) at h
  rw [show (1 : ZMod (2 * 2)) - 0 = 1 from by decide] at h
  simpa [Pi.smul_apply, smul_eq_mul] using h

/-- Odd `z=0` parity kills the copy-`0` values on `arc k 0` (`seamArc 3 = arc k 0`). -/
lemma sector_vanishes_arc0 {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) (hodd : zeta 2 ^ s₀ = -1)
    {z : ℂ} (hz : z ∈ arc k 0) : (uncurryE 2).symm W 0 z = 0 := by
  obtain ⟨-, -, -, -, hsv⟩ := sector_field_mem hW
  have hzs : z ∈ seamArc k 2 (3 : ZMod (2 * 2)) := by
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨hz1, ?_⟩
    rw [show (parity 2 ((3 : ZMod (2 * 2)) + 1)).val = 0 from by decide]
    simpa using hz2
  have hs := hsv (3 : ZMod (2 * 2)) z hzs
  rw [show (3 : ZMod (2 * 2)) + 1 = 0 from by decide] at hs
  -- `hs : u 0 z = u 3 z`; the eigen-equation gives `u 3 z = −u 0 z`
  have h3 := sector_copy_three hW z
  rw [hodd, neg_one_mul] at h3
  rw [h3] at hs
  have h2 : (2 : ℂ) * (uncurryE 2).symm W 0 z = 0 := by linear_combination hs
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-- Odd `z=π` parity kills the copy-`0` values on `arc k 1` (`seamArc 0 = arc k 1`). -/
lemma sector_vanishes_arc1 {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) (hodd : zeta 2 ^ s₁ = -1)
    {z : ℂ} (hz : z ∈ arc k 1) : (uncurryE 2).symm W 0 z = 0 := by
  obtain ⟨-, -, -, -, hsv⟩ := sector_field_mem hW
  have hzs : z ∈ seamArc k 2 (0 : ZMod (2 * 2)) := by
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨hz1, ?_⟩
    rw [show (parity 2 ((0 : ZMod (2 * 2)) + 1)).val = 1 from by decide]
    simpa using hz2
  have hs := hsv (0 : ZMod (2 * 2)) z hzs
  rw [show (0 : ZMod (2 * 2)) + 1 = 1 from by decide] at hs
  -- `hs : u 1 z = u 0 z`; the eigen-equation gives `u 1 z = −u 0 z`
  have h1 := sector_copy_one hW z
  rw [hodd, neg_one_mul] at h1
  rw [h1] at hs
  have h2 : (2 : ℂ) * (uncurryE 2).symm W 0 z = 0 := by linear_combination hs.symm
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-! ### Collar continuity up to the open arcs -/

/-- Near an `arc k 1` point, the copy-`0` field is (within the closed disk) the inside branch
of `glue u 0`, hence continuous there. -/
lemma sector_field_continuousWithinAt_arc1 {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) {w : ℂ} (hw : w ∈ arc k 1) :
    ContinuousWithinAt ((uncurryE 2).symm W 0) {z : ℂ | ‖z‖ ≤ 1} w := by
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, -, -, -, hsv⟩ := sector_field_mem hW
  have hws : w ∈ seamArc k 2 (0 : ZMod (2 * 2)) := by
    obtain ⟨hz1, hz2⟩ := hw
    refine ⟨hz1, ?_⟩
    rw [show (parity 2 ((0 : ZMod (2 * 2)) + 1)).val = 1 from by decide]
    simpa using hz2
  have hglue : ContinuousAt (glue ((uncurryE 2).symm W) 0) w := (hsm2 0 w hws).continuousAt
  apply hglue.continuousWithinAt.congr
  · intro z hz
    have hz' : ‖z‖ ≤ 1 := hz
    simp [glue, hz']
  · have hw' : ‖w‖ ≤ 1 := le_of_eq hw.1
    simp [glue, hw']

/-- Near an `arc k 0` point, the copy-`0` field is (within the closed disk, away from `0`)
`glue u 3` composed with the circle inversion, hence continuous there. -/
lemma sector_field_continuousWithinAt_arc0 {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) {w : ℂ} (hw : w ∈ arc k 0) :
    ContinuousWithinAt ((uncurryE 2).symm W 0) {z : ℂ | ‖z‖ ≤ 1} w := by
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, -, -, -, hsv⟩ := sector_field_mem hW
  have hws : w ∈ seamArc k 2 (3 : ZMod (2 * 2)) := by
    obtain ⟨hz1, hz2⟩ := hw
    refine ⟨hz1, ?_⟩
    rw [show (parity 2 ((3 : ZMod (2 * 2)) + 1)).val = 0 from by decide]
    simpa using hz2
  have hw1 : ‖w‖ = 1 := hw.1
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    exact zero_ne_one hw1
  -- the composite `glue u 3 ∘ σ` is continuous at `w` …
  have hglue : ContinuousAt (glue ((uncurryE 2).symm W) 3) w := (hsm2 3 w hws).continuousAt
  have hσ : ContinuousAt (fun z : ℂ => 1 / (starRingEnd ℂ) z) w := by
    have h1 : ContinuousAt (starRingEnd ℂ) w := Complex.continuous_conj.continuousAt
    have h2 : (starRingEnd ℂ) w ≠ 0 := by simpa using hw0
    exact continuousAt_const.div h1 h2
  have hσw : (1 / (starRingEnd ℂ) w) = w := sigma_circle hw1
  have hglue' : ContinuousAt (glue ((uncurryE 2).symm W) 3) (1 / (starRingEnd ℂ) w) := by
    rw [hσw]
    exact hglue
  have hcomp : ContinuousAt
      (fun z => glue ((uncurryE 2).symm W) 3 (1 / (starRingEnd ℂ) z)) w :=
    ContinuousAt.comp (x := w) (g := glue ((uncurryE 2).symm W) 3)
      (f := fun z : ℂ => 1 / (starRingEnd ℂ) z) hglue' hσ
  -- … and agrees with `u 0` on the closed-disk side near `w` (eventually: the open
  -- sign-set of `arc k 0` is a neighbourhood of `w` avoiding `0` and the other arc)
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    obtain ⟨-, hz2⟩ := hw
    rw [hk0'] at hz2
    norm_num at hz2
  have hopen : IsOpen {z : ℂ | (-1 : ℝ) ^ 0 * ((z ^ k).re) < 0} := by
    have hc : Continuous fun z : ℂ => (-1 : ℝ) ^ 0 * ((z ^ k).re) :=
      continuous_const.mul (Complex.continuous_re.comp (continuous_pow k))
    exact isOpen_lt hc continuous_const
  have hkey : ∀ z : ℂ, ‖z‖ ≤ 1 → (-1 : ℝ) ^ 0 * ((z ^ k).re) < 0 →
      (uncurryE 2).symm W 0 z = glue ((uncurryE 2).symm W) 3 (1 / (starRingEnd ℂ) z) := by
    intro z hz1 hzT
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega : k ≠ 0)] at hzT
      simp at hzT
    rcases eq_or_lt_of_le hz1 with hz1' | hz1'
    · -- on the circle: `σ z = z`; `SeamVal` at seam `3`
      have hσz : (1 / (starRingEnd ℂ) z) = z := sigma_circle hz1'
      rw [hσz]
      have hz1'' : ‖z‖ ≤ 1 := le_of_eq hz1'
      simp only [glue]
      rw [ite_eq_left hz1'']
      have hzs : z ∈ seamArc k 2 (3 : ZMod (2 * 2)) := by
        refine ⟨hz1', ?_⟩
        rw [show (parity 2 ((3 : ZMod (2 * 2)) + 1)).val = 0 from by decide]
        simpa using hzT
      have hs := hsv (3 : ZMod (2 * 2)) z hzs
      rw [show (3 : ZMod (2 * 2)) + 1 = 0 from by decide] at hs
      exact hs
    · -- strictly inside: the outside branch of `glue u 3` at `σ z` returns `u 0 z`
      have hσn : 1 < ‖1 / (starRingEnd ℂ) z‖ := by
        rw [norm_sigma]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hz0, hz1'⟩
      simp only [glue]
      rw [ite_eq_right (not_le.mpr hσn), sigma_sigma,
        show (3 : ZMod (2 * 2)) + 1 = 0 from by decide]
  apply hcomp.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
  · have hmem : {z : ℂ | (-1 : ℝ) ^ 0 * ((z ^ k).re) < 0} ∈
        𝓝[{z : ℂ | ‖z‖ ≤ 1}] w :=
      mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hw.2)
    filter_upwards [hmem, self_mem_nhdsWithin] with z hzT hz1
    exact hkey z hz1 hzT
  · exact hkey w (le_of_eq hw.1) hw.2

/-! ### The trace-zero engine -/

/-- The sign-set of an arc family is open. -/
lemma isOpen_signSet (k p : ℕ) : IsOpen {z : ℂ | (-1 : ℝ) ^ p * ((z ^ k).re) < 0} :=
  isOpen_lt (continuous_const.mul (Complex.continuous_re.comp (continuous_pow k)))
    continuous_const

/-- `boundaryArc` is open in the circle (the norm condition is automatic there). -/
lemma isOpen_boundaryArc (k p : ℕ) : IsOpen (boundaryArc k p) := by
  have h : boundaryArc k p =
      (fun w : Circle₁ => (w : ℂ)) ⁻¹' {z : ℂ | (-1 : ℝ) ^ p * ((z ^ k).re) < 0} := by
    ext w
    rw [mem_boundaryArc]
    rfl
  rw [h]
  exact (isOpen_signSet k p).preimage continuous_subtype_val

/-- **The trace-zero engine**: a `ComplexH1` element whose values agree with a function
continuous on the open sign-set and vanishing on the arc has a.e.-vanishing trace there.
Uses `exists_boundary_neighbourhood_agreement` (the bump-localized wedge argument) and a
locally-null exhaustion. -/
lemma trace_ae_zero_engine {u : ComplexH1} {f : ℂ → ℂ} {p : ℕ}
    (hval : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)] f)
    (hf : ContinuousOn f {z : ℂ | (-1 : ℝ) ^ p * ((z ^ k).re) < 0})
    (hvan : ∀ z ∈ arc k p, f z = 0) :
    (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict (boundaryArc k p)] 0 := by
  have hT := isOpen_signSet k p
  have he : ∀ᵐ z ∂volume.restrict (KsIndex.WeakH1.disk : Set ℂ),
      z ∈ {z : ℂ | (-1 : ℝ) ^ p * ((z ^ k).re) < 0} → valueCLM u z = f z := by
    filter_upwards [hval] with z hz _
    exact hz
  -- locality: around every arc point the trace vanishes a.e. on an open cap
  have hloc : ∀ x : Circle₁, x ∈ boundaryArc k p → ∃ A : Set Circle₁, IsOpen A ∧ x ∈ A ∧
      (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] 0 := by
    intro x hx
    have hxT : (x : ℂ) ∈ {z : ℂ | (-1 : ℝ) ^ p * ((z ^ k).re) < 0} :=
      (mem_boundaryArc k p x).mp hx
    obtain ⟨A, hA, hxA, hAe⟩ := exists_boundary_neighbourhood_agreement u hT hf hxT he
    refine ⟨A ∩ boundaryArc k p, hA.inter (isOpen_boundaryArc k p), ⟨hxA, hx⟩, ?_⟩
    have hAe' := hAe.filter_mono
      (ae_mono (Measure.restrict_mono
        (Set.inter_subset_left : A ∩ boundaryArc k p ⊆ A) le_rfl))
    filter_upwards [hAe',
      ae_restrict_mem (hA.inter (isOpen_boundaryArc k p)).measurableSet] with w hw hwm
    rw [hw]
    have hwarc : (w : ℂ) ∈ arc k p := by
      have := hwm.2
      rw [mem_boundaryArc] at this
      exact ⟨mem_sphere_zero_iff_norm.mp w.property, this⟩
    simpa using hvan _ hwarc
  -- exhaustion: the bad set is locally null
  rw [Filter.EventuallyEq, ae_restrict_iff' (isOpen_boundaryArc k p).measurableSet]
  rw [ae_iff]
  have hbad : {w : Circle₁ | ¬(w ∈ boundaryArc k p →
      (diskTraceCLM u : Circle₁ → ℂ) w = (0 : Circle₁ → ℂ) w)} =
      {w : Circle₁ | w ∈ boundaryArc k p ∧ (diskTraceCLM u : Circle₁ → ℂ) w ≠ 0} := by
    ext w
    simp only [Set.mem_ofPred_eq, not_imp, Pi.zero_apply]
  rw [hbad]
  apply measure_null_of_locally_null
  intro y hy
  obtain ⟨A, hA, hyA, hAe⟩ := hloc y hy.1
  refine ⟨A ∩ {w : Circle₁ | w ∈ boundaryArc k p ∧
    (diskTraceCLM u : Circle₁ → ℂ) w ≠ 0}, ?_, ?_⟩
  · rw [Set.inter_comm]
    exact inter_mem_nhdsWithin _ (hA.mem_nhds hyA)
  · have h1 : ∀ᵐ w ∂circleMeasure, w ∈ A →
        (diskTraceCLM u : Circle₁ → ℂ) w = 0 := by
      have h := hAe
      rw [Filter.EventuallyEq, ae_restrict_iff' hA.measurableSet] at h
      filter_upwards [h] with w hw hwA
      simpa using hw hwA
    have hnull : circleMeasure {w : Circle₁ | w ∈ A ∧
        (diskTraceCLM u : Circle₁ → ℂ) w ≠ 0} = 0 := by
      have h2 := ae_iff.mp h1
      convert h2 using 2
      ext w
      simp only [Set.mem_ofPred_eq, not_imp]
    apply measure_mono_null ?_ hnull
    intro w hw
    exact ⟨hw.1, hw.2.2⟩

/-! ### Sign-set continuity and the membership assembly -/

/-- Odd `z=0` parity: the copy-`0` field is continuous on the whole open `arc k 0`
sign-set — interior smoothness, the collar continuity (with the arc VANISHING matching
the exterior zero), and the exterior normalization. -/
lemma sector_continuousOn_signSet0 {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) (hodd : zeta 2 ^ s₀ = -1) :
    ContinuousOn ((uncurryE 2).symm W 0)
      {z : ℂ | (-1 : ℝ) ^ 0 * ((z ^ k).re) < 0} := by
  intro x hx
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, -, -, -, -⟩ := sector_field_mem hW
  rcases lt_trichotomy ‖x‖ 1 with h | h | h
  · exact ((hsm1 0).continuousOn.continuousAt
      ((Metric.isOpen_ball).mem_nhds (mem_disk_iff.mpr h))).continuousWithinAt
  · have hxarc : x ∈ arc k 0 := ⟨h, hx⟩
    have hin := sector_field_continuousWithinAt_arc0 hW hxarc
    have hval0 := sector_vanishes_arc0 hW hodd hxarc
    have hout : ContinuousWithinAt ((uncurryE 2).symm W 0) {z : ℂ | 1 < ‖z‖} x := by
      apply continuousWithinAt_const.congr
      · intro y hy
        exact hsm3 0 y hy
      · exact hval0
    have huniv := hin.union hout
    have hcover : ({z : ℂ | ‖z‖ ≤ 1} ∪ {z : ℂ | 1 < ‖z‖}) = Set.univ := by
      ext z
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      by_cases hz : ‖z‖ ≤ 1
      · exact Or.inl hz
      · exact Or.inr (not_le.mp hz)
    rw [hcover, continuousWithinAt_univ] at huniv
    exact huniv.continuousWithinAt
  · have hev : (uncurryE 2).symm W 0 =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h] with z hz
      exact hsm3 0 z hz
    exact ((continuousAt_congr hev).mpr continuousAt_const).continuousWithinAt

/-- Odd `z=π` parity: the twin on the `arc k 1` sign-set. -/
lemma sector_continuousOn_signSet1 {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) (hodd : zeta 2 ^ s₁ = -1) :
    ContinuousOn ((uncurryE 2).symm W 0)
      {z : ℂ | (-1 : ℝ) ^ 1 * ((z ^ k).re) < 0} := by
  intro x hx
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, -, -, -, -⟩ := sector_field_mem hW
  rcases lt_trichotomy ‖x‖ 1 with h | h | h
  · exact ((hsm1 0).continuousOn.continuousAt
      ((Metric.isOpen_ball).mem_nhds (mem_disk_iff.mpr h))).continuousWithinAt
  · have hxarc : x ∈ arc k 1 := ⟨h, hx⟩
    have hin := sector_field_continuousWithinAt_arc1 hW hxarc
    have hval0 := sector_vanishes_arc1 hW hodd hxarc
    have hout : ContinuousWithinAt ((uncurryE 2).symm W 0) {z : ℂ | 1 < ‖z‖} x := by
      apply continuousWithinAt_const.congr
      · intro y hy
        exact hsm3 0 y hy
      · exact hval0
    have huniv := hin.union hout
    have hcover : ({z : ℂ | ‖z‖ ≤ 1} ∪ {z : ℂ | 1 < ‖z‖}) = Set.univ := by
      ext z
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      by_cases hz : ‖z‖ ≤ 1
      · exact Or.inl hz
      · exact Or.inr (not_le.mp hz)
    rw [hcover, continuousWithinAt_univ] at huniv
    exact huniv.continuousWithinAt
  · have hev : (uncurryE 2).symm W 0 =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h] with z hz
      exact hsm3 0 z hz
    exact ((continuousAt_congr hev).mpr continuousAt_const).continuousWithinAt

/-- Odd reflection parity `s₀` gives zero trace on `boundaryArc k 0`. -/
lemma sectorRestrict_zeroTrace_arc0 (hk : 2 ≤ k)
    (W : ↥(boundedJacobiSector k r s₁ s₀)) (hodd : zeta 2 ^ s₀ = -1) :
    sectorRestrictFun hk W ∈ zeroTraceDomain (boundaryArc k 0) := by
  rw [mem_zeroTraceDomain]
  exact trace_ae_zero_engine (sectorRestrictFun_value hk W)
    (sector_continuousOn_signSet0 W.property hodd)
    (fun z hz => sector_vanishes_arc0 W.property hodd hz)

/-- Odd reflection parity `s₁` gives zero trace on `boundaryArc k 1`. -/
lemma sectorRestrict_zeroTrace_arc1 (hk : 2 ≤ k)
    (W : ↥(boundedJacobiSector k r s₁ s₀)) (hodd : zeta 2 ^ s₁ = -1) :
    sectorRestrictFun hk W ∈ zeroTraceDomain (boundaryArc k 1) := by
  rw [mem_zeroTraceDomain]
  exact trace_ae_zero_engine (sectorRestrictFun_value hk W)
    (sector_continuousOn_signSet1 W.property hodd)
    (fun z hz => sector_vanishes_arc1 W.property hodd hz)

/-- The copy-`0` restriction
lies in the mixed character domain with the parity-determined flags: even parity
(`ζ₂^s = 1`) ⟹ Neumann (`true`, no constraint), odd (`ζ₂^s = −1`) ⟹ Dirichlet
(`false`, zero trace). -/
lemma sectorRestrict_mem (hk : 2 ≤ k) (hs₁ : s₁ < 2) (hs₀ : s₀ < 2)
    (W : ↥(boundedJacobiSector k r s₁ s₀)) :
    sectorRestrictFun hk W ∈
      mixedCharacterDomain k r (decide (s₁ = 0)) (decide (s₀ = 0)) := by
  refine ⟨⟨?_, ?_⟩, sectorRestrict_char_mem hk W⟩
  · -- arc 1 (the `b₁` slot)
    have h01 : s₁ = 0 ∨ s₁ = 1 := by omega
    rcases h01 with rfl | rfl
    · exact Submodule.mem_top
    · exact sectorRestrict_zeroTrace_arc1 hk W (by rw [pow_one, KsIndex.Bracket.zeta_two])
  · -- arc 0 (the `b₀` slot)
    have h01 : s₀ = 0 ∨ s₀ = 1 := by omega
    rcases h01 with rfl | rfl
    · exact Submodule.mem_top
    · exact sectorRestrict_zeroTrace_arc0 hk W (by rw [pow_one, KsIndex.Bracket.zeta_two])

end KsIndex.NullityDecomp
