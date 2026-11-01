module

public import KsIndexLean.KarcherTensorOverlap
public import KsIndexLean.SphericalChartTransition

@[expose] public section


/-! The EW parameter surface is the actual sphere minus its finite punctures.
It is not identified with the ambient image of the immersion. -/
noncomputable section
open Set
namespace KsIndex.KarcherData

/-- Remove exactly the finite EW punctures from the parameter sphere. -/
def ParameterSphere (k : ℕ) :=
  {p : Spherical.Sphere // p ∉ Spherical.sphereChart '' Surface.punctures k}

instance (k : ℕ) : TopologicalSpace (ParameterSphere k) :=
  inferInstanceAs (TopologicalSpace {p : Spherical.Sphere //
    p ∉ Spherical.sphereChart '' Surface.punctures k})

/-- Finite parameter points in the spherical carrier. -/
def finiteParameter {k : ℕ} (w : PuncturedPlane k) : ParameterSphere k :=
  ⟨Spherical.sphereChart w.val, by
    rintro ⟨z, hz, he⟩
    exact w.property (Spherical.sphereChart_injective he ▸ hz)⟩

/-- Holomorphic infinity chart; the existing southChart alone uses 1/conj(v). -/
def infinitySphereChart (v : ℂ) : Spherical.Sphere := Spherical.southChart (starRingEnd ℂ v)

lemma infinitySphereChart_overlap {v : ℂ} (hv : v ≠ 0) :
    infinitySphereChart v = Spherical.sphereChart v⁻¹ := by
  rw [infinitySphereChart, Spherical.southChart_eq_sigma (by simpa using hv)]
  simp [Bracket.σ]

lemma infinitySphereChart_zero_height : (infinitySphereChart 0).val 2 = 1 := by
  change -((‖starRingEnd ℂ (0 : ℂ)‖ ^ 2 - 1) / (1 + ‖starRingEnd ℂ (0 : ℂ)‖ ^ 2)) = 1
  norm_num

lemma north_unique (p : Spherical.Sphere) (hp : p.val 2 = 1) :
    p = infinitySphereChart 0 := by
  have hs := Spherical.sphere_sum_sq p
  rw [hp] at hs
  have h0 : p.val 0 = 0 := by nlinarith [sq_nonneg (p.val 1), sq_nonneg (p.val 0)]
  have h1 : p.val 1 = 0 := by nlinarith [sq_nonneg (p.val 1), sq_nonneg (p.val 0)]
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [infinitySphereChart, Spherical.southChart, Spherical.reflectSphere,
    Spherical.reflectAmbient, Spherical.sphereChart, Spherical.stereoPoint, h0, h1, hp]

/-- The regular point at infinity belongs to the parameter surface for all k. -/
def infinityParameter (k : ℕ) : ParameterSphere k :=
  ⟨infinitySphereChart 0, by
    rintro ⟨z, _, he⟩
    have hh := congrArg (fun p : Spherical.Sphere => p.val 2) he
    rw [infinitySphereChart_zero_height] at hh
    exact Spherical.stereoPoint_third_ne_one z hh⟩

lemma finiteParameter_ne_infinity {k : ℕ} (w : PuncturedPlane k) :
    finiteParameter w ≠ infinityParameter k := by
  intro he
  have hh := congrArg (fun p : ParameterSphere k => p.val.val 2) he
  change (Spherical.sphereChart w.val).val 2 = (infinitySphereChart 0).val 2 at hh
  rw [infinitySphereChart_zero_height] at hh
  exact Spherical.stereoPoint_third_ne_one w.val hh

/-- Every point is either an ordinary finite non-puncture or the regular infinity. -/
theorem parameterSphere_cases {k : ℕ} (p : ParameterSphere k) :
    p = infinityParameter k ∨ ∃ w : PuncturedPlane k, finiteParameter w = p := by
  by_cases hp : p.val.val 2 = 1
  · exact Or.inl (Subtype.ext (north_unique p.val hp))
  · have hc : Spherical.sphereChart (Spherical.stereoCoord p.val.val) = p.val :=
      Subtype.ext (Spherical.stereoPoint_stereoCoord p.val hp)
    have ha : Spherical.stereoCoord p.val.val ∉ Surface.punctures k := by
      intro hz
      exact p.property ⟨_, hz, hc⟩
    exact Or.inr ⟨⟨_, ha⟩, Subtype.ext hc⟩

/-- A puncture-free infinity neighborhood, with the ordinary sphere topology. -/
def infinityParameterChart {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr : r ≤ 1)
    (v : Metric.ball (0 : ℂ) r) : ParameterSphere k :=
  ⟨infinitySphereChart v.val, by
    by_cases hv : v.val = 0
    · rw [hv]
      exact (infinityParameter k).property
    · rw [infinitySphereChart_overlap hv]
      rintro ⟨z, hz, he⟩
      have hzi := Spherical.sphereChart_injective he
      exact inv_not_puncture_of_norm_lt_one hk
        ((by simpa only [Metric.mem_ball, dist_zero_right] using v.property : ‖v.val‖ < r).trans_le hr) (hzi ▸ hz)⟩

lemma infinityParameterChart_zero {k : ℕ} (hk : 2 ≤ k) {r : ℝ}
    (hr : r ≤ 1) (hr0 : 0 < r) :
    infinityParameterChart hk hr ⟨0, Metric.mem_ball_self hr0⟩ = infinityParameter k := rfl

lemma infinityParameterChart_overlap {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr : r ≤ 1)
    (v : infinityOverlap r) :
    infinityParameterChart hk hr ⟨v.val, by simpa using v.property.2⟩ =
      finiteParameter (infinityOverlapPoint hk hr v) :=
  Subtype.ext (infinitySphereChart_overlap v.property.1)

lemma continuous_finiteParameter (k : ℕ) : Continuous (finiteParameter (k := k)) :=
  (Spherical.continuous_sphereChart.comp continuous_subtype_val).subtype_mk _

lemma continuous_infinitySphereChart : Continuous infinitySphereChart :=
  Spherical.continuous_reflectSphere.comp
    (Spherical.continuous_sphereChart.comp Complex.continuous_conj)

lemma continuous_infinityParameterChart {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr : r ≤ 1) :
    Continuous (infinityParameterChart hk hr) :=
  (continuous_infinitySphereChart.comp continuous_subtype_val).subtype_mk _

/-- Removing the EW ends leaves an open subset of the actual parameter sphere. -/
lemma isOpen_parameterSphere {k : ℕ} (hk : 2 ≤ k) :
    IsOpen (Spherical.sphereChart '' Surface.punctures k)ᶜ := by
  have hc : IsClosed (Surface.punctures k) :=
    isClosed_eq (continuous_id.pow (2 * k)) continuous_const
  have hcompact : IsCompact (Surface.punctures k) :=
    (isCompact_sphere (0 : ℂ) 1).of_isClosed_subset hc
      (fun z hz => mem_sphere_zero_iff_norm.mpr (puncture_norm hk hz))
  exact (hcompact.image Spherical.continuous_sphereChart).isClosed.isOpen_compl

lemma finiteParameter_injective (k : ℕ) : Function.Injective (finiteParameter (k := k)) := by
  intro x y h
  apply Subtype.ext
  exact Spherical.sphereChart_injective (congrArg Subtype.val h)

lemma infinitySphereChart_injective : Function.Injective infinitySphereChart :=
  Spherical.reflectSphere_involutive.injective.comp
    (Spherical.sphereChart_injective.comp (starRingEnd ℂ).injective)

lemma infinityParameterChart_injective {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr : r ≤ 1) :
    Function.Injective (infinityParameterChart hk hr) := by
  intro v w h
  exact Subtype.ext (infinitySphereChart_injective (congrArg Subtype.val h))

/-- The finite chart and any constructed infinity disk cover the whole parameter surface. -/
theorem parameterSphere_chart_cover {k : ℕ} (hk : 2 ≤ k) {r : ℝ}
    (hr0 : 0 < r) (hr : r ≤ 1) (p : ParameterSphere k) :
    (∃ w : PuncturedPlane k, finiteParameter w = p) ∨
      ∃ v : Metric.ball (0 : ℂ) r, infinityParameterChart hk hr v = p := by
  rcases parameterSphere_cases p with hp | hp
  · right
    exact ⟨⟨0, Metric.mem_ball_self hr0⟩, (infinityParameterChart_zero hk hr hr0).trans hp.symm⟩
  · exact Or.inl hp

end KsIndex.KarcherData
