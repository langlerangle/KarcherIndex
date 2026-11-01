module

public import KsIndexLean.KarcherSphericalUniqueness
public import KsIndexLean.KarcherCoverDescent

@[expose] public section


/-! Uniqueness of the normalized EW covering coordinate on the actual
intrinsic immersion. Only the uniqueness-relevant consequences of ewcover
items (1), (2), (3), (5) are required; smooth conformality is not assumed to
replace any of these conditions. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- A competing continuous coordinate with the paper's period, half-period,
upper boundary, and actual Gauss-normal conditions equals the constructed
projection. This is covering-coordinate uniqueness, not surface uniqueness. -/
theorem normalized_cover_unique (R : PaperHalfPeriodRealization k)
    (f : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ParameterSphere k)
    (hf : Continuous f)
    (hperiod : ∀ q, f (HeightLift.deck 1 q) = f q)
    (hfinite : ∀ q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C,
      ∃ w : PuncturedPlane k, f q.val = finiteParameter w)
    (hupper : ∀ q, (centeredLiftAmbient R.C R.t q).2.2 = Real.pi →
      ∃ w : PuncturedPlane k, f q = finiteParameter w ∧ w.val ∈ Surface.arc k 1)
    (hu : ∀ q, euclideanDot
      (fderiv ℝ (R.centeredChart q) (R.chartCenter q) 1) (parameterNormal (f q)) = 0)
    (hv : ∀ q, euclideanDot
      (fderiv ℝ (R.centeredChart q) (R.chartCenter q) Complex.I) (parameterNormal (f q)) = 0) :
    f = HeightLift.projection := by
  obtain ⟨g, ⟨hg, hfg⟩, _⟩ :=
    HeightLift.existsUnique_continuous_period_descent R.hC f hf hperiod
  have hn := R.cover_normal_orientation_of_halfPeriod f hf hu hv hfinite
  have hgn (p : ParameterSphere k) : parameterNormal (g p) = parameterNormal p := by
    obtain ⟨q, rfl⟩ := HeightLift.projection_surjective
      (F := extendedEWMap h.out (reflectionBasepoint k) R.C) p
    have he := congrFun hn q
    rw [hfg] at he
    exact he
  have hone : (1 : ℂ) ∉ Surface.punctures k := by norm_num [Surface.punctures]
  have ha : ∃ v : PuncturedPlane k,
      g (finiteParameter ⟨1, hone⟩) = finiteParameter v ∧ v.val ∈ Surface.arc k 1 := by
    let oneDisk : PuncturedClosedDisk k := ⟨⟨1, hone⟩, by norm_num⟩
    obtain ⟨q, hq⟩ := R.disk_bijective.surjective oneDisk
    have hp := R.projection_agrees q
    rw [hq] at hp
    have hz : HeightLift.height q.val + Real.pi = Real.pi :=
      (halfPeriod_height_pi_iff_arc h.out (reflectionBasepoint k) ⟨1, hone⟩ rfl R.C q hp.symm).mpr
        (by norm_num [Surface.arc])
    obtain ⟨v, hvf, hva⟩ := hupper q.val hz
    refine ⟨v, ?_, hva⟩
    have he := congrFun hfg q.val
    change f q.val = g (HeightLift.projection q.val) at he
    rw [← hp] at he
    exact he.symm.trans hvf
  have hid := normal_preserving_parameter_map_unique h.out g hg hgn hone ha
  rw [hfg, hid]
  rfl

end KsIndex.KarcherData.PaperHalfPeriodRealization
