module

public import KsIndexLean.RawPlanarInversion
public import KsIndexLean.RawPlanarCutoff

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

/-- Join explicit fields across a circle, with a fixed choice on the null boundary. -/
def radialJoin (c : ℝ) (u v : ℂ → ℂ) (z : ℂ) : ℂ := if ‖z‖ ≤ c then u z else v z

lemma measurable_radialJoin (c : ℝ) {u v : ℂ → ℂ}
    (hu : Measurable u) (hv : Measurable v) : Measurable (radialJoin c u v) :=
  Measurable.ite (measurableSet_le measurable_norm measurable_const) hu hv

lemma sliceFun_radialJoin (c : ℝ) (u v : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (w : Circle₁) :
    sliceFun (radialJoin c u v) r w =
      joinAt c (fun t => sliceFun u t w) (fun t => sliceFun v t w) r := by
  have hw : ‖(w : ℂ)‖ = 1 := by simp
  simp only [sliceFun, radialJoin, joinAt, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, hw, mul_one]

lemma ae_raw_joined_slice {a c b : ℝ} (ha : 0 < a) (hac : a < c)
    {u v : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a c)))
    (hv : MemLp v 2 (volume.restrict (annulusSet c b))) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      sliceFun (radialJoin c u v) r =ᵐ[circleMeasure]
        (joinAt c (sliceLp a c u) (sliceLp c b v) r : Lp ℂ 2 circleMeasure) := by
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp (ae_raw_sliceLp ha hu),
    (ae_restrict_iff' measurableSet_Ioo).mp (ae_raw_sliceLp (ha.trans hac) hv),
    volume.ae_ne c] with r hlu hlv hrc hr
  by_cases hle : r ≤ c
  · have hs := hlu ⟨hr.1, lt_of_le_of_ne hle hrc⟩
    filter_upwards [hs] with w hw
    simpa only [sliceFun_radialJoin c u v (ha.trans hr.1), joinAt, ite_eq_left hle] using hw
  · have hs := hlv ⟨lt_of_not_ge hle, hr.2⟩
    filter_upwards [hs] with w hw
    simpa only [sliceFun_radialJoin c u v (ha.trans hr.1), joinAt, ite_eq_right hle] using hw

/-- Finite planar energy patches across the circle without a trace hypothesis. -/
theorem memLp_radialJoin {a c b : ℝ} (ha : 0 < a) (hac : a < c) (hcb : c < b)
    {u v : ℂ → ℂ} (hmu : Measurable u) (hmv : Measurable v)
    (hu : MemLp u 2 (volume.restrict (annulusSet a c)))
    (hv : MemLp v 2 (volume.restrict (annulusSet c b))) :
    MemLp (radialJoin c u v) 2 (volume.restrict (annulusSet a b)) := by
  apply memLp_annulus_of_raw_slices ha (hac.trans hcb) (measurable_radialJoin c hmu hmv)
    (joinAt_sq_integrable hac.le hcb.le
      (intervalIntegrable_sliceLp_norm_sq ha hac hu)
      (intervalIntegrable_sliceLp_norm_sq (ha.trans hac) hcb hv))
  exact ae_raw_joined_slice ha hac hu hv

end KsIndex.Trace
