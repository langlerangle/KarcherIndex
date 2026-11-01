module

public import KsIndexLean.HemisphereMixedSmoothDensity
public import KsIndexLean.SphericalChartHomeomorph

@[expose] public section


/-! Intrinsic closed-hemisphere smoothness, expressed by local smooth ambient
extensions on the actual Euclidean sphere. -/
noncomputable section
open Set Filter Topology
open MeasureTheory
open scoped ContDiff
namespace KsIndex.Spherical

lemma contDiffAt_stereoCoord {p : Ambient} (hp : p 2 ≠ 1) :
    ContDiffAt ℝ ∞ stereoCoord p := by
  have he : stereoCoord = fun p : Ambient =>
      ((p 0 : ℂ) + (p 1 : ℂ) * Complex.I) / ((1 - p 2 : ℝ) : ℂ) := by
    funext p
    rw [stereoCoord, ← Complex.re_add_im (Complex.mk (p 0) (p 1))]
  rw [he]
  simp only [div_eq_mul_inv]
  have hcoord (i : Fin 3) : ContDiffAt ℝ ∞ (fun x : Ambient => (x i : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (by fun_prop)
  apply ContDiffAt.mul
  · exact (hcoord 0).add ((hcoord 1).mul contDiffAt_const)
  · apply ContDiffAt.inv
    · exact Complex.ofRealCLM.contDiff.contDiffAt.comp p
        (contDiffAt_const.sub (show ContDiffAt ℝ ∞ (fun x : Ambient => x 2) p by fun_prop))
    · exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hp.symm)

lemma stereoCoord_norm_le_one {p : Sphere} (hp : p.val 2 ≤ 0) :
    ‖stereoCoord p.val‖ ≤ 1 := by
  have hn : p.val 2 ≠ 1 := by linarith
  have he := stereoCoord_norm_sq p hn
  have hd : 0 < 1 - p.val 2 := by linarith
  have hb : (1 + p.val 2) / (1 - p.val 2) ≤ 1 :=
    (div_le_one hd).mpr (by linarith)
  nlinarith [norm_nonneg (stereoCoord p.val)]

/-- Smoothness up to the boundary of the actual lower hemisphere means local
agreement, on its closed side, with an infinitely smooth ambient function. -/
def HasSmoothClosedHemisphereGerm (f : Sphere → ℂ) (p : Sphere) : Prop :=
  ∃ F : Ambient → ℂ, ContDiffAt ℝ ∞ F p.val ∧
    ∀ᶠ q in 𝓝 p, q.val 2 ≤ 0 → f q = F q.val

/-- Interior smoothness and closed-side equatorial coordinate germs give
smooth ambient extensions at every point of the closed lower hemisphere. -/
theorem closedHemisphere_smooth_of_coordinate {G : ℂ → ℂ}
    (hi : ContDiffOn ℝ ∞ G WeakH1.disk)
    (hb : ∀ w : ℂ, ‖w‖ = 1 → ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w ∧
      ∀ᶠ z in 𝓝 w, ‖z‖ ≤ 1 → G z = F z)
    (p : Sphere) (hp : p.val 2 ≤ 0) :
    HasSmoothClosedHemisphereGerm (fun q => G (stereoCoord q.val)) p := by
  have hn : p.val 2 ≠ 1 := by linarith
  have hs := contDiffAt_stereoCoord hn
  rcases lt_or_eq_of_le hp with hneg | heq
  · have hd : stereoCoord p.val ∈ (WeakH1.disk : Set ℂ) := by
      obtain ⟨z, hz, hzp⟩ := (Set.ext_iff.mp sphereChart_disk_eq_lower p).mpr hneg
      rw [← hzp]
      simpa only [sphereChart, stereoCoord_stereoPoint] using hz
    refine ⟨G ∘ stereoCoord,
      (hi.contDiffAt (WeakH1.disk.isOpen.mem_nhds hd)).comp p.val hs, ?_⟩
    exact Eventually.of_forall fun _ _ => rfl
  · have hw : ‖stereoCoord p.val‖ = 1 := by
      have hh := stereoCoord_norm_sq p hn
      rw [heq] at hh
      norm_num only [add_zero, sub_zero, div_one] at hh
      nlinarith [norm_nonneg (stereoCoord p.val)]
    obtain ⟨F, hF, he⟩ := hb _ hw
    refine ⟨F ∘ stereoCoord, hF.comp p.val hs, ?_⟩
    have hc : ContinuousAt (fun q : Sphere => stereoCoord q.val) p :=
      hs.continuousAt.comp continuous_subtype_val.continuousAt
    filter_upwards [hc.tendsto.eventually he] with q hq hlow
    exact hq (stereoCoord_norm_le_one hlow)

/-- The mixed hemisphere weak domain is approximated by actual spherical
functions smooth up to the equator, with pointwise Dirichlet and character
conditions and a uniform puncture-vanishing neighborhood. -/
theorem hemisphereMixed_intrinsic_smooth_approx {k : ℕ} (hk : 1 ≤ k)
    (j : ℕ) (b1 b0 : Bool) (u : hemisphereMixedCharacterDomain k j b1 b0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : hemisphereMixedCharacterDomain k j b1 b0, ∃ f : Sphere → ℂ,
      dist u.val v.val < ε ∧
      hemisphereValue v.val =ᵐ[
        (volume : Measure Ambient).toSphere.restrict {p : Sphere | p.val 2 < 0}] f ∧
      (∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) ∧
      (b1 = false → ∀ z ∈ Surface.arc k 1, f (sphereChart z) = 0) ∧
      (b0 = false → ∀ z ∈ Surface.arc k 0, f (sphereChart z) = 0) ∧
      (∀ p : Sphere, p.val 2 ≤ 0 →
        f (rotateSphere (-(2 * Real.pi) / k) p) = FormIndex.zeta k ^ j * f p) ∧
      (∃ δ > 0, ∀ p : Sphere, p.val 2 ≤ 0 →
        (∃ z ∈ Surface.punctures k, ‖stereoCoord p.val - z‖ < δ) → f p = 0) := by
  obtain ⟨v, G, hv, _hG, hi, he, hb, hp, h1, h0, hc⟩ :=
    hemisphereMixed_smooth_approx hk j b1 b0 u hε
  refine ⟨v, fun p => G (stereoCoord p.val), hv, he,
    closedHemisphere_smooth_of_coordinate hi hb, ?_, ?_, ?_, ?_⟩
  · intro hflag z hz
    simpa only [sphereChart, stereoCoord_stereoPoint] using h1 hflag z hz
  · intro hflag z hz
    simpa only [sphereChart, stereoCoord_stereoPoint] using h0 hflag z hz
  · intro p hlow
    have hn : p.val 2 ≠ 1 := by linarith
    have hrepr : sphereChart (stereoCoord p.val) = p :=
      Subtype.ext (stereoPoint_stereoCoord p hn)
    have hrot := rotateSphere_sphereChart (-(2 * Real.pi) / k) (stereoCoord p.val)
    rw [hrepr] at hrot
    rw [hrot]
    simpa only [sphereChart, stereoCoord_stereoPoint] using
      hc (stereoCoord p.val) (stereoCoord_norm_le_one hlow)
  · obtain ⟨δ, hδ, hp⟩ := hp
    exact ⟨δ, hδ, fun p hlow hz => hp _ (stereoCoord_norm_le_one hlow) hz⟩

end KsIndex.Spherical
