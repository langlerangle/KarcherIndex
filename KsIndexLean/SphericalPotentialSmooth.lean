module

public import KsIndexLean.SphericalPaperPotential
public import KsIndexLean.SurfacePotentialFacts
public import KsIndexLean.KarcherSourceManifold

@[expose] public section


/-! Smoothness of the paper's spherical potential for `k ≥ 2`, including both poles.
The potential is the coefficient used in the canonical-area forms.
Its two stereographic expressions agree pointwise, not only almost everywhere.
-/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.Spherical
open KsIndex.WeakH1 KsIndex.KarcherData
open scoped KsIndex.KarcherData.ParameterAtlas

/-- The spherical coefficient is smooth in the finite stereographic chart. -/
lemma contDiff_surfacePotential_chart {k : ℕ} (hk : 2 ≤ k) :
    ContDiff ℝ ∞ (fun z : ℂ => Surface.potV k z / stereoAreaDensity z) := by
  apply (Surface.contDiff_potV hk).div
  · have he : stereoAreaDensity = fun z : ℂ =>
        4 / (1 + Complex.normSq z) ^ 2 := by
      funext z
      rw [stereoAreaDensity_eq, Complex.sq_norm]
    rw [he]
    exact contDiff_const.div ((contDiff_const.add Surface.contDiff_normSq).pow 2)
      (fun z => by have := Complex.normSq_nonneg z; positivity)
  · exact fun z => ne_of_gt (stereoAreaDensity_pos z)

/-- Totalization of the stereographic coordinate at the north pole is zero. -/
lemma stereoCoord_infinity_zero : stereoCoord (infinitySphereChart 0).val = 0 := by
  simp [stereoCoord, infinitySphereChart, southChart, reflectSphere, reflectAmbient,
    sphereChart, stereoPoint]

/-- The pole value is the same as the value at the finite-chart origin. -/
lemma spherePotential_infinity_zero (k : ℕ) :
    spherePotential (surfacePotential k) (infinitySphereChart 0) =
      spherePotential (surfacePotential k) (sphereChart 0) := by
  simp only [spherePotential, stereoCoord_infinity_zero]
  rw [show stereoCoord (sphereChart 0).val = 0 from stereoCoord_stereoPoint 0]

/-- In the holomorphic infinity chart the coefficient has the same radial formula. -/
lemma spherePotential_infinity_pullback {k : ℕ} (hk : 2 ≤ k) (z : ℂ) :
    spherePotential (surfacePotential k) (infinitySphereChart z) =
      spherePotential (surfacePotential k) (sphereChart z) := by
  by_cases hz : z = 0
  · subst z; exact spherePotential_infinity_zero k
  rw [infinitySphereChart_overlap hz, sphere_surfacePotential_pullback,
    sphere_surfacePotential_pullback]
  change paperRadialPotential k ‖z⁻¹‖ = paperRadialPotential k ‖z‖
  rw [norm_inv]
  exact paperRadialPotential_inv hk (norm_ne_zero_iff.mpr hz)

/-- The two regular poles have value two for k=2 and zero for k>2. -/
lemma spherePotential_poles {k : ℕ} (hk : 2 ≤ k) :
    spherePotential (surfacePotential k) (sphereChart 0) = (if k = 2 then 2 else 0) ∧
    spherePotential (surfacePotential k) (infinitySphereChart 0) =
      (if k = 2 then 2 else 0) := by
  rw [spherePotential_infinity_zero]
  suffices h : spherePotential (surfacePotential k) (sphereChart 0) =
      (if k = 2 then 2 else 0) from ⟨h, h⟩
  rw [sphere_surfacePotential_pullback]
  by_cases h : k = 2
  · subst k; norm_num
  · have he : 2 * k - 4 ≠ 0 := by omega
    simp [h, he]

/-- The paper's potential is smooth on the entire sphere in its finite/infinity atlas. -/
theorem spherePotential_contMDiff {k : ℕ} (hk : 2 ≤ k) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (spherePotential (surfacePotential k)) := by
  have hfin : ContDiff ℝ ∞
      (spherePotential (surfacePotential k) ∘ sphereChart) := by
    have he : spherePotential (surfacePotential k) ∘ sphereChart =
        fun z => Surface.potV k z / stereoAreaDensity z := by
      funext z
      exact spherePotential_pullback (surfacePotential k) z
    rw [he]
    exact contDiff_surfacePotential_chart hk
  have hinf : ContDiff ℝ ∞
      (spherePotential (surfacePotential k) ∘ infinitySphereChart) := by
    have he : spherePotential (surfacePotential k) ∘ infinitySphereChart =
        spherePotential (surfacePotential k) ∘ sphereChart := by
      funext z; exact spherePotential_infinity_pullback hk z
    rw [he]; exact hfin
  intro p
  rw [contMDiffAt_iff_source]
  simp only [mfld_simps]
  change ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
    (spherePotential (surfacePotential k) ∘ (chartAt ℂ p).symm)
    Set.univ (chartAt ℂ p p)
  rw [contMDiffWithinAt_univ]
  classical
  by_cases hp : p ∈ ParameterAtlas.finite.source
  · have he : chartAt ℂ p = ParameterAtlas.finite := ite_eq_left hp
    rw [he]
    exact hfin.contMDiff _
  · have he : chartAt ℂ p = ParameterAtlas.infinity := ite_eq_right hp
    rw [he]
    exact hinf.contMDiff _

/-- The hemispherewise coefficient used by the weak forms equals the smooth
spherical potential at every point, including the poles and equator. -/
theorem sphereJoinedPotential_eq_paper {k : ℕ} (hk : 2 ≤ k) :
    sphereJoinedPotential (surfacePotential k) = spherePotential (surfacePotential k) := by
  funext p
  unfold sphereJoinedPotential
  split_ifs with hp
  · rfl
  · have hpos : 0 < p.val 2 := lt_of_not_ge hp
    by_cases hn : p.val 2 = 1
    · rw [north_unique p hn]
      change spherePotential (surfacePotential k) (reflectSphere (infinitySphereChart 0)) = _
      have he : reflectSphere (infinitySphereChart 0) = sphereChart 0 := by
        simp only [infinitySphereChart, map_zero, southChart]
        exact reflectSphere_involutive (sphereChart 0)
      rw [he, spherePotential_infinity_zero]
    · let z := stereoCoord p.val
      have hpz : sphereChart z = p := Subtype.ext (stereoPoint_stereoCoord p hn)
      have hz : z ≠ 0 := by
        intro he
        have hh := congrArg (fun q : Sphere => q.val 2) hpz
        rw [he] at hh
        change (‖(0 : ℂ)‖ ^ 2 - 1) / (1 + ‖(0 : ℂ)‖ ^ 2) = p.val 2 at hh
        norm_num at hh
        linarith
      rw [← hpz]
      change spherePotential (surfacePotential k) (southChart z) = _
      rw [southChart_eq_sigma hz]
      exact sphere_surfacePotential_sigma hk hz

/-- The coefficient in the joined integral is itself globally smooth. -/
theorem sphereJoinedPotential_contMDiff {k : ℕ} (hk : 2 ≤ k) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (sphereJoinedPotential (surfacePotential k)) := by
  rw [sphereJoinedPotential_eq_paper hk]
  exact spherePotential_contMDiff hk

end KsIndex.Spherical
