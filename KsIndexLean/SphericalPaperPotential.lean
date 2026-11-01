module

public import KsIndexLean.SphericalQuotientForms
public import KsIndexLean.SphericalWeakJacobi

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1 KsIndex.Trace

/-- The radial expression in the paper's spherical picture. -/
def paperRadialPotential (k : ℕ) (r : ℝ) : ℝ :=
  2 * ((k : ℝ) - 1) ^ 2 * r ^ (2 * k - 4) * (1 + r ^ 2) ^ 2 /
    (r ^ (2 * k - 2) + 1) ^ 2

lemma paperRadialPotential_inv {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr : r ≠ 0) :
    paperRadialPotential k r⁻¹ = paperRadialPotential k r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : 2 * (2 + n) - 4 = 2 * n := by omega
  have h2 : 2 * (2 + n) - 2 = 2 * n + 2 := by omega
  simp only [paperRadialPotential, h1, h2, pow_add, inv_pow]
  field_simp
  ring

lemma sphere_surfacePotential_sigma {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ 0) :
    spherePotential (surfacePotential k) (sphereChart (KsIndex.Bracket.σ z)) =
      spherePotential (surfacePotential k) (sphereChart z) := by
  rw [sphere_surfacePotential_pullback, sphere_surfacePotential_pullback]
  change paperRadialPotential k ‖KsIndex.Bracket.σ z‖ = paperRadialPotential k ‖z‖
  rw [KsIndex.Bracket.norm_σ]
  exact paperRadialPotential_inv hk (norm_ne_zero_iff.mpr hz)

lemma sphereJoinedPotential_paper_pullback {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ 0) :
    sphereJoinedPotential (surfacePotential k) (sphereChart z) = paperRadialPotential k ‖z‖ := by
  unfold sphereJoinedPotential
  split_ifs
  · exact sphere_surfacePotential_pullback k z
  · rw [show reflectSphere (sphereChart z) = sphereChart (KsIndex.Bracket.σ z) from
      southChart_eq_sigma hz, sphere_surfacePotential_sigma hk hz]
    exact sphere_surfacePotential_pullback k z

/-- The global hemispherewise potential agrees with the paper expression away from chart poles,
which is sufficient for all canonical-area form integrals. -/
lemma sphereJoinedPotential_paper_ae {k : ℕ} (hk : 2 ≤ k) :
    sphereJoinedPotential (surfacePotential k) =ᵐ[(volume : Measure Ambient).toSphere]
      spherePotential (surfacePotential k) := by
  have h := (sphere_ae_eq_iff_north
    (fun p => (sphereJoinedPotential (surfacePotential k) p : ℂ))
    (fun p => (spherePotential (surfacePotential k) p : ℂ))).mpr (by
      filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
      rw [sphereJoinedPotential_paper_pullback hk hz, sphere_surfacePotential_pullback]
      rfl)
  filter_upwards [h] with p hp
  exact_mod_cast hp

/-- The quotient Jacobi form with the paper potential, as a canonical spherical integral. -/
theorem sphereChartJacobi_paper_integral {A : Set Circle₁} (hA : IsOpen A)
    {k : ℕ} (hk : 2 ≤ k) (q r : SphereChartSpace A hA) :
    sphereChartJacobi hA (surfacePotential k) q r =
      ∫ p, tangentPair
        (sphereJoinedGradient (chartDiskPair hA q).val.1 (chartDiskPair hA q).val.2 p)
        (sphereJoinedGradient (chartDiskPair hA r).val.1 (chartDiskPair hA r).val.2 p) -
          (spherePotential (surfacePotential k) p : ℂ) *
            (starRingEnd ℂ) (sphereJoinedValue (chartDiskPair hA q).val.1
              (chartDiskPair hA q).val.2 p) *
            sphereJoinedValue (chartDiskPair hA r).val.1 (chartDiskPair hA r).val.2 p
        ∂(volume : Measure Ambient).toSphere := by
  rw [sphereChartJacobi_integral hA (surfacePotential k) k q r,
    canonicalArea_restrict_slitSphere]
  apply integral_congr_ae
  filter_upwards [sphereJoinedPotential_paper_ae hk] with p hp
  simp only [joinedJacobiDensity, hp]

end KsIndex.Spherical
