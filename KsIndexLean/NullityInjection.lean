module

public import KsIndexLean.NullitySectors
public import KsIndexLean.WeakH1Integration
public import KsIndexLean.Caccioppoli
public import KsIndexLean.NaturalCoreCharacter

@[expose] public section


/-!
# Injecting bounded Jacobi symmetry sectors into `ComplexH1`

For `k ≥ 2`, restriction to copy `0` defines a complex-linear injection from
`boundedJacobiSector k r s₁ s₀` into `ComplexH1`. These sectors use four copies
(`m = 2`). The map combines the Caccioppoli finite-energy inclusion with
`energySmoothToH1`.

* `sectorRestrict` bundles the linear map; its value agrees almost everywhere on
  the open disk with the original copy-`0` field.
* `sectorRestrict_char_mem` places the image in
  `weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r)` using the rotation
  eigen-equation.
* `sectorRestrict_injective` recovers vanishing on the open disk from almost-everywhere
  vanishing by continuity. The reflection eigen-equations then give vanishing on all
  four copies. Seam continuity, `PunctureZero`, and exterior normalization extend this
  to every point.

The character-membership statement here concerns the weak rotation character.
Trace conditions and membership in the form radical require additional results.
-/

noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.SurfaceForm KsIndex.WeakH1 KsIndex.Trace
open KsIndex.FaithfulInjection Complex MeasureTheory Filter Topology
open KsIndex.FormIndex
open scoped ContDiff

variable {k r s₁ s₀ : ℕ}

/-! ### Membership projections -/

lemma sector_mem_bje {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) : W ∈ BoundedJacobiE k 2 :=
  (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hW).1).1).1

lemma sector_rot_eigen {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) :
    rotE 2 ((rotUnit k : Circle) : ℂ) W = (zeta k ^ r) • W := by
  have h := (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hW).1).1).2
  exact Module.End.mem_eigenspace_iff.mp h

lemma sector_reflOne_eigen {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) :
    reflE 2 1 W = (zeta 2 ^ s₁) • W := by
  have h := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hW).1).2
  exact Module.End.mem_eigenspace_iff.mp h

lemma sector_reflNeg_eigen {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) :
    reflE 2 (-1) W = (zeta 2 ^ s₀) • W := by
  have h := (Submodule.mem_inf.mp hW).2
  exact Module.End.mem_eigenspace_iff.mp h

/-- The curried bounded Jacobi field of a sector element. -/
lemma sector_field_mem {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) :
    (uncurryE 2).symm W ∈ BoundedJacobi k 2 :=
  mem_boundedJacobiE.mp (sector_mem_bje hW)

/-! ### The injection -/

/-- The copy-`0` restriction of a sector element, as a `ComplexH1` element through the
Caccioppoli inclusion and `energySmoothToH1`. -/
def sectorRestrictFun (hk : 2 ≤ k) (W : ↥(boundedJacobiSector k r s₁ s₀)) : ComplexH1 :=
  energySmoothToH1
    ⟨(uncurryE 2).symm W.val,
      bddJacobi_le_energySmooth hk (sector_field_mem W.property)⟩ 0

/-- Almost-everywhere value identity for the finite-energy realization. -/
lemma energySmoothToH1_value {k m : ℕ} (u : ↥(EnergySmooth k m)) (n : ZMod (2 * m)) :
    (valueCLM (energySmoothToH1 u n) : ℂ → ℂ)
      =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)] u.val n :=
  smoothToH1_value_ae _

lemma sectorRestrictFun_value (hk : 2 ≤ k) (W : ↥(boundedJacobiSector k r s₁ s₀)) :
    (valueCLM (sectorRestrictFun hk W) : ℂ → ℂ)
      =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)] (uncurryE 2).symm W.val 0 :=
  energySmoothToH1_value _ 0

lemma sectorRestrictFun_add (hk : 2 ≤ k) (W W' : ↥(boundedJacobiSector k r s₁ s₀)) :
    sectorRestrictFun hk (W + W') = sectorRestrictFun hk W + sectorRestrictFun hk W' := by
  apply valueCLM_injective
  rw [map_add]
  apply Lp.ext
  filter_upwards [sectorRestrictFun_value hk (W + W'), sectorRestrictFun_value hk W,
    sectorRestrictFun_value hk W',
    Lp.coeFn_add (valueCLM (sectorRestrictFun hk W)) (valueCLM (sectorRestrictFun hk W'))]
    with z h3 h1 h2 hadd
  rw [h3, hadd]
  simp only [Pi.add_apply]
  rw [h1, h2]
  simp only [Submodule.coe_add, map_add, Pi.add_apply]

lemma sectorRestrictFun_smul (hk : 2 ≤ k) (c : ℂ) (W : ↥(boundedJacobiSector k r s₁ s₀)) :
    sectorRestrictFun hk (c • W) = c • sectorRestrictFun hk W := by
  apply valueCLM_injective
  rw [map_smul]
  apply Lp.ext
  filter_upwards [sectorRestrictFun_value hk (c • W), sectorRestrictFun_value hk W,
    Lp.coeFn_smul c (valueCLM (sectorRestrictFun hk W))] with z h3 h1 hsm
  rw [h3, hsm]
  simp only [Pi.smul_apply]
  rw [h1]
  simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul]

/-- **The sector injection**, bundled. -/
def sectorRestrict (hk : 2 ≤ k) : ↥(boundedJacobiSector k r s₁ s₀) →ₗ[ℂ] ComplexH1 where
  toFun := sectorRestrictFun hk
  map_add' := sectorRestrictFun_add hk
  map_smul' := sectorRestrictFun_smul hk

/-! ### Weak rotation-character membership -/

/-- The sector eigen-equation, pointwise on the curried field. -/
lemma sector_rot_pointwise {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) (n : ZMod (2 * 2)) (z : ℂ) :
    (uncurryE 2).symm W n (((rotUnit k : Circle) : ℂ) * z) =
      zeta k ^ r * (uncurryE 2).symm W n z := by
  change W (n, ((rotUnit k : Circle) : ℂ) * z) = zeta k ^ r * W (n, z)
  have h := congrFun (sector_rot_eigen hW) (n, z)
  change W (n, ((rotUnit k : Circle) : ℂ) * z) = (zeta k ^ r • W) (n, z) at h
  simpa [Pi.smul_apply, smul_eq_mul] using h

/-- The copy-`0` restriction satisfies the weak rotation character with eigenvalue
`zeta k ^ r`. -/
lemma sectorRestrict_char_mem (hk : 2 ≤ k) (W : ↥(boundedJacobiSector k r s₁ s₀)) :
    sectorRestrictFun hk W ∈
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r) := by
  apply weakCharacter_of_value_eq _ _ _ (sectorRestrictFun_value hk W)
  intro z
  have hpl : planeRotation (-(2 * Real.pi) / k) z = ((rotUnit k : Circle) : ℂ) * z := by
    rw [planeRotation_apply, rotUnit, Circle.coe_exp]
  rw [hpl]
  exact sector_rot_pointwise W.property 0 z

/-! ### Injectivity -/

/-- Every copy of a sector field is a scalar multiple of copy `0`. -/
lemma sector_copies_scalar {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) :
    ∀ n : ZMod (2 * 2), ∃ c : ℂ, ∀ z, (uncurryE 2).symm W n z = c * (uncurryE 2).symm W 0 z := by
  have h1 : ∀ z, W ((1 : ZMod (2 * 2)), z) = zeta 2 ^ s₁ * W (0, z) := by
    intro z
    have h := congrFun (sector_reflOne_eigen hW) ((0 : ZMod (2 * 2)), z)
    change W ((1 : ZMod (2 * 2)) - 0, z) = (zeta 2 ^ s₁ • W) (0, z) at h
    rw [show (1 : ZMod (2 * 2)) - 0 = 1 from by decide] at h
    simpa [Pi.smul_apply, smul_eq_mul] using h
  have h3 : ∀ z, W ((3 : ZMod (2 * 2)), z) = zeta 2 ^ s₀ * W (0, z) := by
    intro z
    have h := congrFun (sector_reflNeg_eigen hW) ((0 : ZMod (2 * 2)), z)
    change W ((-1 : ZMod (2 * 2)) - 0, z) = (zeta 2 ^ s₀ • W) (0, z) at h
    rw [show (-1 : ZMod (2 * 2)) - 0 = 3 from by decide] at h
    simpa [Pi.smul_apply, smul_eq_mul] using h
  have h2 : ∀ z, W ((2 : ZMod (2 * 2)), z) = zeta 2 ^ s₁ * W (3, z) := by
    intro z
    have h := congrFun (sector_reflOne_eigen hW) ((3 : ZMod (2 * 2)), z)
    change W ((1 : ZMod (2 * 2)) - 3, z) = (zeta 2 ^ s₁ • W) (3, z) at h
    rw [show (1 : ZMod (2 * 2)) - 3 = 2 from by decide] at h
    simpa [Pi.smul_apply, smul_eq_mul] using h
  intro n
  rcases (by decide : ∀ x : ZMod (2 * 2), x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) n
    with rfl | rfl | rfl | rfl
  · exact ⟨1, fun z => (one_mul _).symm⟩
  · exact ⟨zeta 2 ^ s₁, fun z => h1 z⟩
  · refine ⟨zeta 2 ^ s₁ * zeta 2 ^ s₀, fun z => ?_⟩
    change W ((2 : ZMod (2 * 2)), z) = zeta 2 ^ s₁ * zeta 2 ^ s₀ * W ((0 : ZMod (2 * 2)), z)
    rw [h2 z, h3 z]
    ring
  · exact ⟨zeta 2 ^ s₀, fun z => h3 z⟩

/-- A bounded Jacobi field vanishing on the open disk of every copy vanishes identically:
the open arcs by seam-glue continuity, the arc endpoints by `PunctureZero`, the exterior by
the normalization. -/
lemma boundedJacobi_zero_of_disk_zero {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : u ∈ BoundedJacobi k m)
    (h0 : ∀ n, ∀ z ∈ Surface.disk, u n z = 0) : u = 0 := by
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, -, -, hpz, hsv⟩ := hu
  have hglue0 : ∀ n' : ZMod (2 * m), ∀ w ∈ seamArc k m n', u n' w = 0 := by
    intro n' w hw
    -- `glue u n'` is continuous at `w`, agrees with `u n'` on the closed disk, and its
    -- open-disk values vanish
    have hcont : ContinuousAt (glue u n') w := (hsm2 n' w hw).continuousAt
    have hw1 : ‖w‖ = 1 := hw.1
    have hzero : glue u n' =ᶠ[𝓝[Surface.disk] w] fun _ => (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [glue]
      rw [ite_eq_left (le_of_lt (mem_disk_iff.mp hz))]
      exact h0 n' z hz
    have htend : Filter.Tendsto (glue u n') (𝓝[Surface.disk] w) (𝓝 (glue u n' w)) :=
      hcont.continuousWithinAt.tendsto
    have hne : (𝓝[Surface.disk] w).NeBot := by
      apply mem_closure_iff_nhdsWithin_neBot.mp
      rw [show (Surface.disk : Set ℂ) = Metric.ball 0 1 from rfl,
        closure_ball (0 : ℂ) one_ne_zero]
      simpa [Metric.mem_closedBall, dist_zero_right] using le_of_eq hw1
    have h0lim : Filter.Tendsto (glue u n') (𝓝[Surface.disk] w) (𝓝 0) :=
      Filter.Tendsto.congr' hzero.symm tendsto_const_nhds
    have := tendsto_nhds_unique htend h0lim
    have hval : glue u n' w = u n' w := by
      simp only [glue]
      rw [ite_eq_left (le_of_eq hw1)]
    rw [← hval, this]
  funext n z
  rcases lt_trichotomy ‖z‖ 1 with h | h | h
  · exact h0 n z (mem_disk_iff.mpr h)
  · -- on the circle: arcs or punctures
    have hpar2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    -- helper: place `z` on the correct adjacent seam and conclude
    have harc : ∀ q : ZMod 2, ((-1 : ℝ) ^ q.val * (z ^ k).re < 0) → u n z = 0 := by
      intro q hq
      rcases hpar2 (parity m (n + 1)) with hp | hp
      all_goals rcases hpar2 (parity m n) with hp' | hp'
      -- `parity (n+1) = parity n + 1`, so the two disagree; the matching seam exists
      · exfalso
        have : parity m (n + 1) = parity m n + 1 := by rw [map_add, map_one]
        rw [hp, hp'] at this
        exact absurd this (by decide)
      · -- parity(n+1) = 0, parity n = 1
        rcases hpar2 q with hq0 | hq1
        · -- q = 0 matches seam `n`
          have hz : z ∈ seamArc k m n := by
            refine ⟨h, ?_⟩
            rw [hp]
            simpa [hq0] using hq
          exact hglue0 n z hz
        · -- q = 1 matches seam `n − 1`
          have hz : z ∈ seamArc k m (n - 1) := by
            refine ⟨h, ?_⟩
            rw [sub_add_cancel, hp']
            simpa [hq1] using hq
          have h0' := hglue0 (n - 1) z hz
          have hs := hsv (n - 1) z hz
          rw [sub_add_cancel] at hs
          rw [hs, h0']
      · -- parity(n+1) = 1, parity n = 0
        rcases hpar2 q with hq0 | hq1
        · have hz : z ∈ seamArc k m (n - 1) := by
            refine ⟨h, ?_⟩
            rw [sub_add_cancel, hp']
            simpa [hq0] using hq
          have h0' := hglue0 (n - 1) z hz
          have hs := hsv (n - 1) z hz
          rw [sub_add_cancel] at hs
          rw [hs, h0']
        · have hz : z ∈ seamArc k m n := by
            refine ⟨h, ?_⟩
            rw [hp]
            simpa [hq1] using hq
          exact hglue0 n z hz
      · exfalso
        have : parity m (n + 1) = parity m n + 1 := by rw [map_add, map_one]
        rw [hp, hp'] at this
        exact absurd this (by decide)
    rcases lt_trichotomy ((z ^ k).re) 0 with hre | hre | hre
    · refine harc 0 ?_
      have hv : ((0 : ZMod 2)).val = 0 := rfl
      rw [hv, pow_zero, one_mul]
      exact hre
    · -- `(z^k).re = 0` on the unit circle ⟹ `z^{2k} = −1`: a puncture
      have hnorm : ‖z ^ k‖ = 1 := by rw [norm_pow, h, one_pow]
      have him : (z ^ k).im ^ 2 = 1 := by
        have h2 : (z ^ k).re ^ 2 + (z ^ k).im ^ 2 = 1 := by
          have := Complex.normSq_eq_norm_sq (z ^ k)
          rw [hnorm] at this
          rw [Complex.normSq_apply] at this
          nlinarith [this]
        rw [hre] at h2
        nlinarith [h2]
      have hp : z ∈ punctures k := by
        change z ^ (2 * k) = -1
        have h2k : z ^ (2 * k) = (z ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
        rw [h2k, pow_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im, hre]
        constructor
        · simp only [Complex.neg_re, Complex.one_re]
          nlinarith [him]
        · simp
      exact hpz n z hp
    · refine harc 1 ?_
      have hv : ((1 : ZMod 2)).val = 1 := rfl
      rw [hv, pow_one, neg_one_mul]
      linarith
  · simpa using hsm3 n z h

/-- A sector field is determined by its copy-`0` open-disk values. -/
lemma sectorRestrict_injective (hk : 2 ≤ k) :
    Function.Injective (sectorRestrict (k := k) (r := r) (s₁ := s₁) (s₀ := s₀) hk) := by
  refine (injective_iff_map_eq_zero _).mpr fun W hW0 => ?_
  have hW0' : sectorRestrictFun hk W = 0 := hW0
  have hval : ((uncurryE 2).symm W.val 0 : ℂ → ℂ)
      =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)] 0 := by
    have h1 := sectorRestrictFun_value hk W
    rw [hW0'] at h1
    refine h1.symm.trans ?_
    rw [map_zero]
    exact Lp.coeFn_zero ℂ 2 _
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, hbd, hjac, hpz, hsv⟩ := sector_field_mem W.property
  have h00 : Set.EqOn ((uncurryE 2).symm W.val 0) 0 Surface.disk :=
    Measure.eqOn_open_of_ae_eq hval Metric.isOpen_ball
      (hsm1 0).continuousOn continuousOn_const
  have h0all : ∀ n, ∀ z ∈ Surface.disk, (uncurryE 2).symm W.val n z = 0 := by
    intro n z hz
    obtain ⟨c, hc⟩ := sector_copies_scalar W.property n
    rw [hc z, h00 hz]
    simp
  have hu0 : (uncurryE 2).symm W.val = 0 :=
    boundedJacobi_zero_of_disk_zero (sector_field_mem W.property) h0all
  have hv0 : W.val = 0 := by
    have h := congrArg (uncurryE 2) hu0
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h
  exact Subtype.ext hv0

end KsIndex.NullityDecomp
