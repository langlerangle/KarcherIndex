module

/-
# Interior weak equations from the slit pair radical

For a vector in `paperSlitCharacterDomain α j` whose `Bpair` pairing with
every vector in that domain vanishes, this file proves the interior weak
Jacobi equation for each hemisphere component, with potential
`surfacePotential 3`.

The complex span of embedded real smooth tests compactly supported in the
open disk is invariant under disk rotations and has zero boundary trace.
A vector in this span with the required cubic rotation character can be
injected into either component of the slit pair domain: its zero trace
satisfies both transmission conditions. Pair-radical vanishing therefore
implies vanishing against these character tests.

`surfaceJacobi_cubic_tests_suffice` extends this conclusion to every
embedded interior test by character averaging. The final theorems split
the complex pairing into the two real weak equations for the real and
imaginary Sobolev components. The argument establishes interior weak
equations; boundary regularity is handled separately.
-/
public import KsIndexLean.PaperSlitIndexPIN
public import KsIndexLean.CubicCharacterTests
public import KsIndexLean.DiskTraceAgreement
public import KsIndexLean.PunctureRemoval
public import KsIndexLean.PaperSlitLocalTests

@[expose] public section


noncomputable section
open MeasureTheory TopologicalSpace Topology
open scoped ContDiff
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1 KsIndex.PaperSlitAdapter

/-! ### Rotation equivariance of the embedding -/

/-- Smoothness survives precomposition with the plane rotation. -/
lemma contDiff_comp_planeRotation (θ : ℝ) {ψ : ℂ → ℝ}
    (hψs : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => ψ (planeRotation θ z) := by
  have h : (fun z : ℂ => ψ (planeRotation θ z))
      = fun z => ψ ((Circle.exp θ : ℂ) * z) := by
    funext z
    rw [planeRotation_apply, Circle.coe_exp]
  rw [h]
  exact hψs.comp (contDiff_const.mul contDiff_id)

/-- Compact support survives precomposition with the plane rotation. -/
lemma hasCompactSupport_comp_planeRotation (θ : ℝ) {ψ : ℂ → ℝ}
    (hψc : HasCompactSupport ψ) :
    HasCompactSupport fun z => ψ (planeRotation θ z) :=
  hψc.comp_homeomorph (planeRotation θ).toHomeomorph

/-- **Rotation equivariance of the embedding**: rotating the embedded test is
embedding the rotated test (`valueCLM`-injectivity + the value covariances). -/
lemma diskRotation_realTestH1 (θ : ℝ) (ψ : ℂ → ℝ)
    (hψs : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    diskRotation θ (realTestH1 ψ hψs hψc)
      = realTestH1 (fun z => ψ (planeRotation θ z))
          (contDiff_comp_planeRotation θ hψs)
          (hasCompactSupport_comp_planeRotation θ hψc) := by
  apply valueCLM_injective
  unfold realTestH1
  have hL : valueCLM (diskRotation θ (smoothToH1 (realTestData ψ hψs hψc)))
      = diskLpRotation θ (valueCLM (smoothToH1 (realTestData ψ hψs hψc))) :=
    diskH1Rotation_value θ _
  rw [hL]
  apply MeasureTheory.Lp.ext
  have h1 := diskLpRotation_coe_ae θ (valueCLM (smoothToH1 (realTestData ψ hψs hψc)))
  have h2 := smoothToH1_value_ae (realTestData ψ hψs hψc)
  have h3 := (measurePreserving_planeRotation_disk θ).quasiMeasurePreserving.ae_eq_comp h2
  have h4 := smoothToH1_value_ae (realTestData (fun z => ψ (planeRotation θ z))
    (contDiff_comp_planeRotation θ hψs)
    (hasCompactSupport_comp_planeRotation θ hψc))
  filter_upwards [h1, h3, h4] with x hx1 hx3 hx4
  simp only [Function.comp_apply] at hx1 hx3 ⊢
  rw [hx1, hx3, hx4]
  rfl

/-! ### Pair injection of trace-zero character vectors -/

/-- The full rotation is the identity on the carrier. -/
lemma diskRotation_neg_two_pi (v : ComplexH1) :
    diskRotation (-(2 * Real.pi)) v = v := by
  apply valueCLM_injective
  have hL : valueCLM (diskRotation (-(2 * Real.pi)) v)
      = diskLpRotation (-(2 * Real.pi)) (valueCLM v) := diskH1Rotation_value _ _
  rw [hL]
  apply MeasureTheory.Lp.ext
  filter_upwards [diskLpRotation_coe_ae (-(2 * Real.pi)) (valueCLM v)] with x hx
  rw [hx]
  simp only [Function.comp_apply]
  congr 1
  rw [planeRotation_apply]
  rw [show ((-(2 * Real.pi) : ℝ) : ℂ) * Complex.I
      = -(2 * Real.pi * Complex.I) by push_cast; ring]
  rw [Complex.exp_neg, Complex.exp_two_pi_mul_I]
  simp

/-- Rotated support stays in the disk (the rotation is a norm isometry
fixing the origin). -/
lemma tsupport_comp_planeRotation_subset (θ : ℝ) {ψ : ℂ → ℝ}
    (hsupp : tsupport ψ ⊆ (disk : Set ℂ)) :
    tsupport (fun z => ψ (planeRotation θ z)) ⊆ (disk : Set ℂ) := by
  have heq : tsupport (fun z => ψ (planeRotation θ z))
      = planeRotation θ ⁻¹' tsupport ψ := by
    unfold tsupport
    have hsup : (Function.support fun z => ψ (planeRotation θ z))
        = planeRotation θ ⁻¹' Function.support ψ := rfl
    rw [hsup]
    exact ((planeRotation θ).toHomeomorph.preimage_closure _).symm
  rw [heq]
  intro z hz
  have h1 : planeRotation θ z ∈ Metric.ball (0 : ℂ) 1 := hsupp hz
  have h2 : ‖planeRotation θ z‖ = ‖z‖ := (planeRotation θ).norm_map z
  change z ∈ Metric.ball (0 : ℂ) 1
  rw [Metric.mem_ball, dist_zero_right] at h1 ⊢
  rw [h2] at h1
  exact h1

/-- A trace-zero character vector injects into the slit character domain as the
second (lower-hemisphere) component. -/
lemma pair_injection_snd_mem (α : ℝ) (j : ℕ) {S : ComplexH1}
    (hS : diskTraceCLM S = 0)
    (hrot : S ∈ weakCharacterDomain (-(2 * Real.pi) / 3)
      (KsIndex.FormIndex.zeta 3 ^ j)) :
    ((0, S) : DiskPairH1) ∈ paperSlitCharacterDomain α j := by
  have harcS : ∀ A : Set Circle₁, arcTrace A S = 0 := by
    intro A
    unfold arcTrace
    rw [ContinuousLinearMap.comp_apply, hS, map_zero]
  have hz1 : ∀ A : Set Circle₁,
      ((0, S) : DiskPairH1).1 ∈ zeroTraceDomain A := fun A => map_zero _
  have hz2 : ∀ A : Set Circle₁,
      ((0, S) : DiskPairH1).2 ∈ zeroTraceDomain A := fun A => harcS A
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [paperSlitDomain]
    exact Submodule.mem_inf.mpr
      ⟨mem_transmission_of_zero _ (hz1 _) (hz2 _),
        mem_transmission_of_zero _ (hz1 _) (hz2 _)⟩
  · exact Submodule.mem_inf.mpr
      ⟨Submodule.mem_comap.mpr (Submodule.zero_mem _),
        Submodule.mem_comap.mpr hrot⟩

/-- The pair form against an injected lower vector is the single-hemisphere
pairing. -/
lemma Bpair_injection_snd {α : ℝ} {j : ℕ} (u : paperSlitCharacterDomain α j)
    {S : ComplexH1} (hmem : ((0, S) : DiskPairH1) ∈ paperSlitCharacterDomain α j) :
    Bpair u ⟨(0, S), hmem⟩ = weakJacobi (surfacePotential 3) u.val.2 S := by
  change weakJacobi (surfacePotential 3) u.val.1 0
      + weakJacobi (surfacePotential 3) u.val.2 S = _
  have h0 : weakJacobi (surfacePotential 3) u.val.1 0 = 0 := by
    simp [weakJacobi, dirichlet, potential]
  rw [h0, zero_add]

/-! ### Interior character averaging -/

/-- The span of embedded interior tests: the rotation-invariant, trace-zero
test domain of the averaging argument. -/
def interiorTestSpan : Submodule ℂ ComplexH1 :=
  Submodule.span ℂ {v | ∃ (ψ : ℂ → ℝ) (hψs : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ), tsupport ψ ⊆ (disk : Set ℂ)
      ∧ v = realTestH1 ψ hψs hψc}

lemma interiorTestSpan_trace_zero :
    ∀ v ∈ interiorTestSpan, diskTraceCLM v = 0 := by
  have hle : interiorTestSpan
      ≤ LinearMap.ker diskTraceCLM.toLinearMap := by
    rw [interiorTestSpan, Submodule.span_le]
    rintro v ⟨ψ, hψs, hψc, hsupp, rfl⟩
    exact LinearMap.mem_ker.mpr (diskTrace_realTestH1 ψ hψs hψc hsupp)
  exact fun v hv => LinearMap.mem_ker.mp (hle hv)

lemma interiorTestSpan_rot_stable (θ : ℝ) :
    ∀ v ∈ interiorTestSpan, diskRotation θ v ∈ interiorTestSpan := by
  have hmap : Submodule.map (diskRotation θ).toLinearMap interiorTestSpan
      ≤ interiorTestSpan := by
    rw [interiorTestSpan, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro w ⟨v, ⟨ψ, hψs, hψc, hsupp, rfl⟩, rfl⟩
    apply Submodule.subset_span
    exact ⟨fun z => ψ (planeRotation θ z), contDiff_comp_planeRotation θ hψs,
      hasCompactSupport_comp_planeRotation θ hψc,
      tsupport_comp_planeRotation_subset θ hsupp,
      diskRotation_realTestH1 θ ψ hψs hψc⟩
  exact fun v hv => hmap ⟨v, hv, rfl⟩

/-- The lower hemisphere of a pair-radical vector satisfies the weak Jacobi
equation against every embedded real smooth test compactly supported in the disk. -/
theorem pair_radical_interior_snd {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    (ψ : ℂ → ℝ) (hψs : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ (disk : Set ℂ)) :
    weakJacobi (surfacePotential 3) u.val.2 (realTestH1 ψ hψs hψc) = 0 := by
  have hc3 : (KsIndex.FormIndex.zeta 3 ^ j) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, KsIndex.FormIndex.zeta_pow_N (by norm_num),
      one_pow]
  have hcn : ‖KsIndex.FormIndex.zeta 3 ^ j‖ = 1 := by
    have h1 : ‖KsIndex.FormIndex.zeta 3 ^ j‖ ^ 3 = 1 := by
      rw [← norm_pow, hc3, norm_one]
    nlinarith [norm_nonneg (KsIndex.FormIndex.zeta 3 ^ j), sq_nonneg
      (‖KsIndex.FormIndex.zeta 3 ^ j‖ - 1), sq_nonneg
      (‖KsIndex.FormIndex.zeta 3 ^ j‖ + 1)]
  have hT : ∀ v : ComplexH1, diskRotation (-(2 * Real.pi) / 3)
      (diskRotation (-(2 * Real.pi) / 3)
        (diskRotation (-(2 * Real.pi) / 3) v)) = v := by
    intro v
    rw [← diskRotation_add, ← diskRotation_add,
      show -(2 * Real.pi) / 3 + -(2 * Real.pi) / 3 + -(2 * Real.pi) / 3
        = -(2 * Real.pi) by ring]
    exact diskRotation_neg_two_pi v
  have hu2 : diskRotation (-(2 * Real.pi) / 3) u.val.2
      = (KsIndex.FormIndex.zeta 3 ^ j) • u.val.2 := by
    have hmem := (Submodule.mem_inf.mp
      ((Submodule.mem_inf.mp u.property).2)).2
    exact (mem_weakCharacterDomain _ _ _).mp (Submodule.mem_comap.mp hmem)
  have hzero : ∀ v ∈ interiorTestSpan,
      diskRotation (-(2 * Real.pi) / 3) v
        = (KsIndex.FormIndex.zeta 3 ^ j) • v →
      weakJacobi (surfacePotential 3) u.val.2 v = 0 := by
    intro v hv hveig
    have hvchar : v ∈ weakCharacterDomain (-(2 * Real.pi) / 3)
        (KsIndex.FormIndex.zeta 3 ^ j) :=
      (mem_weakCharacterDomain _ _ _).mpr hveig
    have hmem := pair_injection_snd_mem α j
      (interiorTestSpan_trace_zero v hv) hvchar
    have h := hrad ⟨(0, v), hmem⟩
    rw [Bpair_injection_snd u hmem] at h
    exact h
  exact surfaceJacobi_cubic_tests_suffice 3 (-(2 * Real.pi) / 3)
    (KsIndex.FormIndex.zeta 3 ^ j) hc3 hcn hT interiorTestSpan
    (interiorTestSpan_rot_stable _) u.val.2 hu2 hzero
    (realTestH1 ψ hψs hψc)
    (Submodule.subset_span ⟨ψ, hψs, hψc, hsupp, rfl⟩)

/-! ### The upper hemisphere -/

/-- The upper-component injection. -/
lemma pair_injection_fst_mem (α : ℝ) (j : ℕ) {S : ComplexH1}
    (hS : diskTraceCLM S = 0)
    (hrot : S ∈ weakCharacterDomain (-(2 * Real.pi) / 3)
      (KsIndex.FormIndex.zeta 3 ^ j)) :
    ((S, 0) : DiskPairH1) ∈ paperSlitCharacterDomain α j := by
  have harcS : ∀ A : Set Circle₁, arcTrace A S = 0 := by
    intro A
    unfold arcTrace
    rw [ContinuousLinearMap.comp_apply, hS, map_zero]
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [paperSlitDomain]
    exact Submodule.mem_inf.mpr
      ⟨mem_transmission_of_zero _ (harcS _) (map_zero _),
        mem_transmission_of_zero _ (harcS _) (map_zero _)⟩
  · exact Submodule.mem_inf.mpr
      ⟨Submodule.mem_comap.mpr hrot,
        Submodule.mem_comap.mpr (Submodule.zero_mem _)⟩

lemma Bpair_injection_fst {α : ℝ} {j : ℕ} (u : paperSlitCharacterDomain α j)
    {S : ComplexH1} (hmem : ((S, 0) : DiskPairH1) ∈ paperSlitCharacterDomain α j) :
    Bpair u ⟨(S, 0), hmem⟩ = weakJacobi (surfacePotential 3) u.val.1 S := by
  change weakJacobi (surfacePotential 3) u.val.1 S
      + weakJacobi (surfacePotential 3) u.val.2 0 = _
  have h0 : weakJacobi (surfacePotential 3) u.val.2 0 = 0 := by
    simp [weakJacobi, dirichlet, potential]
  rw [h0, add_zero]

/-- The upper hemisphere satisfies the same interior weak equation. -/
theorem pair_radical_interior_fst {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    (ψ : ℂ → ℝ) (hψs : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ (disk : Set ℂ)) :
    weakJacobi (surfacePotential 3) u.val.1 (realTestH1 ψ hψs hψc) = 0 := by
  have hc3 : (KsIndex.FormIndex.zeta 3 ^ j) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, KsIndex.FormIndex.zeta_pow_N (by norm_num),
      one_pow]
  have hcn : ‖KsIndex.FormIndex.zeta 3 ^ j‖ = 1 := by
    have h1 : ‖KsIndex.FormIndex.zeta 3 ^ j‖ ^ 3 = 1 := by
      rw [← norm_pow, hc3, norm_one]
    nlinarith [norm_nonneg (KsIndex.FormIndex.zeta 3 ^ j), sq_nonneg
      (‖KsIndex.FormIndex.zeta 3 ^ j‖ - 1), sq_nonneg
      (‖KsIndex.FormIndex.zeta 3 ^ j‖ + 1)]
  have hT : ∀ v : ComplexH1, diskRotation (-(2 * Real.pi) / 3)
      (diskRotation (-(2 * Real.pi) / 3)
        (diskRotation (-(2 * Real.pi) / 3) v)) = v := by
    intro v
    rw [← diskRotation_add, ← diskRotation_add,
      show -(2 * Real.pi) / 3 + -(2 * Real.pi) / 3 + -(2 * Real.pi) / 3
        = -(2 * Real.pi) by ring]
    exact diskRotation_neg_two_pi v
  have hu1 : diskRotation (-(2 * Real.pi) / 3) u.val.1
      = (KsIndex.FormIndex.zeta 3 ^ j) • u.val.1 := by
    have hmem := (Submodule.mem_inf.mp
      ((Submodule.mem_inf.mp u.property).2)).1
    exact (mem_weakCharacterDomain _ _ _).mp (Submodule.mem_comap.mp hmem)
  have hzero : ∀ v ∈ interiorTestSpan,
      diskRotation (-(2 * Real.pi) / 3) v
        = (KsIndex.FormIndex.zeta 3 ^ j) • v →
      weakJacobi (surfacePotential 3) u.val.1 v = 0 := by
    intro v hv hveig
    have hvchar : v ∈ weakCharacterDomain (-(2 * Real.pi) / 3)
        (KsIndex.FormIndex.zeta 3 ^ j) :=
      (mem_weakCharacterDomain _ _ _).mpr hveig
    have hmem := pair_injection_fst_mem α j
      (interiorTestSpan_trace_zero v hv) hvchar
    have h := hrad ⟨(v, 0), hmem⟩
    rw [Bpair_injection_fst u hmem] at h
    exact h
  exact surfaceJacobi_cubic_tests_suffice 3 (-(2 * Real.pi) / 3)
    (KsIndex.FormIndex.zeta 3 ^ j) hc3 hcn hT interiorTestSpan
    (interiorTestSpan_rot_stable _) u.val.1 hu1 hzero
    (realTestH1 ψ hψs hψc)
    (Submodule.subset_span ⟨ψ, hψs, hψc, hsupp, rfl⟩)

/-! ### Real and imaginary weak equations

The complex pairing against an embedded real test splits as
`(re-identity) − i·(im-identity)`. Its vanishing gives the weak-solution
identities for both Sobolev components of the hemisphere, using
`RealH1 = W1p volume disk 2`. -/

theorem pair_radical_D1_snd {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    (φ : ℂ → ℝ) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ (disk : Set ℂ)) :
    (∫ x in (disk : Set ℂ),
        ((TauCeti.W1p.gradient (rePart u.val.2) x).re * fderiv ℝ φ x 1
          + (TauCeti.W1p.gradient (rePart u.val.2) x).im * fderiv ℝ φ x Complex.I
          - Surface.potV 3 x * TauCeti.W1p.value (rePart u.val.2) x * φ x)) = 0
    ∧ (∫ x in (disk : Set ℂ),
        ((TauCeti.W1p.gradient (imPart u.val.2) x).re * fderiv ℝ φ x 1
          + (TauCeti.W1p.gradient (imPart u.val.2) x).im * fderiv ℝ φ x Complex.I
          - Surface.potV 3 x * TauCeti.W1p.value (imPart u.val.2) x * φ x)) = 0 :=
  realTest_pairing_zero_components 3 u.val.2 φ hφs hφc
    (pair_radical_interior_snd u hrad φ hφs hφc hsupp)

/-- The upper component satisfies both real weak equations. -/
theorem pair_radical_D1_fst {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    (φ : ℂ → ℝ) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ (disk : Set ℂ)) :
    (∫ x in (disk : Set ℂ),
        ((TauCeti.W1p.gradient (rePart u.val.1) x).re * fderiv ℝ φ x 1
          + (TauCeti.W1p.gradient (rePart u.val.1) x).im * fderiv ℝ φ x Complex.I
          - Surface.potV 3 x * TauCeti.W1p.value (rePart u.val.1) x * φ x)) = 0
    ∧ (∫ x in (disk : Set ℂ),
        ((TauCeti.W1p.gradient (imPart u.val.1) x).re * fderiv ℝ φ x 1
          + (TauCeti.W1p.gradient (imPart u.val.1) x).im * fderiv ℝ φ x Complex.I
          - Surface.potV 3 x * TauCeti.W1p.value (imPart u.val.1) x * φ x)) = 0 :=
  realTest_pairing_zero_components 3 u.val.1 φ hφs hφc
    (pair_radical_interior_fst u hrad φ hφs hφc hsupp)

end KsIndex.PaperSlitTransport
