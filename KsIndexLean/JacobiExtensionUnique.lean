module

public import KsIndexLean.JacobiExtensionForm
public import KsIndexLean.GeneralNeumannInjectivity

@[expose] public section


/-! Uniqueness with the paper's zero mean normal-flux normalization.
The normalization tests only constant boundary traces, not all weak H1 tests. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Radial
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- A weak Jacobi field with zero trace and zero mean normal flux vanishes. -/
theorem normalizedJacobi_zero_of_trace_zero {k : ℕ} (hk : 2 ≤ k)
    (u : ComplexH1) (ht : diskTraceCLM u = 0)
    (hweak : ∀ v ∈ zeroTraceDomain Set.univ,
      weakJacobi (surfacePotential k) u v = 0)
    (hnorm : ∀ v : ComplexH1, (∃ c : ℂ, diskTraceCLM v = c • circleOneL2) →
      weakJacobi (surfacePotential k) u v = 0) : u = 0 := by
  obtain ⟨c, hc⟩ := generalDirichlet_kernel_span hk u
    ((mem_fullZeroTrace_iff u).mpr ht) hweak
  let v : ComplexH1 := globalSmoothH1 (fun _ : ℂ => (1 : ℂ)) contDiff_const
  have hv : diskTraceCLM v = circleOneL2 := by
    apply Lp.ext
    filter_upwards [globalSmoothH1_trace (fun _ : ℂ => (1 : ℂ)) contDiff_const,
      MemLp.coeFn_toLp (memLp_const (1 : ℂ))] with w hw ho
    exact hw.trans ho.symm
  have hi : (∫ w : Circle₁, (circleOneL2 : Circle₁ → ℂ) w ∂circleMeasure) =
      (2 * Real.pi : ℂ) := by
    calc
      _ = ∫ _ : Circle₁, (1 : ℂ) ∂circleMeasure := by
        apply integral_congr_ae
        exact MemLp.coeFn_toLp (memLp_const (1 : ℂ))
      _ = _ := by simp [integral_const, measureReal_def, circleMeasure_univ, Real.pi_pos.le]
  have hn : weakJacobi (surfacePotential k) (radialDirichletH1 hk) v ≠ 0 := by
    rw [radialDirichlet_weak_green hk, hv, hi]
    apply mul_ne_zero
    · simp only [neg_ne_zero, Complex.ofReal_ne_zero]
      exact pow_ne_zero 2 (ne_of_gt (kap_pos hk))
    · exact_mod_cast ne_of_gt Real.two_pi_pos
  have he := hnorm v ⟨1, by simpa using hv⟩
  rw [hc, weakJacobi_smul_left] at he
  have hc0 : c = 0 := (starRingEnd ℂ).injective
    (((mul_eq_zero.mp he).resolve_right hn).trans (map_zero (starRingEnd ℂ)).symm)
  rw [hc, hc0, zero_smul]

/-- Constant boundary data have no nonzero Fourier coefficients. -/
lemma circleFourierCoeff_const_nonzero (c : ℂ) {n : ℤ} (hn : n ≠ 0) :
    circleFourierCoeff (fun _ => c) n = 0 := by
  rw [← fourierCoeff_geometric_pullback]
  have he : (fun _ : AddCircle (2 * Real.pi) => c) =
      fun x => c * fourier (0 : ℤ) x := by ext x; simp
  rw [he, fourierCoeff.const_mul, fourierCoeff_fourier]
  simp [hn]

/-- The Jacobi extension has zero weak flux against every constant-trace test. -/
lemma jacobiExtensionCLM_constantTrace {k : ℕ} (hk : 2 ≤ k)
    (f : KsIndex.CircleSobolev.dotted (1 / 2 : ℝ)) (v : ComplexH1)
    (hv : ∃ c : ℂ, diskTraceCLM v = c • circleOneL2) :
    weakJacobi (surfacePotential k) (jacobiExtensionCLM hk f) v = 0 := by
  obtain ⟨c, hc⟩ := hv
  change weakJacobi (surfacePotential k) (jacobiExtensionH1 hk f.val) v = 0
  rw [jacobiExtensionH1_weak_pairing]
  have he : (diskTraceCLM v : Circle₁ → ℂ) =ᵐ[circleMeasure] (fun _ => c) := by
    rw [hc]
    filter_upwards [Lp.coeFn_smul c circleOneL2,
      MemLp.coeFn_toLp (memLp_const (1 : ℂ))] with w hw ho
    rw [hw]
    change c * circleOneL2 w = c
    change circleOneL2 w = 1 at ho
    rw [ho, mul_one]
  have hz (n : KsIndex.DtNCircle.NZ) : circleFourierCoeff (diskTraceCLM v) n = 0 := by
    rw [congrFun (circleFourierCoeff_congr_ae he) n]
    exact circleFourierCoeff_const_nonzero c n.property
  simp only [hz, mul_zero, tsum_zero]

/-- Two normalized weak Jacobi fields with the same trace coincide. -/
theorem normalizedJacobi_unique {k : ℕ} (hk : 2 ≤ k) (u v : ComplexH1)
    (ht : diskTraceCLM u = diskTraceCLM v)
    (hu : ∀ w ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u w = 0)
    (hv : ∀ w ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) v w = 0)
    (hnu : ∀ w : ComplexH1, (∃ c : ℂ, diskTraceCLM w = c • circleOneL2) →
      weakJacobi (surfacePotential k) u w = 0)
    (hnv : ∀ w : ComplexH1, (∃ c : ℂ, diskTraceCLM w = c • circleOneL2) →
      weakJacobi (surfacePotential k) v w = 0) : u = v := by
  apply sub_eq_zero.mp
  apply normalizedJacobi_zero_of_trace_zero hk (u - v)
  · rw [map_sub, ht, sub_self]
  · intro w hw
    rw [sub_eq_add_neg, ← neg_one_smul ℂ v, weakJacobi_add_left, weakJacobi_smul_left,
      hu w hw, hv w hw, mul_zero, add_zero]
  · intro w hw
    rw [sub_eq_add_neg, ← neg_one_smul ℂ v, weakJacobi_add_left, weakJacobi_smul_left,
      hnu w hw, hnv w hw, mul_zero, add_zero]

/-- Uniqueness of the paper's Jacobi extension under the trace and mean-flux conditions. -/
theorem eq_jacobiExtensionCLM_of_normalized {k : ℕ} (hk : 2 ≤ k)
    (f : KsIndex.CircleSobolev.dotted (1 / 2 : ℝ)) (u : ComplexH1)
    (ht : diskTraceCLM u = diskTraceCLM (jacobiExtensionCLM hk f))
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v = 0)
    (hn : ∀ v : ComplexH1, (∃ c : ℂ, diskTraceCLM v = c • circleOneL2) →
      weakJacobi (surfacePotential k) u v = 0) : u = jacobiExtensionCLM hk f :=
  normalizedJacobi_unique hk u _ ht hu (jacobiExtensionCLM_weak_zeroTrace hk f)
    hn (jacobiExtensionCLM_constantTrace hk f)

/-- The half-order trace formulation of normalized Jacobi extension uniqueness. -/
theorem eq_jacobiExtensionCLM_of_halfTrace {k : ℕ} (hk : 2 ≤ k)
    (f : KsIndex.CircleSobolev.dotted (1 / 2 : ℝ)) (u : ComplexH1)
    (ht : halfDiskTraceCLM u = f.val)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v = 0)
    (hn : ∀ v : ComplexH1, (∃ c : ℂ, diskTraceCLM v = c • circleOneL2) →
      weakJacobi (surfacePotential k) u v = 0) : u = jacobiExtensionCLM hk f := by
  apply eq_jacobiExtensionCLM_of_normalized hk f u _ hu hn
  rw [← toL2_comp_halfDiskTraceCLM]
  simp only [ContinuousLinearMap.comp_apply, ht, jacobiExtensionCLM_halfTrace]

end KsIndex.Trace
