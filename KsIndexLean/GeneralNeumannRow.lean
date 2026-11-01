module

public import KsIndexLean.GeneralNeumannInjectivity
public import KsIndexLean.JacobiExtensionForm
public import KsIndexLean.DtnBridge
public import KsIndexLean.ModeWitness
public import KsIndexLean.DtNCircle
public import KsIndexLean.RadialMode

@[expose] public section


/-!
# The full Neumann kernel has dimension at most two

The half-order trace maps the full weak-kernel radical into the radical of
the Dirichlet-to-Neumann form. The radial witness's constant flux forces the
trace mean to vanish, and `jacobiExtensionH1_weak_pairing`, the kernel property
and conjugation give vanishing against every extension test. Trace injectivity
from `GeneralNeumannInjectivity` and `faithfulNopNullity = 2` bound the dimension.
The argument uses the actual radical and its explicit finite-dimensionality
through `diskRadical_finiteDimensional`; it does not infer nullity from index.
-/

noncomputable section
open MeasureTheory
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.CircleSobolev KsIndex.DtnBridge
open KsIndex.Radial KsIndex.ModeWitness KsIndex.DtNCircle

variable {k : ℕ}

/-- **V4a**: the boundary-trace mean of a full weak-kernel element vanishes —
the radial witness's constant flux detects exactly the mode `0`. -/
lemma kernel_trace_integral_zero (hk : 2 ≤ k) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, weakJacobi (surfacePotential k) u v = 0) :
    (∫ w : Circle₁, (diskTraceCLM u : Circle₁ → ℂ) w ∂circleMeasure) = 0 := by
  have h0 : weakJacobi (surfacePotential k) (radialDirichletH1 hk) u = 0 := by
    rw [← weakJacobi_conj, hu (radialDirichletH1 hk), map_zero]
  rw [radialDirichlet_weak_green hk u] at h0
  have hne : -(((kap k : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [neg_ne_zero, Complex.ofReal_ne_zero]
    exact pow_ne_zero 2 (ne_of_gt (kap_pos hk))
  exact (mul_eq_zero.mp h0).resolve_left hne

/-- **V4b**: the kernel's half-order trace pairs to zero, coefficientwise,
against every half-order datum through the faithful symbol sum. -/
lemma kernel_symbol_pairing_zero (hk : 2 ≤ k) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, weakJacobi (surfacePotential k) u v = 0)
    (g : Space (1 / 2 : ℝ)) :
    (∑' n : NZ, (dtnSymbol k n : ℂ) *
      (starRingEnd ℂ) (coeff (1 / 2 : ℝ) g n) *
      circleFourierCoeff (diskTraceCLM u) n) = 0 := by
  have h0 : weakJacobi (surfacePotential k) (jacobiExtensionH1 hk g) u = 0 := by
    rw [← weakJacobi_conj, hu (jacobiExtensionH1 hk g), map_zero]
  rw [jacobiExtensionH1_weak_pairing hk g u] at h0
  have h2π : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt Real.two_pi_pos
  exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast h2π)

/-- The Fourier mean of an `Lp` boundary datum with vanishing circle integral. -/
lemma circleFourierCoeff_zero_of_integral_zero {f : Circle₁ → ℂ}
    (hf : AEStronglyMeasurable f circleMeasure)
    (h : (∫ w : Circle₁, f w ∂circleMeasure) = 0) :
    circleFourierCoeff f 0 = 0 := by
  rw [circleFourierCoeff]
  rw [integral_circleMeasure hf, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.two_pi_pos.le] at h
  rw [fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul]
  rw [h, smul_zero]

set_option maxHeartbeats 1600000 in
-- The `⊤`-subtype radical forces heavy `whnf`/instance unification through
-- `domainJacobiForm`'s `mapPairing` spelling; default heartbeats time out.
/-- **V4 headline: the general Neumann row bound** — the full weak nullity of
the disk is at most `2`, by the half-trace injection into the faithful
boundary budget. -/
theorem neumannRow_nullity_le_two (hk : 3 ≤ k) :
    diskWeakNullity (⊤ : Submodule ℂ ComplexH1) (surfacePotential k) ≤ 2 := by
  have hk2 : 2 ≤ k := by omega
  have hcs : CompleteSpace ↥(⊤ : Submodule ℂ ComplexH1) :=
    (by rw [Submodule.top_coe]; exact isClosed_univ :
      IsClosed ((⊤ : Submodule ℂ ComplexH1) : Set ComplexH1)).completeSpace_coe
  set R := @formRadical ↥(⊤ : Submodule ℂ ComplexH1) inferInstance
    (diskDomain_innerProductSpace (⊤ : Submodule ℂ ComplexH1))
    (domainJacobiForm (⊤ : Submodule ℂ ComplexH1) (surfacePotential k)) with hR
  have hfinR : FiniteDimensional ℂ ↥R :=
    diskRadical_finiteDimensional (⊤ : Submodule ℂ ComplexH1) (surfacePotential k)
  -- every radical element is a FULL weak-kernel element
  have htest : ∀ u : ↥R, ∀ w : ComplexH1,
      weakJacobi (surfacePotential k) u.val.val w = 0 := by
    intro u w
    have h := (mem_formRadical _ u.val).mp u.property ⟨w, trivial⟩
    rwa [domainJacobiForm_apply] at h
  -- the half-trace map into the dotted space
  have hmem : ∀ u : ↥R, halfDiskTraceCLM u.val.val ∈ dotted (1 / 2 : ℝ) := by
    intro u
    rw [mem_dotted]
    rw [show coeff (1 / 2 : ℝ) (halfDiskTraceCLM u.val.val) 0 =
        circleFourierCoeff (diskTraceCLM u.val.val) 0 from coeff_halfDiskTrace _ 0]
    exact circleFourierCoeff_zero_of_integral_zero
      (Lp.aestronglyMeasurable _)
      (kernel_trace_integral_zero hk2 _ (htest u))
  let Φ : ↥R →ₗ[ℂ] ↥(dotted (1 / 2 : ℝ)) :=
    LinearMap.codRestrict (dotted (1 / 2 : ℝ))
      ((halfDiskTraceCLM.toLinearMap.comp
        (⊤ : Submodule ℂ ComplexH1).subtype).comp R.subtype) hmem
  have hinj : Function.Injective Φ := by
    intro u₁ u₂ h
    have hval : halfDiskTrace u₁.val.val = halfDiskTrace u₂.val.val :=
      congrArg Subtype.val h
    have htr : diskTraceCLM u₁.val.val = diskTraceCLM u₂.val.val := by
      rw [← toL2_halfDiskTrace, ← toL2_halfDiskTrace, hval]
    have hz : u₁.val.val - u₂.val.val = 0 := by
      apply weak_neumann_zero_of_trace_zero_gen hk2
      · intro v
        rw [sub_eq_add_neg, ← neg_one_smul ℂ u₂.val.val, weakJacobi_add_left,
          weakJacobi_smul_left, htest u₁ v, htest u₂ v, mul_zero, add_zero]
      · rw [map_sub, htr, sub_self]
    apply Subtype.ext; apply Subtype.ext
    exact sub_eq_zero.mp hz
  -- the range is an admissible sesqNullity competitor
  have hvan : ∀ x ∈ LinearMap.range Φ, ∀ w : ↥(dotted (1 / 2 : ℝ)),
      faithfulDtnB k x w = 0 := by
    rintro x ⟨u, rfl⟩ w
    have hpair := kernel_symbol_pairing_zero hk2 u.val.val (htest u) w.val
    have hcoe : ∀ n : NZ, coeff (1 / 2 : ℝ) (Φ u).val n.val =
        circleFourierCoeff (diskTraceCLM u.val.val) n.val := fun n =>
      coeff_halfDiskTrace _ n.val
    rw [faithfulDtnB]
    have hflip : ∀ n : NZ, (dtnSymbol k n : ℂ) *
        (starRingEnd ℂ) (coeff (1 / 2 : ℝ) (Φ u).val n.val) *
        coeff (1 / 2 : ℝ) w.val n.val =
        star ((dtnSymbol k n : ℂ) *
          (starRingEnd ℂ) (coeff (1 / 2 : ℝ) w.val n.val) *
          circleFourierCoeff (diskTraceCLM u.val.val) n.val) := by
      intro n
      rw [hcoe n]
      simp only [RCLike.star_def, map_mul, Complex.conj_conj, Complex.conj_ofReal]
      ring
    calc (∑' n : NZ, (dtnSymbol k n : ℂ) *
          (starRingEnd ℂ) (coeff (1 / 2 : ℝ) (Φ u).val n.val) *
          coeff (1 / 2 : ℝ) w.val n.val)
        = ∑' n : NZ, star ((dtnSymbol k n : ℂ) *
            (starRingEnd ℂ) (coeff (1 / 2 : ℝ) w.val n.val) *
            circleFourierCoeff (diskTraceCLM u.val.val) n.val) := tsum_congr hflip
      _ = star (∑' n : NZ, (dtnSymbol k n : ℂ) *
            (starRingEnd ℂ) (coeff (1 / 2 : ℝ) w.val n.val) *
            circleFourierCoeff (diskTraceCLM u.val.val) n.val) := tsum_star.symm
      _ = 0 := by rw [hpair, star_zero]
  -- the count: range finrank fits under the faithful budget
  have hle1 : (Module.finrank ℂ ↥(LinearMap.range Φ) : ℕ∞) ≤
      sesqNullity (faithfulDtnB k) := by
    apply le_iSup_of_le (LinearMap.range Φ)
    apply le_iSup_of_le hvan
    exact le_iSup_of_le inferInstance le_rfl
  rw [faithfulNopNullity hk] at hle1
  have hle2 : Module.finrank ℂ ↥(LinearMap.range Φ) ≤ 2 := by exact_mod_cast hle1
  have heq : Module.finrank ℂ ↥R = Module.finrank ℂ ↥(LinearMap.range Φ) :=
    (LinearMap.finrank_range_of_inj hinj).symm
  have hdw : diskWeakNullity (⊤ : Submodule ℂ ComplexH1) (surfacePotential k) =
      Module.finrank ℂ ↥R := rfl
  rw [hdw, heq]
  exact hle2

end KsIndex.Spectral
