module

public import KsIndexLean.FourierEigenTests
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Perfect

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace

/-- A finite Laurent sum vanishing at infinitely many nonzero complex points
vanishes everywhere off zero. Clearing negative powers reduces to polynomial roots. -/
theorem finite_laurent_eq_zero_of_infinite (s : Finset ℤ) (c : ℤ → ℂ)
    (A : Set ℂ) (hA : A.Infinite) (hA0 : ∀ z ∈ A, z ≠ 0)
    (hz : ∀ z ∈ A, ∑ n ∈ s, c n * z ^ n = 0) :
    ∀ z : ℂ, z ≠ 0 → ∑ n ∈ s, c n * z ^ n = 0 := by
  let N : ℕ := s.sup (fun n => (-n).toNat)
  have hN (n : ℤ) (hn : n ∈ s) : 0 ≤ n + (N : ℤ) := by
    have h : (-n).toNat ≤ N := Finset.le_sup (f := fun n : ℤ => (-n).toNat) hn
    omega
  let p : Polynomial ℂ := ∑ n ∈ s, Polynomial.C (c n) * Polynomial.X ^ (n + (N : ℤ)).toNat
  have he (z : ℂ) (hz0 : z ≠ 0) :
      p.eval z = z ^ (N : ℤ) * ∑ n ∈ s, c n * z ^ n := by
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← zpow_natCast, Int.toNat_of_nonneg (hN n hn), zpow_add₀ hz0]
    ring
  have hp : p = 0 := p.eq_zero_of_infinite_isRoot (hA.mono (by
    intro z hzA
    change p.eval z = 0
    rw [he z (hA0 z hzA), hz z hzA, mul_zero]))
  intro z hz0
  have h := he z hz0
  rw [hp, Polynomial.eval_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (zpow_ne_zero _ hz0)

lemma fourierAmbient_eq_zpow_on_circle (n : ℤ) (w : Circle₁) :
    fourierAmbient n w = (w : ℂ) ^ n := by
  have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  cases n with
  | ofNat m => simp [fourierAmbient]
  | negSucc m => simp [fourierAmbient, zpow_negSucc, ← Complex.inv_eq_conj hw, inv_pow]

/-- An infinite subset of the circle determines a finite Fourier sum. -/
theorem finite_fourier_eq_zero_of_infinite (s : Finset ℤ) (c : ℤ → ℂ)
    (A : Set Circle₁) (hA : A.Infinite)
    (hz : ∀ w ∈ A, ∑ n ∈ s, c n * fourierAmbient n w = 0) :
    ∀ w : Circle₁, ∑ n ∈ s, c n * fourierAmbient n w = 0 := by
  have hn (w : Circle₁) : (w : ℂ) ≠ 0 := by
    have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
    intro h
    simp [h] at hw
  have h := finite_laurent_eq_zero_of_infinite s c
    ((fun w : Circle₁ => (w : ℂ)) '' A)
    (hA.image (fun _ _ _ _ h => Subtype.ext h))
    (by rintro _ ⟨w, _, rfl⟩; exact hn w)
    (by
      rintro _ ⟨w, hw, rfl⟩
      simpa only [fourierAmbient_eq_zpow_on_circle] using hz w hw)
  intro w
  simpa only [fourierAmbient_eq_zpow_on_circle] using h w (hn w)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

local instance : Nontrivial Circle₁ := by
  refine ⟨⟨⟨1, mem_sphere_zero_iff_norm.mpr (by norm_num)⟩,
    ⟨-1, mem_sphere_zero_iff_norm.mpr (by norm_num)⟩, ?_⟩⟩
  intro h
  have he := congrArg (fun w : Circle₁ => (w : ℂ)) h
  norm_num at he

local instance : Nontrivial (AddCircle (2 * Real.pi)) :=
  fourierCircleHomeomorph.symm.injective.nontrivial

local instance : NullSingletonClass circleMeasure := by
  constructor
  intro w
  rw [← measurePreserving_fourierCircleHomeomorph.map_eq,
    Measure.map_apply fourierCircleHomeomorph.continuous.measurable (measurableSet_singleton w)]
  have he : fourierCircleHomeomorph ⁻¹' {w} = {fourierCircleHomeomorph.symm w} := by
    ext x
    change fourierCircleHomeomorph x = w ↔ x = fourierCircleHomeomorph.symm w
    constructor
    · intro h; exact fourierCircleHomeomorph.injective (h.trans (fourierCircleHomeomorph.apply_symm_apply w).symm)
    · rintro rfl; exact fourierCircleHomeomorph.apply_symm_apply w
  rw [he]
  exact measure_singleton _

local instance : circleMeasure.IsOpenPosMeasure := by
  rw [← measurePreserving_fourierCircleHomeomorph.map_eq]
  exact fourierCircleHomeomorph.continuous.isOpenPosMeasure_map fourierCircleHomeomorph.surjective

/-- Almost-everywhere vanishing on any nonempty open boundary arc is enough
for a finite Fourier sum to vanish on the whole circle. -/
theorem finite_fourier_eq_zero_of_open_ae (s : Finset ℤ) (c : ℤ → ℂ)
    (A : Set Circle₁) (hA : IsOpen A) (hne : A.Nonempty)
    (hz : (fun w : Circle₁ => ∑ n ∈ s, c n * fourierAmbient n w) =ᵐ[circleMeasure.restrict A] 0) :
    ∀ w : Circle₁, ∑ n ∈ s, c n * fourierAmbient n w = 0 := by
  have hc : Continuous (fun w : Circle₁ => ∑ n ∈ s, c n * fourierAmbient n w) := by
    apply continuous_finsetSum
    intro n hn
    exact continuous_const.mul ((contDiff_fourierAmbient n).continuous.comp continuous_subtype_val)
  have he := Measure.eqOn_open_of_ae_eq hz hA hc.continuousOn continuous_const.continuousOn
  have hi : A.Infinite := by
    intro hf
    exact hA.measure_ne_zero circleMeasure hne (hf.measure_zero circleMeasure)
  exact finite_fourier_eq_zero_of_infinite s c A hi he

end KsIndex.Trace
