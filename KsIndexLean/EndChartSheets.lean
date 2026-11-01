module

/-
# Angular sheets and the end-chart energy bound

For `0 < m`, the half-open angular sectors of width `2π/m`, anchored at `−π`,
cover the plane. The chart `endChart p m ζ = p + ζ^m` is injective on each
sector: equality of powers fixes the norm and makes the argument difference
an integer multiple of `2π/m`, which the half-open window forces to be zero.

Applying the per-sheet energy identity and summing the `m` contributions gives
`∫_A ‖(Du ∘ endChart p m).comp (endDeriv m)‖² ≤ m · ∫_N ‖Du‖²`
when `A` is measurable and `endChart p m '' A ⊆ N`. The bound uses nonnegative
integrals and requires no measurability hypothesis on `N` or `Du`.
When `Du` is a field's derivative, the chain rule identifies the left integrand
with the energy density of the pullback. The estimate concerns derivative
energy, not unweighted integrability of the field itself.
-/
public import KsIndexLean.EndChartEnergy
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

@[expose] public section


noncomputable section
open Set MeasureTheory Real
open scoped ENNReal
namespace KsIndex.EndChart

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The j-th angular sector of width `2π/m` (half-open, anchored at `−π` to
match `Complex.arg`'s range). -/
def powSector (m j : ℕ) : Set ℂ :=
  {ζ : ℂ | Complex.arg ζ ∈ Ioc (-π + j * (2 * π / m)) (-π + (j + 1) * (2 * π / m))}

lemma measurableSet_powSector (m j : ℕ) : MeasurableSet (powSector m j) :=
  Complex.measurable_arg measurableSet_Ioc

/-- The m sectors cover the plane (`arg` lands in `Ioc (−π) π`, which the m
windows partition). -/
lemma exists_mem_powSector {m : ℕ} (hm : 0 < m) (ζ : ℂ) :
    ∃ j < m, ζ ∈ powSector m j := by
  set t : ℝ := Complex.arg ζ with ht
  obtain ⟨ht1, ht2⟩ := Complex.arg_mem_Ioc ζ
  have hL : (0 : ℝ) < 2 * π / m := by positivity
  set x : ℝ := (t + π) / (2 * π / m) with hx
  have hx0 : 0 < x := div_pos (by linarith) hL
  have hxm : x ≤ m := by
    rw [hx, div_le_iff₀ hL]
    have hmL : (m : ℝ) * (2 * π / m) = 2 * π := by
      field_simp
    linarith [hmL]
  have h1 : 1 ≤ ⌈x⌉ := by
    exact_mod_cast Int.ceil_pos.mpr hx0
  have h2 : ⌈x⌉ ≤ (m : ℤ) := Int.ceil_le.mpr (by exact_mod_cast hxm)
  refine ⟨(⌈x⌉ - 1).toNat, by omega, ?_⟩
  have hkr : (((⌈x⌉ - 1).toNat : ℕ) : ℝ) = ((⌈x⌉ : ℤ) : ℝ) - 1 := by
    have : ((⌈x⌉ - 1).toNat : ℤ) = ⌈x⌉ - 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have hxL : x * (2 * π / m) = t + π := by
    rw [hx]
    exact div_mul_cancel₀ _ hL.ne'
  simp only [powSector, Set.mem_ofPred_eq, mem_Ioc, ← ht]
  constructor
  · have hlt : (((⌈x⌉ - 1).toNat : ℕ) : ℝ) < x := by
      rw [hkr]
      linarith [Int.ceil_lt_add_one x]
    have h' := mul_lt_mul_of_pos_right hlt hL
    rw [hxL] at h'
    linarith
  · have hge : x ≤ (((⌈x⌉ - 1).toNat : ℕ) : ℝ) + 1 := by
      rw [hkr]
      linarith [Int.le_ceil x]
    have h' := mul_le_mul_of_nonneg_right hge hL.le
    rw [hxL] at h'
    linarith

/-- **Sector injectivity**: `ζ ↦ ζ^m` is injective on each sector — equal
m-th powers give equal norms and an argument difference in `(2π/m)·ℤ`,
which the width-`2π/m` window forces to vanish. -/
lemma injOn_pow_powSector {m : ℕ} (hm : 0 < m) (j : ℕ) :
    Set.InjOn (fun ζ : ℂ => ζ ^ m) (powSector m j) := by
  intro x hx y hy hxy
  simp only at hxy
  simp only [powSector, Set.mem_ofPred_eq, mem_Ioc] at hx hy
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [zero_pow hm.ne'] at hxy
    exact ((pow_eq_zero_iff hm.ne').mp hxy.symm).symm
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [zero_pow hm.ne'] at hxy
    exact absurd ((pow_eq_zero_iff hm.ne').mp hxy) hx0
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hnorm : ‖x‖ = ‖y‖ := by
    have h : ‖x‖ ^ m = ‖y‖ ^ m := by rw [← norm_pow, ← norm_pow, hxy]
    exact (pow_left_strictMonoOn₀ hm.ne').injOn hnx.le hny.le h
  have hexp : Complex.exp (m * (x.arg * Complex.I))
      = Complex.exp (m * (y.arg * Complex.I)) := by
    have hX : ((‖x‖ : ℝ) : ℂ) ^ m * Complex.exp (m * (x.arg * Complex.I))
        = x ^ m := by
      rw [Complex.exp_nat_mul, ← mul_pow, Complex.norm_mul_exp_arg_mul_I]
    have hY : ((‖y‖ : ℝ) : ℂ) ^ m * Complex.exp (m * (y.arg * Complex.I))
        = y ^ m := by
      rw [Complex.exp_nat_mul, ← mul_pow, Complex.norm_mul_exp_arg_mul_I]
    have hne : ((‖x‖ : ℝ) : ℂ) ^ m ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast hnx.ne')
    apply mul_left_cancel₀ hne
    rw [hX, hxy, hnorm, hY]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hreal : (m : ℝ) * x.arg = m * y.arg + n * (2 * π) := by
    have h2 : ((m * x.arg : ℝ) : ℂ) * Complex.I
        = ((m * y.arg + n * (2 * π) : ℝ) : ℂ) * Complex.I := by
      push_cast
      linear_combination hn
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h2
  have hL : (0 : ℝ) < 2 * π / m := by positivity
  have hdiff : |x.arg - y.arg| < 2 * π / m := by
    rw [abs_lt]
    constructor <;> [linarith [hx.1, hy.2]; linarith [hx.2, hy.1]]
  have hn0 : n = 0 := by
    have hmdiff : (m : ℝ) * (x.arg - y.arg) = n * (2 * π) := by
      linarith [hreal]
    have hb : |(n : ℝ)| * (2 * π) < 2 * π := by
      have h1 : (m : ℝ) * |x.arg - y.arg| < m * (2 * π / m) :=
        mul_lt_mul_of_pos_left hdiff (by exact_mod_cast hm)
      have hmL : (m : ℝ) * (2 * π / m) = 2 * π := by field_simp
      calc |(n : ℝ)| * (2 * π)
          = |(n : ℝ) * (2 * π)| := by
            rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        _ = |(m : ℝ)| * |x.arg - y.arg| := by rw [← abs_mul, ← hmdiff, abs_mul]
        _ = (m : ℝ) * |x.arg - y.arg| := by rw [Nat.abs_cast]
        _ < 2 * π := by rw [← hmL]; exact h1
    have habs : |(n : ℝ)| < 1 := by
      nlinarith [hb, Real.pi_pos, abs_nonneg ((n : ℝ))]
    have h' := abs_lt.mp habs
    have hlo : (-1 : ℤ) < n := by exact_mod_cast h'.1
    have hhi : n < 1 := by exact_mod_cast h'.2
    omega
  have hargeq : x.arg = y.arg := by
    have h : (m : ℝ) * x.arg = m * y.arg := by
      rw [hn0] at hreal
      simpa using hreal
    exact mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0) h
  exact Complex.ext_norm_arg hnorm hargeq

/-- The chart `σ(ζ) = p + ζ^m` inherits sector injectivity. -/
lemma injOn_endChart_powSector (p : ℂ) {m : ℕ} (hm : 0 < m) (j : ℕ) :
    Set.InjOn (endChart p m) (powSector m j) := by
  intro x hx y hy hxy
  have h : x ^ m = y ^ m := add_left_cancel (hxy : p + x ^ m = p + y ^ m)
  exact injOn_pow_powSector hm j hx hy h

/-- For positive `m`, the transported energy over a measurable chart domain
is at most `m` times the energy over any set containing its image. Each sector
uses the per-sheet identity; no measurability hypothesis on the containing
set is needed. When `Du` is the derivative of `u`, the chain rule identifies
the left integrand with the derivative energy of `u ∘ endChart p m`. -/
theorem lintegral_energy_comp_endChart_le (p : ℂ) {m : ℕ} (hm : 0 < m)
    {A : Set ℂ} (hA : MeasurableSet A) {N : Set ℂ}
    (hAN : endChart p m '' A ⊆ N) (Du : ℂ → (ℂ →L[ℝ] F)) :
    (∫⁻ ζ in A,
        ENNReal.ofReal
          (‖(Du (endChart p m ζ)).comp (endDeriv m ζ)‖ ^ 2) ∂volume)
      ≤ m * ∫⁻ w in N, ENNReal.ofReal (‖Du w‖ ^ 2) ∂volume := by
  have hcov : A ⊆ ⋃ j : Fin m, A ∩ powSector m j := by
    intro ζ hζ
    obtain ⟨j, hj, hmem⟩ := exists_mem_powSector hm ζ
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hζ, hmem⟩
  calc (∫⁻ ζ in A,
        ENNReal.ofReal
          (‖(Du (endChart p m ζ)).comp (endDeriv m ζ)‖ ^ 2) ∂volume)
      ≤ ∫⁻ ζ in ⋃ j : Fin m, A ∩ powSector m j,
          ENNReal.ofReal
            (‖(Du (endChart p m ζ)).comp (endDeriv m ζ)‖ ^ 2) ∂volume :=
        lintegral_mono_set hcov
    _ ≤ ∑' j : Fin m, ∫⁻ ζ in A ∩ powSector m j,
          ENNReal.ofReal
            (‖(Du (endChart p m ζ)).comp (endDeriv m ζ)‖ ^ 2) ∂volume :=
        lintegral_iUnion_le _ _
    _ = ∑ j : Fin m, ∫⁻ ζ in A ∩ powSector m j,
          ENNReal.ofReal
            (‖(Du (endChart p m ζ)).comp (endDeriv m ζ)‖ ^ 2) ∂volume :=
        tsum_fintype _
    _ ≤ ∑ _j : Fin m, ∫⁻ w in N, ENNReal.ofReal (‖Du w‖ ^ 2) ∂volume := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hS : MeasurableSet (A ∩ powSector m j.1) :=
          hA.inter (measurableSet_powSector m j.1)
        have hinj : Set.InjOn (endChart p m) (A ∩ powSector m j.1) :=
          (injOn_endChart_powSector p hm j.1).mono inter_subset_right
        rw [← lintegral_energy_endChart_sheet p m hS hinj Du]
        exact lintegral_mono' (Measure.restrict_mono
          ((image_mono inter_subset_left).trans hAN) le_rfl) fun _ => le_rfl
    _ = m * ∫⁻ w in N, ENNReal.ofReal (‖Du w‖ ^ 2) ∂volume := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end KsIndex.EndChart
