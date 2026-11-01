module

public import KsIndexLean.KarcherLiftHeightPhase

@[expose] public section


/-! Exponential root coordinates with a supplied real phase. The application
uses the actual EW height, rather than a choice of complex logarithm. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex

/-- A root defined using the logarithmic modulus and a real lifted phase. -/
def heightRoot (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  Complex.exp (((Real.log ‖z‖ : ℝ) : ℂ) / m + I * (h : ℂ) / m)

lemma heightRoot_ne_zero (m : ℕ) (z : ℂ) (h : ℝ) : heightRoot m z h ≠ 0 :=
  Complex.exp_ne_zero _

/-- The prescribed phase ensures that the exponential root has the correct
power, without choosing an argument branch. -/
theorem heightRoot_pow {m : ℕ} (hm : 0 < m) {z : ℂ} (hz : z ≠ 0)
    {h : ℝ} (hh : Complex.exp (I * (h : ℂ)) = z / (‖z‖ : ℂ)) :
    heightRoot m z h ^ m = z := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  unfold heightRoot
  rw [← Complex.exp_nat_mul]
  have he : (m : ℂ) * (((Real.log ‖z‖ : ℝ) : ℂ) / m + I * (h : ℂ) / m) =
      (Real.log ‖z‖ : ℂ) + I * (h : ℂ) := by field_simp
  rw [he, Complex.exp_add, ← Complex.ofReal_exp,
    Real.exp_log (norm_pos_iff.mpr hz), hh]
  field_simp

/-- Changing the lifted height by an integral m-fold period leaves the root
unchanged. -/
theorem heightRoot_period {m : ℕ} (hm : 0 < m) (z : ℂ) (h : ℝ) (n : ℤ) :
    heightRoot m z (h + ((n * (m : ℤ) : ℤ) : ℝ) * (2 * Real.pi)) =
      heightRoot m z h := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold heightRoot
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨n, ?_⟩
  push_cast
  field_simp
  ring

/-- Equality of roots detects precisely integral m-fold height shifts. -/
theorem heightRoot_eq_iff {m : ℕ} (hm : 0 < m) (z : ℂ) (h l : ℝ) :
    heightRoot m z h = heightRoot m z l ↔
      ∃ n : ℤ, h = l + ((n * (m : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
  constructor
  · intro he
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    refine ⟨n, ?_⟩
    have hi := congrArg Complex.im hn
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    simp [Complex.div_natCast, Complex.mul_im] at hi
    push_cast
    field_simp at hi
    nlinarith [hi]
  · rintro ⟨n, rfl⟩
    exact heightRoot_period hm z l n

/-- Every m-th root of a nonzero value is realized by an integral change of
height sheet. -/
theorem exists_heightRoot_shift {m : ℕ} (hm : 0 < m) {z : ℂ} (hz : z ≠ 0)
    {h : ℝ} (hh : Complex.exp (I * (h : ℂ)) = z / (‖z‖ : ℂ))
    {t : ℂ} (ht : t ^ m = z) :
    ∃ n : ℤ, heightRoot m z (h + (n : ℝ) * (2 * Real.pi)) = t := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have ht0 : t ≠ 0 := by
    intro he
    rw [he, zero_pow (Nat.ne_of_gt hm)] at ht
    exact hz ht.symm
  have hp := heightRoot_pow hm hz hh
  unfold heightRoot at hp
  rw [← Complex.exp_nat_mul] at hp
  have he : Complex.exp ((m : ℂ) *
      ((Real.log ‖z‖ : ℂ) / m + I * (h : ℂ) / m)) =
      Complex.exp ((m : ℂ) * Complex.log t) := by
    rw [hp, Complex.exp_nat_mul, Complex.exp_log ht0, ht]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  refine ⟨-n, ?_⟩
  unfold heightRoot
  rw [← Complex.exp_log ht0]
  congr 1
  push_cast
  apply (mul_left_cancel₀ hm')
  calc
    (m : ℂ) * ((Real.log ‖z‖ : ℂ) / m + I *
        ((h : ℂ) + -(n : ℂ) * (2 * (Real.pi : ℂ))) / m) =
      (m : ℂ) * ((Real.log ‖z‖ : ℂ) / m + I * (h : ℂ) / m) -
        (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by field_simp; ring
    _ = (m : ℂ) * Complex.log t := by rw [hn]; ring

/-- The root of the normalized rational coordinate on every actual finite
sheet of the EW carrier. -/
theorem lift_heightRoot_pow {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b w : PuncturedPlane k) (C : PeriodTarget)
    (q : PeriodicEWCarrier hk b C)
    (hq : HeightLift.projection q = finiteParameter w) :
    heightRoot m (heightCayley k w.val / heightCayley k b.val)
      (HeightLift.height q) ^ m = heightCayley k w.val / heightCayley k b.val :=
  heightRoot_pow hm (div_ne_zero (heightCayley_ne_zero w.property)
    (heightCayley_ne_zero b.property)) (exp_lift_height hk b w C q hq)

/-- Continuity of the exponential root along any continuous nonzero base
coordinate and continuous real lifted phase. -/
theorem continuous_heightRoot {X : Type*} [TopologicalSpace X] (m : ℕ)
    {Z : X → ℂ} {H : X → ℝ} (hZ : Continuous Z) (hH : Continuous H)
    (hzero : ∀ x, Z x ≠ 0) : Continuous (fun x => heightRoot m (Z x) (H x)) := by
  unfold heightRoot
  apply Continuous.cexp
  exact ((Complex.continuous_ofReal.comp (hZ.norm.log (fun x => norm_ne_zero_iff.mpr (hzero x)))).div_const _).add
    ((continuous_const.mul (Complex.continuous_ofReal.comp hH)).div_const _)

namespace HeightLift

/-- The exponential root descends to the actual m-period quotient for any
base coordinate. No logarithm branch on the base is selected. -/
def quotientHeightRoot {P : Type*} {F : P → PeriodTarget} {m : ℕ}
    (hm : 0 < m) (Z : P → ℂ) : PeriodQuotient F m → ℂ :=
  Quotient.lift (fun q => heightRoot m (Z (projection q)) (height q)) (by
    rintro q r ⟨n, rfl⟩
    exact (heightRoot_period hm (Z (projection q)) (height q) n).symm)

@[simp] theorem quotientHeightRoot_mk {P : Type*} {F : P → PeriodTarget} {m : ℕ}
    (hm : 0 < m) (Z : P → ℂ) (q : HeightLift F) :
    quotientHeightRoot hm Z (Quotient.mk _ q) =
      heightRoot m (Z (projection q)) (height q) := rfl

/-- A phase identity on the lift yields the power identity on the actual
quotient, over any region where the base coordinate is nonzero. -/
theorem quotientHeightRoot_pow {P : Type*} {F : P → PeriodTarget} {m : ℕ}
    (hm : 0 < m) (Z : P → ℂ) (U : Set P)
    (hZ : ∀ p ∈ U, Z p ≠ 0)
    (hphase : ∀ q : HeightLift F, projection q ∈ U →
      Complex.exp (I * (height q : ℂ)) = Z (projection q) / (‖Z (projection q)‖ : ℂ))
    (x : PeriodQuotient F m) (hx : quotientProjection m x ∈ U) :
    quotientHeightRoot hm Z x ^ m = Z (quotientProjection m x) := by
  induction x using Quotient.inductionOn with
  | h q => exact heightRoot_pow hm (hZ _ hx) (hphase q hx)

/-- Every algebraic root over a parameter point comes from an actual quotient
sheet, provided the actual height realizes the coordinate's phase there. -/
theorem exists_quotientHeightRoot {P : Type*} {F : P → PeriodTarget}
    {m : ℕ} (hm : 0 < m) (Z : P → ℂ) (p : P) (hZ : Z p ≠ 0)
    (hphase : ∀ q : HeightLift F, projection q = p →
      Complex.exp (I * (height q : ℂ)) = Z p / (‖Z p‖ : ℂ))
    {t : ℂ} (ht : t ^ m = Z p) :
    ∃ x : PeriodQuotient F m, quotientProjection m x = p ∧ quotientHeightRoot hm Z x = t := by
  obtain ⟨q, hq⟩ := projection_surjective (F := F) p
  obtain ⟨n, hn⟩ := exists_heightRoot_shift hm hZ (hphase q hq) ht
  refine ⟨Quotient.mk _ (deck n q), ?_, ?_⟩
  · exact hq
  · change heightRoot m (Z (projection (deck n q))) (height (deck n q)) = t
    simpa only [projection_deck, height_deck, hq] using hn

/-- Over a fixed parameter point the root distinguishes all actual quotient
sheets. This uses the defining period relation, not an abstract fiber count. -/
theorem quotientHeightRoot_fiber_injective {P : Type*} {F : P → PeriodTarget}
    {m : ℕ} (hm : 0 < m) (Z : P → ℂ) (x y : PeriodQuotient F m)
    (hp : quotientProjection m x = quotientProjection m y)
    (hr : quotientHeightRoot hm Z x = quotientHeightRoot hm Z y) : x = y := by
  induction x using Quotient.inductionOn with
  | h q =>
    induction y using Quotient.inductionOn with
    | h r =>
      change projection q = projection r at hp
      change heightRoot m (Z (projection q)) (height q) =
        heightRoot m (Z (projection r)) (height r) at hr
      rw [hp] at hr
      obtain ⟨n, hn⟩ := (heightRoot_eq_iff hm _ _ _).mp hr
      apply Quotient.sound
      refine ⟨-n, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact hp
      · change height q + (((-n) * (m : ℤ) : ℤ) : ℝ) * (2 * Real.pi) = height r
        rw [hn]
        push_cast
        ring

/-- On a region where the base coordinate is injective and its phase is
realized by the height, the quotient root itself is injective. -/
theorem quotientHeightRoot_injOn {P : Type*} {F : P → PeriodTarget}
    {m : ℕ} (hm : 0 < m) (Z : P → ℂ) (U : Set P)
    (hZ : ∀ p ∈ U, Z p ≠ 0) (hinj : Set.InjOn Z U)
    (hphase : ∀ q : HeightLift F, projection q ∈ U →
      Complex.exp (I * (height q : ℂ)) = Z (projection q) / (‖Z (projection q)‖ : ℂ)) :
    Set.InjOn (quotientHeightRoot (F := F) hm Z) (quotientProjection m ⁻¹' U) := by
  intro x hx y hy he
  apply quotientHeightRoot_fiber_injective hm Z x y _ he
  apply hinj hx hy
  rw [← quotientHeightRoot_pow hm Z U hZ hphase x hx,
    ← quotientHeightRoot_pow hm Z U hZ hphase y hy, he]

/-- The root on the existing quotient topology is continuous whenever the
base coordinate is continuous and nowhere zero. -/
theorem continuous_quotientHeightRoot {P : Type*} [TopologicalSpace P]
    {F : P → PeriodTarget} {m : ℕ} (hm : 0 < m) {Z : P → ℂ}
    (hZ : Continuous Z) (hzero : ∀ p, Z p ≠ 0) :
    Continuous (quotientHeightRoot (F := F) hm Z) := by
  apply continuous_quot_lift
  exact continuous_heightRoot m (hZ.comp continuous_projection) continuous_height
    (fun q => hzero (projection q))

end HeightLift

end KsIndex.KarcherData
