module

public import KsIndexLean.PowerArcConvolution
public import KsIndexLean.Statements

@[expose] public section


/-! Finite admissible trials with normalized power-arc coefficients. -/

namespace KsIndex.PowerArc
open CircleQ Statements

noncomputable def normalizedPowerField (β : ℝ) (d : ℤ) : ℤ → ℂ :=
  ((g β 0 : ℂ)⁻¹) • powerField β d

lemma normalizedPowerField_apply (β : ℝ) (d n : ℤ) :
    normalizedPowerField β d n = (g β (2 * (n : ℝ) + d) / g β 0 : ℝ) := by
  simp only [normalizedPowerField, Pi.smul_apply, smul_eq_mul, powerField,
    div_eq_mul_inv]
  push_cast
  ring

lemma normalizedPowerField_memDom {β : ℝ} (hβ : 0 < β) (d : ℤ) :
    MemDom (normalizedPowerField β d) :=
  memDom_smul _ (powerField_memDom hβ d)

lemma convS_normalizedPowerField {β : ℝ} (hβ : 0 < β) (d m : ℤ) :
    convS (normalizedPowerField β d) m =
      (g β (2 * (m : ℝ) + (d + 1)) / g β 0 : ℝ) := by
  rw [normalizedPowerField, convS_smul, convS_powerField hβ]
  push_cast
  ring

noncomputable def powerTrial {ι : Type*} (s : Finset ι)
    (β : ι → ℝ) (d : ι → ℤ) (a : ι → ℂ) : ℤ → ℂ :=
  ∑ i ∈ s, a i • normalizedPowerField (β i) (d i)

lemma powerTrial_memDom {ι : Type*} (s : Finset ι)
    (β : ι → ℝ) (d : ι → ℤ) (a : ι → ℂ) (hβ : ∀ i ∈ s, 0 < β i) :
    MemDom (powerTrial s β d a) := by
  apply (mem_Dom).mp
  exact Dom.sum_mem (fun i hi => memDom_smul _ (normalizedPowerField_memDom (hβ i hi) _))

lemma convS_powerTrial {ι : Type*} (s : Finset ι)
    (β : ι → ℝ) (d : ι → ℤ) (a : ι → ℂ) (hβ : ∀ i ∈ s, 0 < β i) (m : ℤ) :
    convS (powerTrial s β d a) m =
      ∑ i ∈ s, a i * (g (β i) (2 * (m : ℝ) + (d i + 1)) / g (β i) 0 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [powerTrial, convS]
  | @insert i s hi ih =>
    have hbi := hβ i (Finset.mem_insert_self i s)
    have hbs : ∀ j ∈ s, 0 < β j := fun j hj => hβ j (Finset.mem_insert_of_mem hj)
    have hf : powerTrial (insert i s) β d a =
        a i • normalizedPowerField (β i) (d i) + powerTrial s β d a := by
      simp only [powerTrial, Finset.sum_insert hi]
    rw [hf, convS_add (summable_normSq (memDom_smul _
      (normalizedPowerField_memDom hbi _)).1)
      (summable_normSq (powerTrial_memDom s β d a hbs).1),
      convS_smul, convS_normalizedPowerField hbi, ih hbs, Finset.sum_insert hi]

end KsIndex.PowerArc
