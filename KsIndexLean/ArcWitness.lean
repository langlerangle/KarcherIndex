module

/-
# A negative arc witness supported away from the junctions

For `0 < a < 1` and `2 * a * (1 - a) ≤ b²`, this file constructs
`0 < η ≤ 1/4` such that the Fourier coefficients of `psiF η` belong to
`MemArc` and have strictly negative `NQformArc a b` energy.

The cutoff field satisfies `psiF η = vF - fJ η`, so its coefficients are
`cC - fc (fJ η)`. Weighted square summability follows from the corresponding
bounds for these two sequences. The arc constraint follows from the
convolution identity for a continuous field vanishing where `cos θ < η`.

The perturbation estimate bounds the change in energy by
`Cσ * (ε * Wc + (ε⁻¹ + 3) * CB * η^(3/4))` for every `ε > 0`, where
`Cσ = 1 + b² / min a (1 - a)` and `Wc` is the weighted square sum of `cC`.
Choosing `ε` from the negative energy margin of `cC`, then choosing `η`
sufficiently small, preserves strict negativity. The result supplies a
specific cutoff witness for subsequent disk constructions; it does not
assert a density theorem for arbitrary arc-domain elements.
-/
public import KsIndexLean.ArcBudget
public import KsIndexLean.ArcBridge
public import KsIndexLean.ArcLower

@[expose] public section


noncomputable section

open Real Set
open KsIndex.ArcField KsIndex.ArcJunction KsIndex.JunctionFresnel KsIndex.ArcBudget
  KsIndex.ArcSpace KsIndex.ArcForm KsIndex.ArcLower KsIndex.Parseval

namespace KsIndex.ArcWitness

/-! ### The coefficients of the cut field -/

lemma psiF_eq_sub (η θ : ℝ) : psiF η θ = vF θ - fJ η θ :=
  eq_sub_of_add_eq (psiF_add_fJ η θ)

/-- `fc` is subtractive on continuous integrands. -/
lemma fc_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (ℓ : ℤ) :
    Parseval.fc (fun θ => f θ - g θ) ℓ = Parseval.fc f ℓ - Parseval.fc g ℓ := by
  have hchar : Continuous (fun θ : ℝ => Complex.exp (-(ℓ : ℂ) * Complex.I * θ)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  simp only [Parseval.fc]
  rw [← mul_sub]
  congr 1
  have h1 : IntervalIntegrable
      (fun θ : ℝ => f θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ))
      MeasureTheory.volume 0 (2 * π) := (hf.mul hchar).intervalIntegrable _ _
  have h2 : IntervalIntegrable
      (fun θ : ℝ => g θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ))
      MeasureTheory.volume 0 (2 * π) := (hg.mul hchar).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub h1 h2]
  exact intervalIntegral.integral_congr fun θ _ => by ring

/-- **The cut coefficients**: `fc (psiF η) = cC − fc (fJ η)`. -/
lemma fc_psiF_eq (η : ℝ) (ℓ : ℤ) :
    Parseval.fc (psiF η) ℓ = ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ := by
  have h1 : Parseval.fc (psiF η) ℓ = Parseval.fc (fun θ => vF θ - fJ η θ) ℓ := by
    congr 1
    funext θ
    exact psiF_eq_sub η θ
  rw [h1, fc_sub continuous_vF (continuous_fJ η), KsIndex.ArcField.fc_vF]

lemma fc_psiF_funext (η : ℝ) :
    Parseval.fc (psiF η) = fun ℓ => ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ :=
  funext (fc_psiF_eq η)

/-! ### Membership in the arc domain -/

/-- The weight half: `Summable ((1+|ℓ|)·‖cC − f̂‖²)`. -/
lemma summable_weight_sub (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) :
    Summable (fun ℓ : ℤ =>
      (1 + |(ℓ : ℝ)|) * ‖ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ‖ ^ 2) := by
  have hc : Summable (fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖ArcSpace.cC ℓ‖ ^ 2) :=
    (ArcSpace.mem_ArcDom.mp ArcSpace.cC_mem_ArcDom).1
  have hf := summable_weighted η hη0 hη
  refine Summable.of_nonneg_of_le (fun ℓ => by positivity) (fun ℓ => ?_)
    ((hc.mul_left 2).add (hf.mul_left 2))
  have h1 : (0:ℝ) ≤ 1 + |(ℓ : ℝ)| := by positivity
  have htri : ‖ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ‖
      ≤ ‖ArcSpace.cC ℓ‖ + ‖Parseval.fc (fJ η) ℓ‖ := norm_sub_le _ _
  have hsq : ‖ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ‖ ^ 2
      ≤ 2 * ‖ArcSpace.cC ℓ‖ ^ 2 + 2 * ‖Parseval.fc (fJ η) ℓ‖ ^ 2 := by
    nlinarith [htri, norm_nonneg (ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ),
      sq_nonneg (‖ArcSpace.cC ℓ‖ - ‖Parseval.fc (fJ η) ℓ‖)]
  calc (1 + |(ℓ : ℝ)|) * ‖ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ‖ ^ 2
      ≤ (1 + |(ℓ : ℝ)|) * (2 * ‖ArcSpace.cC ℓ‖ ^ 2 + 2 * ‖Parseval.fc (fJ η) ℓ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq h1
    _ = 2 * ((1 + |(ℓ : ℝ)|) * ‖ArcSpace.cC ℓ‖ ^ 2)
        + 2 * ((1 + |(ℓ : ℝ)|) * ‖Parseval.fc (fJ η) ℓ‖ ^ 2) := by ring

/-- Membership: `MemArc (fc (psiF η))`. -/
theorem memArc_psiF (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) :
    MemArc (Parseval.fc (psiF η)) := by
  constructor
  · rw [fc_psiF_funext η]
    exact summable_weight_sub η hη0 hη
  · intro m
    have hβ := KsIndex.ArcBridge.convS₁_fc_eq (psiF η) (continuous_psiF η) hη0
      (fun θ hθ => psiF_eq_zero hη0 (le_of_lt hθ))
    exact congrFun hβ m

/-! ### The energy perturbation -/

/-- The weighted square sum of the test sequence. -/
def Wc : ℝ := ∑' ℓ : ℤ, (1 + |(ℓ : ℝ)|) * ‖ArcSpace.cC ℓ‖ ^ 2

lemma Wc_nonneg : 0 ≤ Wc := tsum_nonneg (fun ℓ => by positivity)

/-- The perturbation bound (AM–GM split, valid for every `ε > 0`):
`|NQ(cC − f̂) − NQ(cC)| ≤ Cσ·(ε·Wc + (ε⁻¹ + 3)·CB·η^{3/4})`. -/
theorem NQ_perturb {a : ℝ} (ha : a ∈ Set.Ioo (0:ℝ) 1) (b : ℝ)
    (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) (ε : ℝ) (hε : 0 < ε) :
    |NQformArc a b (fun ℓ => ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ)
        - NQformArc a b ArcSpace.cC|
      ≤ (1 + b ^ 2 / min a (1 - a))
        * (ε * Wc + (ε⁻¹ + 3) * (CB * η ^ ((3:ℝ)/4))) := by
  set Cσ : ℝ := 1 + b ^ 2 / min a (1 - a) with hCσ
  have hm : 0 < min a (1 - a) := lt_min ha.1 (by linarith [ha.2])
  have hCσ0 : 0 < Cσ := by
    rw [hCσ]
    positivity
  have hwc : Summable (fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖ArcSpace.cC ℓ‖ ^ 2) :=
    (ArcSpace.mem_ArcDom.mp ArcSpace.cC_mem_ArcDom).1
  have hwf := summable_weighted η hη0 hη
  have hwψ := summable_weight_sub η hη0 hη
  have hSc := summable_sigmaArc_mul_sq ha b hwc
  have hSpsi := summable_sigmaArc_mul_sq ha b hwψ
  -- the difference series
  have hdiff : NQformArc a b (fun ℓ => ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ)
      - NQformArc a b ArcSpace.cC
      = ∑' ℓ : ℤ, (sigmaArc a b ℓ * ‖ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ‖ ^ 2
        - sigmaArc a b ℓ * ‖ArcSpace.cC ℓ‖ ^ 2) := by
    simp only [NQformArc]
    exact (hSpsi.tsum_sub hSc).symm
  rw [hdiff]
  -- termwise bound
  have hterm : ∀ ℓ : ℤ,
      |sigmaArc a b ℓ * ‖ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ‖ ^ 2
        - sigmaArc a b ℓ * ‖ArcSpace.cC ℓ‖ ^ 2|
      ≤ Cσ * (ε * ((1 + |(ℓ : ℝ)|) * ‖ArcSpace.cC ℓ‖ ^ 2)
        + (ε⁻¹ + 3) * ((1 + |(ℓ : ℝ)|) * ‖Parseval.fc (fJ η) ℓ‖ ^ 2)) := by
    intro ℓ
    set c := ArcSpace.cC ℓ
    set f := Parseval.fc (fJ η) ℓ
    have hσ := abs_sigmaArc_le ha b ℓ
    have hcn : (0:ℝ) ≤ ‖c‖ := norm_nonneg _
    have hfn : (0:ℝ) ≤ ‖f‖ := norm_nonneg _
    have hψn : (0:ℝ) ≤ ‖c - f‖ := norm_nonneg _
    have h1 : (0:ℝ) ≤ 1 + |(ℓ : ℝ)| := by positivity
    have htri1 : ‖c - f‖ ≤ ‖c‖ + ‖f‖ := norm_sub_le _ _
    have htri2 : ‖c‖ ≤ ‖c - f‖ + ‖f‖ := by
      have := norm_sub_le (c - f) (-f)
      simp only [sub_neg_eq_add, sub_add_cancel] at this
      calc ‖c‖ = ‖c - f + f‖ := by rw [sub_add_cancel]
        _ ≤ ‖c - f‖ + ‖f‖ := norm_add_le _ _
    -- |‖c−f‖² − ‖c‖²| ≤ 2‖c‖‖f‖ + 3‖f‖²
    have hval : |‖c - f‖ ^ 2 - ‖c‖ ^ 2| ≤ 2 * ‖c‖ * ‖f‖ + 3 * ‖f‖ ^ 2 := by
      rw [abs_le]
      constructor
      · nlinarith [htri2, hψn, hfn, hcn]
      · nlinarith [htri1, hψn, hfn, hcn]
    -- AM–GM: 2‖c‖‖f‖ ≤ ε‖c‖² + ε⁻¹‖f‖²
    have hamgm : 2 * ‖c‖ * ‖f‖ ≤ ε * ‖c‖ ^ 2 + ε⁻¹ * ‖f‖ ^ 2 := by
      have h := sq_nonneg (ε * ‖c‖ - ‖f‖)
      have hεi : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
      nlinarith [mul_pos hε hε, sq_nonneg (ε * ‖c‖ - ‖f‖),
        mul_le_mul_of_nonneg_left (sq_nonneg (ε * ‖c‖ - ‖f‖)) (inv_nonneg.mpr hε.le),
        hεi]
    calc |sigmaArc a b ℓ * ‖c - f‖ ^ 2 - sigmaArc a b ℓ * ‖c‖ ^ 2|
        = |sigmaArc a b ℓ| * |‖c - f‖ ^ 2 - ‖c‖ ^ 2| := by rw [← abs_mul, mul_sub]
      _ ≤ (Cσ * (1 + |(ℓ : ℝ)|)) * (2 * ‖c‖ * ‖f‖ + 3 * ‖f‖ ^ 2) := by
          refine mul_le_mul hσ hval (abs_nonneg _) ?_
          positivity
      _ ≤ (Cσ * (1 + |(ℓ : ℝ)|)) * (ε * ‖c‖ ^ 2 + ε⁻¹ * ‖f‖ ^ 2 + 3 * ‖f‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [hamgm]
      _ = Cσ * (ε * ((1 + |(ℓ : ℝ)|) * ‖c‖ ^ 2)
          + (ε⁻¹ + 3) * ((1 + |(ℓ : ℝ)|) * ‖f‖ ^ 2)) := by ring
  -- sum the termwise bound
  have hmaj : Summable (fun ℓ : ℤ =>
      Cσ * (ε * ((1 + |(ℓ : ℝ)|) * ‖ArcSpace.cC ℓ‖ ^ 2)
        + (ε⁻¹ + 3) * ((1 + |(ℓ : ℝ)|) * ‖Parseval.fc (fJ η) ℓ‖ ^ 2))) :=
    (((hwc.mul_left ε).add (hwf.mul_left (ε⁻¹ + 3))).mul_left Cσ)
  have hnorm_sum : Summable (fun ℓ : ℤ =>
      ‖sigmaArc a b ℓ * ‖ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ‖ ^ 2
        - sigmaArc a b ℓ * ‖ArcSpace.cC ℓ‖ ^ 2‖) := by
    refine Summable.of_nonneg_of_le (fun ℓ => norm_nonneg _) (fun ℓ => ?_) hmaj
    rw [Real.norm_eq_abs]
    exact hterm ℓ
  have habs := norm_tsum_le_tsum_norm (f := fun ℓ : ℤ =>
      sigmaArc a b ℓ * ‖ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ‖ ^ 2
        - sigmaArc a b ℓ * ‖ArcSpace.cC ℓ‖ ^ 2) hnorm_sum
  rw [Real.norm_eq_abs] at habs
  refine le_trans habs ?_
  have h2 := hnorm_sum.tsum_le_tsum (fun ℓ => by
    rw [Real.norm_eq_abs]
    exact hterm ℓ) hmaj
  refine le_trans h2 ?_
  -- evaluate: Σ Cσ(ε·wc + (ε⁻¹+3)·wf) = Cσ(ε·Wc + (ε⁻¹+3)·Σwf) ≤ Cσ(ε·Wc + (ε⁻¹+3)·CB·η^{3/4})
  rw [tsum_mul_left]
  refine mul_le_mul_of_nonneg_left ?_ hCσ0.le
  rw [((hwc.mul_left ε).tsum_add (hwf.mul_left (ε⁻¹ + 3)) :
    (∑' ℓ : ℤ, (ε * ((1 + |(ℓ : ℝ)|) * ‖ArcSpace.cC ℓ‖ ^ 2)
      + (ε⁻¹ + 3) * ((1 + |(ℓ : ℝ)|) * ‖Parseval.fc (fJ η) ℓ‖ ^ 2))) = _),
    tsum_mul_left, tsum_mul_left]
  refine add_le_add le_rfl ?_
  refine mul_le_mul_of_nonneg_left (budget_le η hη0 hη) ?_
  have : 0 < ε⁻¹ := inv_pos.mpr hε
  linarith

/-! ### The negative witness -/

/-- A negative-energy witness supported away from the junctions. For
`0 < a < 1` and `2 * a * (1 - a) ≤ b²` there is `η ∈ (0, 1/4]` with `fc (psiF η) ∈ MemArc` and
`NQformArc a b (fc (psiF η)) < 0`. -/
theorem exists_witness {a : ℝ} (ha : a ∈ Set.Ioo (0:ℝ) 1) {b : ℝ}
    (hb : 2 * (a * (1 - a)) ≤ b ^ 2) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/4 ∧ MemArc (Parseval.fc (psiF η))
      ∧ NQformArc a b (Parseval.fc (psiF η)) < 0 := by
  set Cσ : ℝ := 1 + b ^ 2 / min a (1 - a) with hCσdef
  have hm0 : 0 < min a (1 - a) := lt_min ha.1 (by linarith [ha.2])
  have hCσ0 : 0 < Cσ := by rw [hCσdef]; positivity
  set m : ℝ := -(NQformArc a b ArcSpace.cC) with hmdef
  have hmpos : 0 < m := by
    rw [hmdef, neg_pos]
    exact NQformArc_cC_neg ha hb
  set ε : ℝ := m / (2 * Cσ * (Wc + 1)) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    have := Wc_nonneg
    positivity
  set D : ℝ := Cσ * (ε⁻¹ + 3) * (CB + 1) with hDdef
  have hD0 : 0 < D := by
    rw [hDdef]
    have h1 : 0 < ε⁻¹ := inv_pos.mpr hε
    have h2 := CB_nonneg
    positivity
  set η : ℝ := min (1/4) ((m / (2 * D)) ^ ((4:ℝ)/3)) with hηdef
  have hX0 : (0:ℝ) < m / (2 * D) := by positivity
  have hη0 : 0 < η := by
    rw [hηdef]
    exact lt_min (by norm_num) (Real.rpow_pos_of_pos hX0 _)
  have hη14 : η ≤ 1/4 := min_le_left _ _
  refine ⟨η, hη0, hη14, memArc_psiF η hη0 hη14, ?_⟩
  -- the two strict halves
  have half1 : Cσ * (ε * Wc) < m / 2 := by
    have hWc := Wc_nonneg
    have heq : Cσ * (ε * Wc) = m * Wc / (2 * (Wc + 1)) := by
      rw [hεdef]
      have hW1 : Wc + 1 ≠ 0 := by linarith [Wc_nonneg]
      field_simp
    rw [heq, div_lt_iff₀ (by positivity)]
    nlinarith
  have half2 : Cσ * ((ε⁻¹ + 3) * (CB * η ^ ((3:ℝ)/4))) < m / 2 := by
    have hη34 : η ^ ((3:ℝ)/4) ≤ m / (2 * D) := by
      have h1 : η ≤ (m / (2 * D)) ^ ((4:ℝ)/3) := min_le_right _ _
      calc η ^ ((3:ℝ)/4) ≤ ((m / (2 * D)) ^ ((4:ℝ)/3)) ^ ((3:ℝ)/4) :=
            Real.rpow_le_rpow hη0.le h1 (by norm_num)
        _ = m / (2 * D) := by
            rw [← Real.rpow_mul hX0.le]
            norm_num
    have hcoef : 0 ≤ Cσ * (ε⁻¹ + 3) := by
      have : 0 < ε⁻¹ := inv_pos.mpr hε
      positivity
    have hCB := CB_nonneg
    calc Cσ * ((ε⁻¹ + 3) * (CB * η ^ ((3:ℝ)/4)))
        = (Cσ * (ε⁻¹ + 3) * CB) * η ^ ((3:ℝ)/4) := by ring
      _ ≤ (Cσ * (ε⁻¹ + 3) * CB) * (m / (2 * D)) := by
          refine mul_le_mul_of_nonneg_left hη34 (by positivity)
      _ < m / 2 := by
          rw [hDdef]
          have h1 : 0 < ε⁻¹ := inv_pos.mpr hε
          have hA : 0 < Cσ * (ε⁻¹ + 3) := by positivity
          have hCB1 : (0:ℝ) < CB + 1 := by linarith [CB_nonneg]
          have heq2 : Cσ * (ε⁻¹ + 3) * CB * (m / (2 * (Cσ * (ε⁻¹ + 3) * (CB + 1))))
              = m / 2 * (CB / (CB + 1)) := by
            field_simp

          rw [heq2]
          have hfrac : CB / (CB + 1) < 1 := by
            rw [div_lt_one hCB1]
            linarith [CB_nonneg]
          calc m / 2 * (CB / (CB + 1)) < m / 2 * 1 :=
                mul_lt_mul_of_pos_left hfrac (by positivity)
            _ = m / 2 := mul_one _
  -- assemble
  have hpert := NQ_perturb ha b η hη0 hη14 ε hε
  rw [fc_psiF_funext η]
  have habs := abs_le.mp hpert
  have hNQc : NQformArc a b ArcSpace.cC = -m := by rw [hmdef]; ring
  have hbound : NQformArc a b (fun ℓ => ArcSpace.cC ℓ - Parseval.fc (fJ η) ℓ)
      ≤ NQformArc a b ArcSpace.cC
        + Cσ * (ε * Wc + (ε⁻¹ + 3) * (CB * η ^ ((3:ℝ)/4))) := by
    linarith [habs.2]
  have hfin : Cσ * (ε * Wc + (ε⁻¹ + 3) * (CB * η ^ ((3:ℝ)/4))) < m := by
    have hexp : Cσ * (ε * Wc + (ε⁻¹ + 3) * (CB * η ^ ((3:ℝ)/4)))
        = Cσ * (ε * Wc) + Cσ * ((ε⁻¹ + 3) * (CB * η ^ ((3:ℝ)/4))) := by ring
    rw [hexp]
    linarith [half1, half2]
  rw [hNQc] at hbound
  linarith [hbound, hfin]

end KsIndex.ArcWitness
