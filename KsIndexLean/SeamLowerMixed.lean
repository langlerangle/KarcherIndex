module

/-
# Mixed seam index counts

For `k ≥ 3` and `1 ≤ r ≤ k - 1`, this file proves that each of the two
mixed natural seam domains has index one.

The lower bound starts with the negative arc witness supplied by
`ArcWitness.exists_witness`. It fixes an angular separation margin using
`c = η / 8` and `δ₀ = 1 / (8k)`, then chooses a collar width `δ` and a
Fourier truncation size `N`. The truncation preserves a fixed negative
energy margin while making the coefficient tail smaller than `δ`.

The uniform disk bounds and the collar value estimate control the cost
of multiplying by the slit cutoff. Although the cutoff derivative grows
like `1 / δ`, the witness is bounded by a constant times `δ` on the
collar. Their product remains bounded independently of `δ`, and the
collar area makes the total energy perturbation at most `K * δ`.
Choosing `δ` sufficiently small therefore gives a negative test function
in the mixed domain and an index lower bound of one.

Combining this with `TraceArc.seamNat_mixed_le_one` gives the exact count.
The screw congruence transfers it to the other mixed domain.
-/
public import KsIndexLean.CollarValue
public import KsIndexLean.PsiCut
public import KsIndexLean.SlitMargin
public import KsIndexLean.ModeGrad
public import KsIndexLean.CollarBound
public import KsIndexLean.SeamLower
public import KsIndexLean.TraceArc

@[expose] public section


noncomputable section

open Real Set Filter Complex MeasureTheory
open KsIndex.ArcField KsIndex.ArcForm KsIndex.ArcLower KsIndex.ArcTrunc KsIndex.ArcSmooth
  KsIndex.ArcPoisson KsIndex.ArcInfCoeff KsIndex.ModeWitness KsIndex.ModePoisson
  KsIndex.ModeGrad KsIndex.ModeSeries KsIndex.CollarValue KsIndex.PsiCut KsIndex.SlitMargin
  KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.Surface KsIndex.SurfaceForm
  KsIndex.CutoffContinuity KsIndex.CollarBound KsIndex.Radial KsIndex.FormIndex
  KsIndex.PunctureCutoff

namespace KsIndex.SeamLowerMixed

variable {k r : ℕ}

/-! ### The `ℓ¹` tail is eventually small -/

/-- The subtype-complement tail equals the symmetric-window indicator tail. -/
lemma tailCompl_eq_indicator (η : ℝ) (N : ℕ) :
    (∑' n : ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ),
        ‖Parseval.fc (psiF η) (n : ℤ)‖)
      = ∑' ℓ : ℤ, if |ℓ| ≤ (N : ℤ) then (0:ℝ) else ‖Parseval.fc (psiF η) ℓ‖ := by
  refine Eq.trans (tsum_subtype ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ)
    (fun ℓ : ℤ => ‖Parseval.fc (psiF η) ℓ‖)) ?_
  refine tsum_congr (fun ℓ => ?_)
  by_cases h : |ℓ| ≤ (N : ℤ)
  · have hmem : ℓ ∈ (↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ) := by
      rw [Finset.mem_coe, Finset.mem_Icc]
      exact abs_le.mp h
    have hnot : ℓ ∉ ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ) := by
      rw [Set.mem_compl_iff, not_not]
      exact hmem
    rw [if_pos h, Set.indicator_of_notMem hnot]
  · have hmem : ℓ ∈ ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ) := by
      intro hcon
      rw [Finset.mem_coe, Finset.mem_Icc] at hcon
      exact h (abs_le.mpr hcon)
    rw [if_neg h, Set.indicator_of_mem hmem]

/-- The `ℓ¹` truncation tail is eventually below any `ε > 0`. -/
lemma eventually_tailCompl_lt {η : ℝ} (hη0 : 0 < η) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑' n : ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ),
        ‖Parseval.fc (psiF η) (n : ℤ)‖) < ε := by
  have hgen := tendsto_tail_indicator (w := fun ℓ : ℤ => ‖Parseval.fc (psiF η) ℓ‖)
    (fun ℓ => norm_nonneg _) (summable_fc_psiF η hη0)
  filter_upwards [hgen.eventually_lt_const hε] with N hN
  rw [tailCompl_eq_indicator η N]
  exact hN

/-! ### Truncation preserves a negative energy margin -/

/-- `NQ(trunc N t)` is eventually `< NQ(t)/2` (persistent negativity). -/
lemma eventually_NQ_trunc_lt {a : ℝ} (ha : a ∈ Set.Ioo (0:ℝ) 1) (b : ℝ) {t : ℤ → ℂ}
    (hw : Summable (fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖t ℓ‖ ^ 2))
    (hneg : NQformArc a b t < 0) :
    ∀ᶠ N : ℕ in atTop, NQformArc a b (trunc N t) < NQformArc a b t / 2 := by
  obtain ⟨C, hC0, hkey⟩ := exists_NQ_trunc_perturb ha b hw
  have hCne : C ≠ 0 := hC0.ne'
  set m : ℝ := -(NQformArc a b t) with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have hev := (tendsto_tailW hw).eventually_lt_const
    (show (0:ℝ) < m / (2 * C) from div_pos hm0 (by linarith))
  filter_upwards [hev] with N hN
  have h1 : NQformArc a b t - NQformArc a b (trunc N t) ≥ -(C * tailW N t) :=
    (abs_le.mp (hkey N)).1
  have h2 : C * tailW N t < m / 2 := by
    calc C * tailW N t < C * (m / (2 * C)) := mul_lt_mul_of_pos_left hN hC0
      _ = m / 2 := by field_simp
  have hval : NQformArc a b t = -m := by rw [hm]; ring
  linarith

/-- A division identity used in the collar estimate. -/
private lemma two_div_helper (a X : ℝ) (hX : X ≠ 0) : 2*a/(2*X) = a * (1/X) := by
  field_simp

/-! ### The mixed seam index lower bound -/

/-- **`1 ≤ seamNat k true false r`** — the mixed-cell index lower bound: the witness construction
(arc coefficients → disk modes → Poisson collar control → slit cut) assembled through
`Qd_cut_collar` under the coupled `δ–N` limit. -/
theorem one_le_seamNat_mixed (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) :
    1 ≤ seamNat k true false r := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hk0R : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1R : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hk3R : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  -- ═══ stage 1: the arc witness ═══
  have ha : aOf r k ∈ Set.Ioo (0:ℝ) 1 := aOf_mem hk hr1 hrk
  have hb2 : 2 * (aOf r k * (1 - aOf r k)) ≤ bOf k ^ 2 := two_mul_aOf_le hk hr1 hrk
  obtain ⟨η, hη0, hη14, hmem, hneg⟩ := KsIndex.ArcWitness.exists_witness ha hb2
  set t : ℤ → ℂ := Parseval.fc (psiF η) with ht
  set m₀ : ℝ := -(NQformArc (aOf r k) (bOf k) t) with hm₀
  have hm₀0 : 0 < m₀ := by rw [hm₀]; linarith
  -- ═══ stage 2: fixed margin data ═══
  set c : ℝ := η / 8 with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  set δ₀ : ℝ := 1 / (8 * (k:ℝ)) with hδ₀def
  have hδ₀0 : 0 < δ₀ := by rw [hδ₀def]; positivity
  have hkne : (k:ℝ) ≠ 0 := hk0R.ne'
  have hδ₀k : 2 * (k:ℝ) * δ₀ = 1/4 := by
    rw [hδ₀def, mul_one_div, div_eq_div_iff (by linarith) (by norm_num)]
    ring
  have hδ₀small : δ₀ ≤ 1/24 := by
    rw [hδ₀def, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hδ₀half : 0 < 1 - 2*δ₀ := by linarith
  have hBern : (1/2 : ℝ) ≤ (1 - 2*δ₀)^k := by
    have hb := one_add_mul_le_pow (show (-2:ℝ) ≤ -(2*δ₀) by nlinarith) k
    have h1 : (1:ℝ) + (k:ℝ) * (-(2*δ₀)) = 3/4 := by
      have := hδ₀k
      nlinarith
    have h2 : (1:ℝ) + (-(2*δ₀)) = 1 - 2*δ₀ := by ring
    rw [h1, h2] at hb
    linarith
  have hpow₀ : (0:ℝ) < (1 - 2*δ₀)^k := pow_pos hδ₀half k
  set A₀ : ℝ := 2 * c / (1 - 2*δ₀)^k with hA₀def
  have hA₀0 : 0 ≤ A₀ := by
    rw [hA₀def]
    exact div_nonneg (by linarith) hpow₀.le
  have hA₀η : A₀ < η := by
    rw [hA₀def, div_lt_iff₀ hpow₀, hcdef]
    nlinarith [hBern, hη0]
  set d₀ : ℝ := (η - A₀) / (k:ℝ) with hd₀def
  have hd₀0 : 0 < d₀ := by
    rw [hd₀def]
    exact div_pos (by linarith) hk0R
  have hd₀π : d₀ ≤ π := by
    have h1 : d₀ ≤ η - A₀ := by
      rw [hd₀def]
      exact div_le_self (by linarith) hk1R
    linarith [Real.pi_gt_three, hη14, hA₀0]
  have hcosd₀ : Real.cos d₀ < 1 := cos_lt_one_of_pos_le_pi hd₀0 hd₀π
  have hcosd₀' : 0 < 1 - Real.cos d₀ := by linarith
  have hsq₀ : 0 < Real.sqrt (1 - 2*δ₀) := Real.sqrt_pos.mpr hδ₀half
  -- ═══ stage 3: N-uniform disk bounds, masses, constants ═══
  obtain ⟨Mη, Dη, hMη0, hDη0, hMηb, hDηb⟩ := Psi_disk_bounds hk hr1 hrk hη0
  set T : ℝ := ∑' n : ℤ, ‖t n‖ with hT
  have hT0 : 0 ≤ T := tsum_nonneg (fun n => norm_nonneg _)
  have hκ0 : 0 ≤ kap k := (kap_pos hk2).le
  have h2k2 : (0:ℝ) ≤ 2*(k:ℝ) - 2 := by linarith
  set Cm : ℝ := 1/(Real.sqrt (1 - 2*δ₀) * (1 - Real.cos d₀)) + 1
      + kap k * (2*(k:ℝ)-2) * 2 * T with hCmdef
  have hCm0 : 0 ≤ Cm := by
    rw [hCmdef]
    have h1 : (0:ℝ) ≤ 1/(Real.sqrt (1 - 2*δ₀) * (1 - Real.cos d₀)) :=
      le_of_lt (div_pos one_pos (mul_pos hsq₀ hcosd₀'))
    have h2 : (0:ℝ) ≤ kap k * (2*(k:ℝ)-2) * 2 * T := by
      have := mul_nonneg (mul_nonneg (mul_nonneg hκ0 h2k2) (by norm_num : (0:ℝ) ≤ 2)) hT0
      linarith only [this]
    linarith only [h1, h2]
  set MG : ℝ := Cm * (8 * Mψ + 2*(k:ℝ)*Mψ*δ₀/c) with hMGdef
  have hMG0 : 0 ≤ MG := by
    rw [hMGdef]
    have h2 : (0:ℝ) ≤ 2*(k:ℝ)*Mψ*δ₀/c :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith only [hk0R] : (0:ℝ) ≤ 2*(k:ℝ))
        Mψ_nonneg) hδ₀0.le) hc0.le
    have h1 : (0:ℝ) ≤ 8 * Mψ + 2*(k:ℝ)*Mψ*δ₀/c := by
      have := Mψ_nonneg
      linarith only [this, h2]
    exact mul_nonneg hCm0 h1
  set K : ℝ := 4 * π * (2*Dη*(Dη + MG) + MG*(Dη + MG)
      + 8*((k:ℝ)-1)^2 * (Cm*δ₀) * Mη) with hKdef
  have hKinner0 : (0:ℝ) ≤ 2*Dη*(Dη + MG) + MG*(Dη + MG) + 8*((k:ℝ)-1)^2 * (Cm*δ₀) * Mη := by
    have h1 : (0:ℝ) ≤ Dη + MG := by linarith only [hDη0, hMG0]
    have h2 : (0:ℝ) ≤ 2*Dη*(Dη + MG) :=
      mul_nonneg (mul_nonneg (by norm_num) hDη0) h1
    have h3 : (0:ℝ) ≤ MG*(Dη + MG) := mul_nonneg hMG0 h1
    have h4 : (0:ℝ) ≤ 8*((k:ℝ)-1)^2 * (Cm*δ₀) * Mη := by
      have := mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 8*((k:ℝ)-1)^2)
        (mul_nonneg hCm0 hδ₀0.le)) hMη0
      linarith only [this]
    linarith only [h2, h3, h4]
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have := mul_nonneg (by positivity : (0:ℝ) ≤ 4*π) hKinner0
    linarith only [this]
  -- ═══ stage 4: choose δ, then N ═══
  set δ : ℝ := min δ₀ (π*(k:ℝ)*m₀/(2*(K+1))) with hδdef
  have hδ0 : 0 < δ := lt_min hδ₀0
    (div_pos (mul_pos (mul_pos Real.pi_pos hk0R) hm₀0) (by linarith only [hK0]))
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδK : (K+1)*δ ≤ π*(k:ℝ)*m₀/2 := by
    have h1 : δ ≤ π*(k:ℝ)*m₀/(2*(K+1)) := min_le_right _ _
    have h2 : (0:ℝ) < K+1 := by linarith only [hK0]
    calc (K+1)*δ ≤ (K+1)*(π*(k:ℝ)*m₀/(2*(K+1))) :=
          mul_le_mul_of_nonneg_left h1 h2.le
      _ = π*(k:ℝ)*m₀/2 := by field_simp
  have hδhalf : 0 < 1 - 2*δ := by linarith only [hδδ₀, hδ₀small, hδ0]
  have hδq : δ ≤ 1/2 := by linarith only [hδδ₀, hδ₀small]
  obtain ⟨N, hN1, hN2⟩ := ((eventually_NQ_trunc_lt ha (bOf k) hmem.1 hneg).and
    (eventually_tailCompl_lt hη0 hδ0)).exists
  -- ═══ stage 5: the collar smallness ═══
  set mδ : ℝ := Cm * δ with hmδdef
  have hmδ0 : 0 ≤ mδ := mul_nonneg hCm0 hδ0.le
  have hm : ∀ w ∈ disk ∩ cutS k δ c, ‖Psi k r N t w‖ ≤ mδ := by
    rintro w ⟨hwd, hwS⟩
    have hw1 : ‖w‖ < 1 := mem_disk_iff.mp hwd
    obtain ⟨hwlow', hwk⟩ := hwS
    have hwlow : 1 - 2*δ ≤ ‖w‖^2 := by rw [norm_sq_eq]; exact hwlow'
    have hmargin : ∀ φ, fInf k r η φ ≠ 0 →
        Real.cos (Complex.arg w - φ) ≤ Real.cos d₀ := by
      intro φ hφ
      have hα1 := cos_k_arg_le hk1 hc0.le hδhalf hwlow hw1.le hwk
      have hα : Real.cos ((k:ℝ) * Complex.arg w) ≤ A₀ := by
        refine le_trans hα1 ?_
        rw [hA₀def]
        refine div_le_div_of_nonneg_left (by linarith only [hc0]) hpow₀ ?_
        exact pow_le_pow_left₀ hδ₀half.le (by linarith only [hδδ₀]) k
      rw [hd₀def]
      exact cos_margin hk1 hA₀η hα (fInf_supp_cos hη0 hφ)
    refine le_trans (collar_value_bound hk hr1 hrk hη0 hδhalf N hd₀0 hd₀π hwlow hw1 hmargin) ?_
    -- the three collar terms sum to at most `Cm·δ`
    have hsqle : Real.sqrt (1 - 2*δ₀) ≤ Real.sqrt (1 - 2*δ) :=
      Real.sqrt_le_sqrt (by linarith only [hδδ₀])
    have ht1 : 2*δ/(2*Real.sqrt (1 - 2*δ)*(1 - Real.cos d₀))
        ≤ δ * (1/(Real.sqrt (1 - 2*δ₀)*(1 - Real.cos d₀))) := by
      have hden₀ : (0:ℝ) < Real.sqrt (1 - 2*δ₀)*(1 - Real.cos d₀) := mul_pos hsq₀ hcosd₀'
      have hdenle : 2*(Real.sqrt (1 - 2*δ₀)*(1 - Real.cos d₀))
          ≤ 2*Real.sqrt (1 - 2*δ)*(1 - Real.cos d₀) := by
        have h := mul_le_mul_of_nonneg_right hsqle hcosd₀'.le
        linarith only [h]
      calc 2*δ/(2*Real.sqrt (1 - 2*δ)*(1 - Real.cos d₀))
          ≤ 2*δ/(2*(Real.sqrt (1 - 2*δ₀)*(1 - Real.cos d₀))) :=
            div_le_div_of_nonneg_left (mul_pos two_pos hδ0).le
              (mul_pos two_pos hden₀) hdenle
        _ = δ * (1/(Real.sqrt (1 - 2*δ₀)*(1 - Real.cos d₀))) :=
            two_div_helper δ _ hden₀.ne'
    have ht3 : kap k * (2*(k:ℝ)-2) * (2*δ) * T
        = δ * (kap k * (2*(k:ℝ)-2) * 2 * T) := by ring
    rw [hmδdef, hCmdef]
    linarith only [ht1, ht3, hN2.le]
  -- ═══ stage 6: the collar perturbation and the K·δ bound ═══
  set Gδ : ℝ := 8*Mψ/δ + 2*(k:ℝ)*Mψ/c with hGδdef
  have hMψ0 : (0:ℝ) ≤ Mψ := Mψ_nonneg
  have hGδ0 : 0 ≤ Gδ := by
    rw [hGδdef]
    have h1 : (0:ℝ) ≤ 8*Mψ/δ := div_nonneg (by linarith only [hMψ0]) hδ0.le
    have h2 : (0:ℝ) ≤ 2*(k:ℝ)*Mψ/c :=
      div_nonneg (mul_nonneg (by linarith only [hk0R] : (0:ℝ) ≤ 2*(k:ℝ)) hMψ0) hc0.le
    linarith only [h1, h2]
  have hG : ∀ w ∈ disk ∩ cutS k δ c,
      |fderiv ℝ (cutSlit k δ c) w 1| + |fderiv ℝ (cutSlit k δ c) w I| ≤ Gδ := by
    rintro w ⟨hwd, -⟩
    rw [hGδdef]
    exact cutSlit_grad_bound hδ0 hc0 (mem_disk_iff.mp hwd).le
  have hpert := Qd_cut_collar hk2 (measurableSet_cutS k δ c)
    (fun w => ((contDiff_cutSlit k δ c).differentiable (by simp)).differentiableAt)
    (fun w => (cutSlit_mem_Icc k δ c w).1) (fun w => (cutSlit_mem_Icc k δ c w).2)
    (fun w _ hw => cutSlit_off_S hδ0 hc0 hw)
    hmδ0 hGδ0
    (fun w _ => ((contDiff_Psi k r N t).differentiable (by simp)).differentiableAt)
    (fun w hw => hMηb N w (mem_disk_iff.mp hw).le)
    (fun w hw => hDηb N w (mem_disk_iff.mp hw).le)
    hm hG
  -- `mδ·Gδ ≤ MG` (the δ cancels)
  have hmG : mδ * Gδ ≤ MG := by
    rw [hmδdef, hGδdef, hMGdef]
    have hδne : δ ≠ 0 := hδ0.ne'
    have hcne : c ≠ 0 := hc0.ne'
    have hkey : Cm*δ*(8*Mψ/δ + 2*(k:ℝ)*Mψ/c) = Cm*(8*Mψ + 2*(k:ℝ)*Mψ*δ/c) := by
      field_simp
    rw [hkey]
    have hmono : 2*(k:ℝ)*Mψ*δ/c ≤ 2*(k:ℝ)*Mψ*δ₀/c := by
      refine div_le_div_of_nonneg_right ?_ hc0.le
      exact mul_le_mul_of_nonneg_left hδδ₀
        (mul_nonneg (by linarith only [hk0R]) hMψ0)
    exact mul_le_mul_of_nonneg_left (by linarith only [hmono]) hCm0
  have hvol := volume_real_cutS_le (k := k) (c := c) hδ0 hδq
  have hvol0 : (0:ℝ) ≤ (volume : MeasureTheory.Measure ℂ).real (disk ∩ cutS k δ c) := by
    positivity
  -- the perturbation is at most `K·δ`
  have hRHS : 2 * (2 * (Dη * (Dη + mδ * Gδ)) + Gδ * (mδ * (Dη + mδ * Gδ))
        + 8 * ((k:ℝ) - 1) ^ 2 * (mδ * Mη))
      * (volume : MeasureTheory.Measure ℂ).real (disk ∩ cutS k δ c) ≤ K * δ := by
    have hfac : Dη + mδ * Gδ ≤ Dη + MG := by linarith only [hmG]
    have hfac0 : (0:ℝ) ≤ Dη + mδ * Gδ := by
      have := mul_nonneg hmδ0 hGδ0
      linarith only [this, hDη0]
    have h1 : Dη * (Dη + mδ * Gδ) ≤ Dη * (Dη + MG) :=
      mul_le_mul_of_nonneg_left hfac hDη0
    have h2 : Gδ * (mδ * (Dη + mδ * Gδ)) ≤ MG * (Dη + MG) := by
      have hGm : Gδ * mδ ≤ MG := by rw [mul_comm]; exact hmG
      calc Gδ * (mδ * (Dη + mδ * Gδ)) = (Gδ * mδ) * (Dη + mδ * Gδ) := by ring
        _ ≤ MG * (Dη + MG) :=
            mul_le_mul hGm hfac hfac0 hMG0
    have h3 : 8 * ((k:ℝ) - 1) ^ 2 * (mδ * Mη)
        ≤ 8 * ((k:ℝ) - 1) ^ 2 * ((Cm * δ₀) * Mη) := by
      have hmδ₀ : mδ ≤ Cm * δ₀ := by
        rw [hmδdef]
        exact mul_le_mul_of_nonneg_left hδδ₀ hCm0
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hmδ₀ hMη0)
        (by positivity : (0:ℝ) ≤ 8*((k:ℝ)-1)^2)
    have hinner : 2 * (Dη * (Dη + mδ * Gδ)) + Gδ * (mδ * (Dη + mδ * Gδ))
        + 8 * ((k:ℝ) - 1) ^ 2 * (mδ * Mη)
        ≤ 2*Dη*(Dη + MG) + MG*(Dη + MG) + 8*((k:ℝ)-1)^2 * (Cm*δ₀) * Mη := by
      linarith only [h1, h2, h3]
    have hinner0 : (0:ℝ) ≤ 2 * (Dη * (Dη + mδ * Gδ)) + Gδ * (mδ * (Dη + mδ * Gδ))
        + 8 * ((k:ℝ) - 1) ^ 2 * (mδ * Mη) := by
      have ha1 : (0:ℝ) ≤ Dη * (Dη + mδ * Gδ) := mul_nonneg hDη0 hfac0
      have ha2 : (0:ℝ) ≤ Gδ * (mδ * (Dη + mδ * Gδ)) :=
        mul_nonneg hGδ0 (mul_nonneg hmδ0 hfac0)
      have ha3 : (0:ℝ) ≤ 8 * ((k:ℝ) - 1) ^ 2 * (mδ * Mη) :=
        mul_nonneg (by positivity) (mul_nonneg hmδ0 hMη0)
      linarith only [ha1, ha2, ha3]
    calc 2 * (2 * (Dη * (Dη + mδ * Gδ)) + Gδ * (mδ * (Dη + mδ * Gδ))
          + 8 * ((k:ℝ) - 1) ^ 2 * (mδ * Mη))
        * (volume : MeasureTheory.Measure ℂ).real (disk ∩ cutS k δ c)
        ≤ 2 * (2*Dη*(Dη + MG) + MG*(Dη + MG) + 8*((k:ℝ)-1)^2 * (Cm*δ₀) * Mη)
          * (2 * π * δ) := by
          refine mul_le_mul (by linarith only [hinner]) hvol hvol0 (by linarith only [hKinner0])
      _ = K * δ := by rw [hKdef]; ring
  -- ═══ stage 7: negativity of the cut witness ═══
  have hQdPsi : Qd k (Psi k r N t) ≤ -(π*(k:ℝ)*m₀) := by
    rw [Qd_Psi_eq hk hr1 hrk N t]
    have h1 : NQformArc (aOf r k) (bOf k) (trunc N t) ≤ -(m₀/2) := by
      have h2 : NQformArc (aOf r k) (bOf k) t = -m₀ := by rw [hm₀]; ring
      rw [h2] at hN1
      linarith only [hN1]
    have h2 : (k:ℝ) * NQformArc (aOf r k) (bOf k) (trunc N t)
        ≤ (k:ℝ) * (-(m₀/2)) := mul_le_mul_of_nonneg_left h1 hk0R.le
    calc 2 * π * ((k:ℝ) * NQformArc (aOf r k) (bOf k) (trunc N t))
        ≤ 2 * π * ((k:ℝ) * (-(m₀/2))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = -(π*(k:ℝ)*m₀) := by ring
  have hQdW : Qd k (psiCut k r N t δ c) < 0 := by
    rw [Qd_psiCut_eq]
    have habs := (abs_le.mp (le_trans hpert hRHS)).2
    have hKδ : K*δ ≤ π*(k:ℝ)*m₀/2 := by linarith only [hδK, hδ0.le]
    have hπk : (0:ℝ) < π*(k:ℝ)*m₀ := mul_pos (mul_pos Real.pi_pos hk0R) hm₀0
    linarith only [habs, hQdPsi, hKδ, hπk]
  -- ═══ stage 8: the form-index lower bound ═══
  rw [seamNat]
  refine formIndex_ge_of_neg (KsIndex.SingleDisk.Qd_zero k)
    (fun _ : Fin 1 => psiCut k r N t δ c)
    (fun _ => psiCut_mem hk hr1 hrk N t hδ0 hc0) ?_
  intro cvec hcvec
  rw [Fin.sum_univ_one]
  have hc00 : cvec 0 ≠ 0 := by
    intro h0
    exact hcvec (funext (fun i => by fin_cases i; exact h0))
  rw [KsIndex.PsiCut.Qd_smul]
  have : (0:ℝ) < ‖cvec 0‖^2 := pow_pos (norm_pos_iff.mpr hc00) 2
  exact mul_neg_of_pos_of_neg this hQdW

/-! ### The mixed seam counts -/

/-- The mixed seam count `seamNat k true false r = 1` for `k ≥ 3`, `1 ≤ r ≤ k−1`:
the lower bound (`one_le_seamNat_mixed`) meets the upper bound
(`TraceArc.seamNat_mixed_le_one`). -/
theorem seamNat_mixed_eq_one (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) :
    seamNat k true false r = 1 :=
  le_antisymm (KsIndex.TraceArc.seamNat_mixed_le_one hk (by omega) hr1 hrk)
    (one_le_seamNat_mixed hk hr1 hrk)

/-- The other mixed cell, by the screw congruence (`seamNat_mixed`). -/
theorem seamNat_mixed_eq_one' (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) :
    seamNat k false true r = 1 := by
  rw [seamNat_mixed (by omega : 2 ≤ k) r]
  exact seamNat_mixed_eq_one hk hr1 hrk

end KsIndex.SeamLowerMixed
