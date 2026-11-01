module

/-
Poisson series on the character-frequency lattice and its truncation bound.

For `k ≥ 3`, `hasSum_poissonExt_fInf` reindexes the integer Fourier expansion of
`fInf k r η` along the injective map `lz k r`. Its frequencies are
`k*n + ↑(k-r)`, where `k-r` is natural-number subtraction. The theorem allows
arbitrary `r : ℕ` and `η : ℝ` and applies at each point of the open unit disk:

  `poissonExt (fInf k r η) w = Σ'_n fc (psiF η) n • baseMode k r n w`.

The proof combines the general Poisson expansion with `coeff_fInf_eq`: coefficients
vanish off this progression, and `baseMode_polar` identifies the remaining terms.
`Hpart_eq_sum_Icc` identifies the finite harmonic part with the sum over `[-N,N]`.

For `η > 0`, summability of the coefficients gives a truncation-error bound by
their `ℓ¹`-tail outside `[-N,N]`. The bound is independent of the point `w` in the
open disk. Although the termwise monomial bound also holds on the closed disk,
the Poisson-extension identity and truncation theorem here assume `‖w‖ < 1`;
no boundary-value conclusion is asserted.
-/
public import KsIndexLean.ModePoissonBridge
public import KsIndexLean.ArcPoissonSeries
public import KsIndexLean.ArcInfCoeff
public import KsIndexLean.ArcSmooth

@[expose] public section


noncomputable section

open Real Set Filter Topology Complex
open KsIndex.ArcField KsIndex.ArcPoisson KsIndex.ArcPoissonSeries KsIndex.ArcInfCoeff
  KsIndex.ModeWitness KsIndex.ModePoisson KsIndex.ModePoissonBridge

namespace KsIndex.ModeSeries

variable {k r : ℕ}

/-- On the open disk, the Poisson extension of `fInf` is the mode sum over the
frequency progression. This identity allows arbitrary `η : ℝ`. -/
theorem hasSum_poissonExt_fInf (hk : 3 ≤ k) (η : ℝ) {w : ℂ} (hw1 : ‖w‖ < 1) :
    HasSum (fun n : ℤ => Parseval.fc (psiF η) n • baseMode k r n w)
      (poissonExt (fInf k r η) w) := by
  have hk1 : 1 ≤ k := by omega
  have hA1 := hasSum_poissonExt (continuous_fInf k r η) (norm_fInf_le_one k r η) hw1
  -- substitute the Fourier coefficient formula
  have hA1' : HasSum (fun m : ℤ => ((‖w‖ ^ m.natAbs : ℝ) : ℂ)
      * Complex.exp (↑m * ↑(Complex.arg w) * Complex.I)
      * (if (k : ℤ) ∣ (m - ((k - r : ℕ) : ℤ))
          then Parseval.fc (psiF η) ((m - ((k - r : ℕ) : ℤ)) / (k : ℤ)) else 0))
      (poissonExt (fInf k r η) w) := by
    refine hA1.congr_fun (fun m => ?_)
    rw [← coeff_fInf_eq hk1 η m]
    push_cast
    ring
  -- the summand vanishes off the progression
  have hsupp : ∀ m : ℤ, m ∉ Set.range (lz k r) →
      (((‖w‖ ^ m.natAbs : ℝ) : ℂ)
        * Complex.exp (↑m * ↑(Complex.arg w) * Complex.I)
        * (if (k : ℤ) ∣ (m - ((k - r : ℕ) : ℤ))
            then Parseval.fc (psiF η) ((m - ((k - r : ℕ) : ℤ)) / (k : ℤ)) else 0)) = 0 := by
    intro m hm
    rw [if_neg, mul_zero]
    intro hdvd
    obtain ⟨j, hj⟩ := hdvd
    exact hm ⟨j, by unfold lz; linear_combination -hj⟩
  -- reindex along the injection `lz`
  have hre := ((lz_injective (k := k) (r := r) hk).hasSum_iff hsupp).mpr hA1'
  refine hre.congr_fun (fun n => ?_)
  simp only [Function.comp]
  have hdvd : (k : ℤ) ∣ (lz k r n - ((k - r : ℕ) : ℤ)) :=
    ⟨n, by unfold lz; ring⟩
  rw [if_pos hdvd,
    show (lz k r n - ((k - r : ℕ) : ℤ)) / (k : ℤ) = n from by
      rw [show lz k r n - ((k - r : ℕ) : ℤ) = (k : ℤ) * n from by unfold lz; ring]
      exact Int.mul_ediv_cancel_left n (Int.natCast_ne_zero.mpr (by omega)),
    smul_eq_mul, baseMode_polar]
  ring

/-- `Hpart` is the `Icc (−N) N` partial sum of the mode series. -/
lemma Hpart_eq_sum_Icc (k r N : ℕ) (t : ℤ → ℂ) (w : ℂ) :
    Hpart k r N t w = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), t n • baseMode k r n w := by
  unfold Hpart
  refine Finset.sum_nbij' (i := slot N)
    (j := fun ℓ => ⟨min (ℓ + N).toNat (2 * N), by omega⟩)
    (fun i _ => ?_) (fun ℓ hℓ => Finset.mem_univ _) (fun i _ => ?_) (fun ℓ hℓ => ?_)
    (fun i _ => rfl)
  · rw [Finset.mem_Icc]
    unfold slot
    omega
  · unfold slot
    apply Fin.ext
    simp only []
    omega
  · rw [Finset.mem_Icc] at hℓ
    unfold slot
    simp only []
    omega

/-- For `η > 0`, the truncation error on the open disk is bounded by the coefficient
`ℓ¹`-tail outside `[-N,N]`. The right-hand side is independent of the interior point. -/
theorem norm_poissonExt_fInf_sub_Hpart (hk : 3 ≤ k) {η : ℝ} (hη0 : 0 < η) (N : ℕ)
    {w : ℂ} (hw1 : ‖w‖ < 1) :
    ‖poissonExt (fInf k r η) w - Hpart k r N (Parseval.fc (psiF η)) w‖
      ≤ ∑' n : ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ),
          ‖Parseval.fc (psiF η) (n : ℤ)‖ := by
  have hA3 := hasSum_poissonExt_fInf (r := r) hk η hw1
  have hsummable : Summable (fun n : ℤ => Parseval.fc (psiF η) n • baseMode k r n w) :=
    hA3.summable
  have hsplit := hsummable.sum_add_tsum_compl (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
  rw [hA3.tsum_eq] at hsplit
  rw [Hpart_eq_sum_Icc, ← hsplit, add_sub_cancel_left]
  -- termwise domination on the closed disk
  have hterm : ∀ n : ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ),
      ‖Parseval.fc (psiF η) (n : ℤ) • baseMode k r (n : ℤ) w‖
        ≤ ‖Parseval.fc (psiF η) (n : ℤ)‖ := by
    intro n
    rw [norm_smul, norm_baseMode]
    calc ‖Parseval.fc (psiF η) (n : ℤ)‖ * ‖w‖ ^ (lz k r (n : ℤ)).natAbs
        ≤ ‖Parseval.fc (psiF η) (n : ℤ)‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg w) hw1.le) (norm_nonneg _)
      _ = ‖Parseval.fc (psiF η) (n : ℤ)‖ := mul_one _
  have hsub_summable : Summable (fun n : ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ) =>
      ‖Parseval.fc (psiF η) (n : ℤ)‖) :=
    (KsIndex.ArcSmooth.summable_fc_psiF η hη0).subtype _
  have hnorm_summable : Summable
      (fun n : ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ) =>
        ‖Parseval.fc (psiF η) (n : ℤ) • baseMode k r (n : ℤ) w‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsub_summable
  calc ‖∑' n : ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ),
        Parseval.fc (psiF η) (n : ℤ) • baseMode k r (n : ℤ) w‖
      ≤ ∑' n : ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ),
          ‖Parseval.fc (psiF η) (n : ℤ) • baseMode k r (n : ℤ) w‖ :=
        norm_tsum_le_tsum_norm hnorm_summable
    _ ≤ ∑' n : ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ),
          ‖Parseval.fc (psiF η) (n : ℤ)‖ :=
        hnorm_summable.tsum_le_tsum hterm hsub_summable

end KsIndex.ModeSeries
