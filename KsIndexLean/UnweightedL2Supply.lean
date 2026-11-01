module

/-
# Unweighted square integrability on a punctured disk

For `R > 0`, `memLp_two_of_energy_anchor` proves `MemLp v 2` on
`{ζ | 0 < ‖ζ‖ ∧ ‖ζ‖ ≤ R}`. It assumes a real-valued function `v` with
specified Fréchet derivative `Dv` at every point of that set, continuity
of `Dv` there, finite integral of its squared operator norm, and a finite
`L²` norm of `v` on the outer dyadic annulus.

Writing `a j` for the annular `L²` norms and `E` for the total derivative
energy, the doubling estimate gives
`a (j+1) ≤ a j / 2 + 2^(-j) * (R * sqrt E)`.
The resulting bound is a linear polynomial in `j` times `2^(-j)`, so its
squares are summable. The dyadic annuli cover the punctured disk, yielding
the conclusion. No pointwise boundedness of `v` or regularity at the
removed origin is assumed.
-/
public import KsIndexLean.AnnulusDoubling

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ENNReal Pointwise
namespace KsIndex.EndChart

/-! ### The abstract telescope -/

/-- **The telescope bound**: the recursion
`a_{j+1} ≤ a_j/2 + 2^{-j}·E` integrates to `a_j ≤ 2^{-j}a_0 + 2j·2^{-j}E`. -/
lemma telescope_bound (a : ℕ → ℝ≥0∞) (E : ℝ≥0∞)
    (hrec : ∀ j, a (j + 1) ≤ 2⁻¹ * a j + 2⁻¹ ^ j * E) :
    ∀ j, a j ≤ 2⁻¹ ^ j * a 0 + 2 * j * 2⁻¹ ^ j * E := by
  have h21 : (2:ℝ≥0∞)⁻¹ * 2 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have h12 : (2:ℝ≥0∞) * 2⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have key : 2⁻¹ * (2⁻¹ ^ j * a 0 + 2 * j * 2⁻¹ ^ j * E) + 2⁻¹ ^ j * E
        = 2⁻¹ ^ (j + 1) * a 0 + 2 * ((j:ℝ≥0∞) + 1) * 2⁻¹ ^ (j + 1) * E := by
      calc 2⁻¹ * (2⁻¹ ^ j * a 0 + 2 * j * 2⁻¹ ^ j * E) + 2⁻¹ ^ j * E
          = 2⁻¹ ^ (j + 1) * a 0
              + (2⁻¹ * 2) * j * 2⁻¹ ^ j * E + 2⁻¹ ^ j * E := by
            rw [pow_succ]
            ring
        _ = 2⁻¹ ^ (j + 1) * a 0 + ((j:ℝ≥0∞) + 1) * 2⁻¹ ^ j * E := by
            rw [h21]
            ring
        _ = 2⁻¹ ^ (j + 1) * a 0
              + ((j:ℝ≥0∞) + 1) * ((2 * 2⁻¹) * 2⁻¹ ^ j) * E := by
            rw [h12]
            ring
        _ = 2⁻¹ ^ (j + 1) * a 0
              + 2 * ((j:ℝ≥0∞) + 1) * 2⁻¹ ^ (j + 1) * E := by
            rw [pow_succ]
            ring
    calc a (j + 1) ≤ 2⁻¹ * a j + 2⁻¹ ^ j * E := hrec j
      _ ≤ 2⁻¹ * (2⁻¹ ^ j * a 0 + 2 * j * 2⁻¹ ^ j * E) + 2⁻¹ ^ j * E := by
          gcongr
      _ = 2⁻¹ ^ (j + 1) * a 0
            + 2 * ((j:ℝ≥0∞) + 1) * 2⁻¹ ^ (j + 1) * E := key
      _ = 2⁻¹ ^ (j + 1) * a 0 + 2 * ((j + 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ (j + 1) * E := by
          push_cast
          ring

/-- **Square summability**: under the telescope bound with finite
`a 0` and `E`, the squares have finite sum. -/
lemma tsum_sq_lt_top_of_telescope (a : ℕ → ℝ≥0∞) (E : ℝ≥0∞)
    (hE : E ≠ ⊤) (ha0 : a 0 ≠ ⊤)
    (hbound : ∀ j, a j ≤ 2⁻¹ ^ j * a 0 + 2 * j * 2⁻¹ ^ j * E) :
    (∑' j, a j ^ 2) < ⊤ := by
  set C : ℝ≥0∞ := a 0 + E with hC
  have hCne : C ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ha0, hE⟩
  -- uniform shape: a j ≤ (1 + 2j)·2⁻ʲ·C
  have hshape : ∀ j, a j ≤ (1 + 2 * j) * 2⁻¹ ^ j * C := by
    intro j
    calc a j ≤ 2⁻¹ ^ j * a 0 + 2 * j * 2⁻¹ ^ j * E := hbound j
      _ ≤ 2⁻¹ ^ j * C + 2 * j * 2⁻¹ ^ j * C := by
          gcongr
          · rw [hC]
            exact self_le_add_right _ _
          · rw [hC]
            exact self_le_add_left _ _
      _ = (1 + 2 * j) * 2⁻¹ ^ j * C := by ring
  -- compare the squares with a summable real series
  have hsq : ∀ j, a j ^ 2
      ≤ ENNReal.ofReal ((1 + 2 * (j:ℝ)) ^ 2 * (1/4) ^ j) * C ^ 2 := by
    intro j
    calc a j ^ 2 ≤ ((1 + 2 * j) * 2⁻¹ ^ j * C) ^ 2 := by
          gcongr
          exact hshape j
      _ = ((1 + 2 * j) * 2⁻¹ ^ j) ^ 2 * C ^ 2 := mul_pow _ _ 2
      _ = ENNReal.ofReal ((1 + 2 * (j:ℝ)) ^ 2 * (1/4) ^ j) * C ^ 2 := by
          congr 1
          have h1 : ENNReal.ofReal ((1:ℝ) + 2 * (j:ℝ)) = 1 + 2 * (j : ℝ≥0∞) := by
            rw [ENNReal.ofReal_add (by norm_num) (by positivity),
              ENNReal.ofReal_one, ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
          have h4 : ((2:ℝ≥0∞)⁻¹) ^ 2 = 4⁻¹ := by
            rw [← ENNReal.inv_pow]
            norm_num
          rw [ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow (by positivity),
            ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/4), h1,
            show ENNReal.ofReal ((1:ℝ)/4) = (4⁻¹ : ℝ≥0∞) by
              rw [show ((1:ℝ)/4) = (4:ℝ)⁻¹ by norm_num,
                ENNReal.ofReal_inv_of_pos (by norm_num),
                ENNReal.ofReal_ofNat],
            mul_pow]
          congr 1
          rw [← pow_mul, mul_comm j 2, pow_mul, h4]
  -- the real comparison series is summable
  have hsum : Summable fun j : ℕ => (1 + 2 * (j:ℝ)) ^ 2 * (1/4) ^ j := by
    have h1 : Summable fun j : ℕ => ((j:ℝ) ^ 2) * (1/4) ^ j := by
      simpa using
        summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
          (r := 1/4) (by rw [Real.norm_of_nonneg (by norm_num)]; norm_num)
    have h2 : Summable fun j : ℕ => ((j:ℝ) ^ 1) * (1/4) ^ j := by
      simpa using
        summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (r := 1/4) (by rw [Real.norm_of_nonneg (by norm_num)]; norm_num)
    have h0 : Summable fun j : ℕ => ((1:ℝ)/4) ^ j :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    refine (((h1.mul_left 4).add ((h2.mul_left 4).add h0)).congr fun j => ?_)
    ring
  -- assemble
  calc (∑' j, a j ^ 2)
      ≤ ∑' j : ℕ, ENNReal.ofReal ((1 + 2 * (j:ℝ)) ^ 2 * (1/4) ^ j) * C ^ 2 :=
        ENNReal.tsum_le_tsum hsq
    _ = (∑' j : ℕ, ENNReal.ofReal ((1 + 2 * (j:ℝ)) ^ 2 * (1/4) ^ j)) * C ^ 2 :=
        ENNReal.tsum_mul_right
    _ = ENNReal.ofReal (∑' j : ℕ, (1 + 2 * (j:ℝ)) ^ 2 * (1/4) ^ j) * C ^ 2 := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum]
    _ < ⊤ :=
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.pow_lt_top hCne.lt_top)

/-! ### Assembly on the punctured disk -/

/-- The closed disk with its center removed. -/
def puncturedDisk (R : ℝ) : Set ℂ := {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ ≤ R}

lemma measurableSet_puncturedDisk (R : ℝ) :
    MeasurableSet (puncturedDisk R) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)

/-- The dyadic annuli sit inside the punctured disk. -/
lemma dyadicAnnulus_subset_puncturedDisk {R : ℝ} (hR : 0 < R) {j : ℕ} :
    dyadicAnnulus (R * 2⁻¹ ^ j) ⊆ puncturedDisk R := by
  rintro ζ ⟨h1, h2⟩
  have hpos : (0:ℝ) < R * 2⁻¹ ^ j := by positivity
  constructor
  · linarith
  · calc ‖ζ‖ ≤ R * 2⁻¹ ^ j := h2
      _ ≤ R * 1 := by
          gcongr
          calc (2⁻¹:ℝ) ^ j ≤ 1 ^ j := by
                gcongr
                norm_num
            _ = 1 := one_pow j
      _ = R := mul_one R

/-- The dyadic annuli cover the punctured disk. -/
lemma puncturedDisk_subset_iUnion {R : ℝ} (hR : 0 < R) :
    puncturedDisk R ⊆ ⋃ j : ℕ, dyadicAnnulus (R * 2⁻¹ ^ j) := by
  rintro ζ ⟨h0, hle⟩
  have hex : ∃ n : ℕ, R * 2⁻¹ ^ n < ‖ζ‖ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos h0 hR)
      (by norm_num : (2⁻¹:ℝ) < 1)
    exact ⟨n, by
      rw [mul_comm]
      exact (lt_div_iff₀ hR).mp hn⟩
  classical
  have hspec : R * 2⁻¹ ^ (Nat.find hex) < ‖ζ‖ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hspec
    simp only [pow_zero, mul_one] at hspec
    linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  rw [hj] at hspec
  have hmin : ¬ R * 2⁻¹ ^ j < ‖ζ‖ := Nat.find_min hex (by omega)
  refine mem_iUnion.mpr ⟨j, ?_, ?_⟩
  · calc R * 2⁻¹ ^ j / 2 = R * (2⁻¹ ^ j * 2⁻¹) := by ring
      _ = R * 2⁻¹ ^ (j + 1) := by rw [← pow_succ]
      _ ≤ ‖ζ‖ := hspec.le
  · linarith [not_lt.mp hmin]

/-- Finite derivative energy and an outer-annulus `L²` norm give unweighted
`L²` membership on the punctured disk, under the stated differentiability
and derivative-continuity hypotheses. No pointwise bound on `v` is required. -/
theorem memLp_two_of_energy_anchor {R : ℝ} (hR : 0 < R)
    (v : ℂ → ℝ) (Dv : ℂ → (ℂ →L[ℝ] ℝ))
    (hv : ∀ ζ ∈ puncturedDisk R, HasFDerivAt v (Dv ζ) ζ)
    (hDvc : ContinuousOn Dv (puncturedDisk R))
    (hE : (∫⁻ ζ in puncturedDisk R, ‖Dv ζ‖ₑ ^ 2 ∂volume) ≠ ⊤)
    (hanchor : eLpNorm v 2 (volume.restrict (dyadicAnnulus R)) ≠ ⊤) :
    MemLp v 2 (volume.restrict (puncturedDisk R)) := by
  have hvc : ContinuousOn v (puncturedDisk R) :=
    fun ζ hζ => (hv ζ hζ).continuousAt.continuousWithinAt
  -- the annulus data
  set A : ℕ → Set ℂ := fun j => dyadicAnnulus (R * 2⁻¹ ^ j) with hAdef
  have hAmeas : ∀ j, MeasurableSet (A j) :=
    fun j => measurableSet_dyadicAnnulus _
  have hAsub : ∀ j, A j ⊆ puncturedDisk R :=
    fun j => dyadicAnnulus_subset_puncturedDisk hR
  have hradius : ∀ j : ℕ, 2 * (R * 2⁻¹ ^ (j + 1)) = R * 2⁻¹ ^ j := by
    intro j
    rw [pow_succ]
    field_simp
  set a : ℕ → ℝ≥0∞ := fun j => eLpNorm v 2 (volume.restrict (A j)) with hadef
  set Etot : ℝ≥0∞ := ∫⁻ ζ in puncturedDisk R, ‖Dv ζ‖ₑ ^ 2 ∂volume with hEdef
  -- squared eLpNorm = the lintegral of the square
  have hsq_eq : ∀ (μ : Measure ℂ) (f : ℂ → ℝ), AEStronglyMeasurable f μ →
      eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
    intro μ f hf
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
      show ((2:ℝ≥0∞)).toReal = (2:ℝ) by norm_num,
      ← ENNReal.rpow_natCast
        ((∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂μ) ^ (1 / (2:ℝ))) 2,
      ← ENNReal.rpow_mul]
    norm_num
  -- the recursion from annular scaling and the doubling estimate
  have hrec : ∀ j, a (j + 1)
      ≤ 2⁻¹ * a j + 2⁻¹ ^ j * (ENNReal.ofReal R * Etot ^ (1/2 : ℝ)) := by
    intro j
    set ρ : ℝ := R * 2⁻¹ ^ (j + 1) with hρdef
    have hρ : (0:ℝ) < ρ := by rw [hρdef]; positivity
    have hpair : dyadicAnnulus ρ ∪ dyadicAnnulus (2 * ρ) ⊆ puncturedDisk R := by
      rw [hρdef, hradius j]
      exact union_subset (hAsub (j + 1)) (hAsub j)
    -- measurability for the triangle inequality
    have hvA : AEStronglyMeasurable v (volume.restrict (A (j + 1))) :=
      ((hvc.mono (hAsub (j + 1))).aestronglyMeasurable (hAmeas (j + 1)))
    have hv2A : AEStronglyMeasurable (fun x => v ((2:ℝ) • x))
        (volume.restrict (A (j + 1))) := by
      have hc2 : ContinuousOn (fun x : ℂ => v ((2:ℝ) • x)) (A (j + 1)) := by
        apply hvc.comp (continuous_const_smul (2:ℝ)).continuousOn
        intro x hx
        apply hAsub j
        have hx' : x ∈ dyadicAnnulus ρ := hx
        have h2x : (2:ℝ) • x ∈ (2:ℝ) • dyadicAnnulus ρ := smul_mem_smul_set hx'
        rw [smul_dyadicAnnulus (by norm_num : (0:ℝ) < 2) ρ, hρdef,
          hradius j] at h2x
        exact h2x
      exact hc2.aestronglyMeasurable (hAmeas (j + 1))
    -- triangle: v = v(2·) − (v(2·) − v)
    have htri : a (j + 1)
        ≤ eLpNorm (fun x => v ((2:ℝ) • x)) 2 (volume.restrict (A (j + 1)))
          + eLpNorm (fun x => v ((2:ℝ) • x) - v x) 2
              (volume.restrict (A (j + 1))) := by
      have h1 : a (j + 1) = eLpNorm
          (fun x => v ((2:ℝ) • x) - (v ((2:ℝ) • x) - v x)) 2
          (volume.restrict (A (j + 1))) := by
        simp only [hadef]
        exact eLpNorm_congr_ae
          (Filter.Eventually.of_forall fun x => by ring)
      rw [h1]
      exact eLpNorm_sub_le (by norm_num)
    -- the doubling term: exact halving by annular scaling
    have hdouble : eLpNorm (fun x => v ((2:ℝ) • x)) 2
        (volume.restrict (A (j + 1))) = 2⁻¹ * a j := by
      rw [eLpNorm_comp_smul_restrict v (by norm_num : (0:ℝ) < 2)
        (hAmeas (j + 1))]
      congr 1
      · rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2),
          ENNReal.ofReal_ofNat]
      · simp only [hadef, hAdef]
        rw [smul_dyadicAnnulus (by norm_num : (0:ℝ) < 2), hradius j]
    -- the difference term: the doubling estimate, energy monotonicity and square roots
    have hdiff : eLpNorm (fun x => v ((2:ℝ) • x) - v x) 2
        (volume.restrict (A (j + 1)))
        ≤ 2⁻¹ ^ j * (ENNReal.ofReal R * Etot ^ (1/2 : ℝ)) := by
      have hEpair : (∫⁻ ζ in dyadicAnnulus ρ ∪ dyadicAnnulus (2 * ρ),
          ‖Dv ζ‖ₑ ^ 2 ∂volume) ≤ Etot :=
        lintegral_mono_set hpair
      have hsq : eLpNorm (fun x => v ((2:ℝ) • x) - v x) 2
          (volume.restrict (A (j + 1))) ^ 2
          ≤ ENNReal.ofReal (ρ ^ 2) * Etot := by
        rw [hsq_eq _ _ (show AEStronglyMeasurable (fun x => v ((2 : ℝ) • x) - v x)
          (volume.restrict (A (j + 1))) from by
            convert hv2A.sub hvA using 1)]
        exact (lintegral_sq_sub_doubling_le v Dv hv hDvc hρ hpair).trans
          (by gcongr)
      have hsqrt : eLpNorm (fun x => v ((2:ℝ) • x) - v x) 2
          (volume.restrict (A (j + 1)))
          ≤ ENNReal.ofReal ρ * Etot ^ (1/2 : ℝ) := by
        have h1 := ENNReal.rpow_le_rpow hsq (by norm_num : (0:ℝ) ≤ 1/2)
        rw [← ENNReal.rpow_natCast (eLpNorm _ 2 _) 2,
          ← ENNReal.rpow_mul] at h1
        norm_num at h1
        refine h1.trans_eq ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_pos (by positivity)]
        congr 2
        rw [← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ.le,
          show ((2:ℕ):ℝ) * (1/2) = 1 by norm_num, Real.rpow_one]
      have hρle : ENNReal.ofReal ρ ≤ 2⁻¹ ^ j * ENNReal.ofReal R := by
        rw [hρdef, ENNReal.ofReal_mul hR.le, mul_comm]
        gcongr
        calc ENNReal.ofReal (2⁻¹ ^ (j + 1))
            = (2⁻¹ : ℝ≥0∞) ^ (j + 1) := by
              rw [ENNReal.ofReal_pow (by norm_num)]
              congr 1
              rw [ENNReal.ofReal_inv_of_pos (by norm_num),
                ENNReal.ofReal_ofNat]
          _ ≤ 2⁻¹ ^ j := by
              rw [pow_succ]
              calc (2⁻¹:ℝ≥0∞) ^ j * 2⁻¹ ≤ 2⁻¹ ^ j * 1 := by
                    gcongr
                    exact ENNReal.inv_le_one.mpr one_le_two
                _ = 2⁻¹ ^ j := mul_one _
      calc eLpNorm (fun x => v ((2:ℝ) • x) - v x) 2
            (volume.restrict (A (j + 1)))
          ≤ ENNReal.ofReal ρ * Etot ^ (1/2 : ℝ) := hsqrt
        _ ≤ (2⁻¹ ^ j * ENNReal.ofReal R) * Etot ^ (1/2 : ℝ) := by gcongr
        _ = 2⁻¹ ^ j * (ENNReal.ofReal R * Etot ^ (1/2 : ℝ)) :=
            mul_assoc _ _ _
    calc a (j + 1)
        ≤ eLpNorm (fun x => v ((2:ℝ) • x)) 2 (volume.restrict (A (j + 1)))
          + eLpNorm (fun x => v ((2:ℝ) • x) - v x) 2
              (volume.restrict (A (j + 1))) := htri
      _ = 2⁻¹ * a j + eLpNorm (fun x => v ((2:ℝ) • x) - v x) 2
              (volume.restrict (A (j + 1))) := by rw [hdouble]
      _ ≤ 2⁻¹ * a j + 2⁻¹ ^ j * (ENNReal.ofReal R * Etot ^ (1/2 : ℝ)) := by
          gcongr
  -- telescope and sum
  have hEterm : ENNReal.ofReal R * Etot ^ (1/2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hE).ne
  have ha0 : a 0 ≠ ⊤ := by
    simpa [hadef, hAdef] using hanchor
  have hsum := tsum_sq_lt_top_of_telescope a _ hEterm ha0
    (telescope_bound a _ hrec)
  -- assemble MemLp
  rw [memLp_iff]
  have hsq2 : eLpNorm v 2 (volume.restrict (puncturedDisk R)) ^ 2 < ⊤ := by
    rw [hsq_eq _ _ (hvc.aestronglyMeasurable (measurableSet_puncturedDisk R))]
    calc (∫⁻ ζ in puncturedDisk R, ‖v ζ‖ₑ ^ 2 ∂volume)
        ≤ ∫⁻ ζ in ⋃ j : ℕ, A j, ‖v ζ‖ₑ ^ 2 ∂volume :=
          lintegral_mono_set (puncturedDisk_subset_iUnion hR)
      _ ≤ ∑' j, ∫⁻ ζ in A j, ‖v ζ‖ₑ ^ 2 ∂volume := lintegral_iUnion_le _ _
      _ = ∑' j, a j ^ 2 := by
          refine tsum_congr fun j => ?_
          simp only [hadef]
          exact (hsq_eq _ _ ((hvc.mono (hAsub j)).aestronglyMeasurable (hAmeas j))).symm
      _ < ⊤ := hsum
  have hne : eLpNorm v 2 (volume.restrict (puncturedDisk R)) ≠ ⊤ := by
    intro htop
    rw [htop] at hsq2
    simp at hsq2
  exact lt_top_iff_ne_top.mpr hne

end KsIndex.EndChart
