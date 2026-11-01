module

public import KsIndexLean.ModeWitness
public import KsIndexLean.CircleSobolev

@[expose] public section


/-! General coefficient reindexing for the single-arc reduction.
The spatial arc-support identification is supplied by SingleArcDNEquivalence. -/
noncomputable section
namespace KsIndex.SingleArcReindex
open ModeWitness CircleSobolev

lemma lattice_weight_upper (k j : ℕ) (n : ℤ) :
    1 + |(lz k j n : ℝ)| ≤ ((k : ℝ) + 1) * (1 + |(n : ℝ)|) := by
  have hc : ((k - j : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k j
  have h := abs_add_le ((k : ℝ) * n) ((k - j : ℕ) : ℝ)
  simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) by positivity),
    abs_of_nonneg (show (0 : ℝ) ≤ ((k - j : ℕ) : ℝ) by positivity)] at h
  have he : (lz k j n : ℝ) = (k : ℝ) * n + ((k - j : ℕ) : ℝ) := by simp [lz]
  rw [he]
  nlinarith [abs_nonneg (n : ℝ)]

lemma lattice_weight_lower {k : ℕ} (hk : 1 ≤ k) (j : ℕ) (n : ℤ) :
    1 + |(n : ℝ)| ≤ 2 * (1 + |(lz k j n : ℝ)|) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : ((k - j : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k j
  have he : (lz k j n : ℝ) - ((k - j : ℕ) : ℝ) = (k : ℝ) * n := by simp [lz]
  have h := abs_add_le (lz k j n : ℝ) (-((k - j : ℕ) : ℝ))
  simp only [← sub_eq_add_neg, abs_neg] at h
  rw [he, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) by positivity),
    abs_of_nonneg (show (0 : ℝ) ≤ ((k - j : ℕ) : ℝ) by positivity)] at h
  have hn : |(n : ℝ)| ≤ |(lz k j n : ℝ)| + 1 := by
    nlinarith [abs_nonneg (lz k j n : ℝ),
      mul_nonneg (sub_nonneg.mpr hk') (abs_nonneg (lz k j n : ℝ))]
  linarith [abs_nonneg (lz k j n : ℝ)]

lemma lattice_range {k j : ℕ} (hj : j ≤ k) (m : ℤ) :
    (∃ n : ℤ, m = lz k j n) ↔ ∃ q : ℤ, m = -(j : ℤ) + (k : ℤ) * q := by
  have hc : ((k - j : ℕ) : ℤ) = (k : ℤ) - j := Int.natCast_sub hj
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, by unfold lz; rw [hc]; ring⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q - 1, by unfold lz; rw [hc]; ring⟩

lemma reindex_summable {k : ℕ} (hk : 3 ≤ k) (j : ℕ)
    (f : Space (1 / 2)) :
    Summable (fun n : ℤ => weight (1 / 2) n ^ 2 *
      ‖coeff (1 / 2) f (lz k j n)‖ ^ 2) := by
  have h := (hasSum_weighted_sq (1 / 2) f).summable.comp_injective
    (lz_injective (r := j) hk)
  have h2 := h.mul_left 2
  refine h2.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  have hw (m : ℤ) : weight (1 / 2) m ^ 2 = 1 + |(m : ℝ)| := by
    rw [weight_sq]; norm_num
  simp only [Function.comp_apply, hw]
  nlinarith [mul_le_mul_of_nonneg_right
    (lattice_weight_lower (by omega : 1 ≤ k) j n)
    (sq_nonneg ‖coeff (1 / 2) f (lz k j n)‖)]

/-- Extract physical Fourier coefficients, rather than permuting stored coordinates. -/
def extract {k : ℕ} (hk : 3 ≤ k) (j : ℕ) (f : Space (1 / 2)) : Space (1 / 2) :=
  ofCoefficients (1 / 2) (fun n => coeff (1 / 2) f (lz k j n))
    (reindex_summable hk j f)

@[simp] lemma coeff_extract {k : ℕ} (hk : 3 ≤ k) (j : ℕ)
    (f : Space (1 / 2)) (n : ℤ) :
    coeff (1 / 2) (extract hk j f) n = coeff (1 / 2) f (lz k j n) :=
  coeff_ofCoefficients _ _ _ _

/-- The physical-coefficient extraction is complex-linear. -/
def extractLinear {k : ℕ} (hk : 3 ≤ k) (j : ℕ) :
    Space (1 / 2) →ₗ[ℂ] Space (1 / 2) where
  toFun := extract hk j
  map_add' f g := by
    apply coeff_injective (1 / 2)
    funext n
    change coeff (1 / 2) (extract hk j (f + g)) n =
      (coeffLinear (1 / 2) n) (extract hk j f + extract hk j g)
    rw [map_add, coeff_extract]
    change (coeffLinear (1 / 2) (lz k j n)) (f + g) = _
    rw [map_add]
    change coeff (1 / 2) f (lz k j n) + coeff (1 / 2) g (lz k j n) =
      coeff (1 / 2) (extract hk j f) n + coeff (1 / 2) (extract hk j g) n
    simp only [coeff_extract]
  map_smul' c f := by
    apply coeff_injective (1 / 2)
    funext n
    change coeff (1 / 2) (extract hk j (c • f)) n =
      (coeffLinear (1 / 2) n) (c • extract hk j f)
    rw [map_smul, coeff_extract]
    change (coeffLinear (1 / 2) (lz k j n)) (c • f) = _
    rw [map_smul]
    change c • coeff (1 / 2) f (lz k j n) = c • coeff (1 / 2) (extract hk j f) n
    rw [coeff_extract]

/-- No information is lost on the paper's character subspace. -/
theorem extract_injective_on_character {k j : ℕ} (hk : 3 ≤ k) (hj : j ≤ k)
    {f g : Space (1 / 2)} (hf : f ∈ character (1 / 2) j k)
    (hg : g ∈ character (1 / 2) j k)
    (h : extract hk j f = extract hk j g) : f = g := by
  apply coeff_injective (1 / 2)
  funext m
  by_cases hm : ∃ n : ℤ, m = lz k j n
  · obtain ⟨n, rfl⟩ := hm
    have he := congrArg (fun u => coeff (1 / 2) u n) h
    simpa only [coeff_extract] using he
  · have hoff : ¬ ∃ q : ℤ, m = -(j : ℤ) + (k : ℤ) * q :=
      fun hq => hm ((lattice_range hj m).mpr hq)
    rw [(mem_character _ _ _ _).mp hf m hoff,
      (mem_character _ _ _ _).mp hg m hoff]

end KsIndex.SingleArcReindex
