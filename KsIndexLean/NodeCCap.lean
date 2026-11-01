module

public import KsIndexLean.SingleArcConditionalAssembly
public import KsIndexLean.NodeCQLower

@[expose] public section


/-!
# Single-arc index and nullity bound for the middle character classes

For `k ≥ 4` and `2 ≤ j ≤ k - 2`, the combined negative index and sesquilinear
nullity on `dnSpace 1` are at most one. The proof works directly on that domain.
The head map extracting Fourier coefficients at `0` and `-1` is injective on
nonpositive subspaces by positivity when both heads vanish. The lower bound
`nodeC_Q_lower` excludes the slice direction `(1/σ₀, -1/σ₋₁)` from its image.
Thus a negative subspace and a radical subspace together have dimension at
most one. The resulting `SingleArcUpperBound` supplies the middle-class input
to the mixed-nullity assembly.
-/

noncomputable section
open MeasureTheory Complex Filter Topology Module
namespace KsIndex.SingleArcReindex
open KsIndex.Trace KsIndex.CircleSobolev KsIndex.NegativeDensity KsIndex.DtnBridge KsIndex.NodeC

variable {k j : ℕ}

/-! ### Sesquilinearity and the real diagonal of `singleArcForm` -/

/-- Each diagonal term is real: `σ·conj(f̂)·f̂ = ↑(σ‖f̂‖²)`. -/
lemma singleArcForm_term (f : dnSpace 1) (n : ℤ) :
    (sigma k (censusA j k) n : ℂ)
        * (starRingEnd ℂ) (coeff (1 / 2 : ℝ) f.val n) * coeff (1 / 2 : ℝ) f.val n
      = ((sigma k (censusA j k) n * ‖coeff (1 / 2 : ℝ) f.val n‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_assoc, Complex.conj_mul']
  push_cast
  ring

lemma coeff_dnSpace_add (f₁ f₂ : dnSpace 1) (n : ℤ) :
    coeff (1 / 2 : ℝ) (f₁ + f₂).val n
      = coeff (1 / 2 : ℝ) f₁.val n + coeff (1 / 2 : ℝ) f₂.val n := by
  simp only [coeff, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, mul_add]

lemma singleArcForm_add_left (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) (f₁ f₂ g : dnSpace 1) :
    singleArcForm k j (f₁ + f₂) g = singleArcForm k j f₁ g + singleArcForm k j f₂ g := by
  unfold singleArcForm
  rw [← (singleArcForm_summable hk hj0 hjk f₁ g).tsum_add (singleArcForm_summable hk hj0 hjk f₂ g)]
  refine tsum_congr fun n => ?_
  rw [coeff_dnSpace_add]
  simp only [map_add]
  ring

lemma singleArcForm_add_right (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) (f g₁ g₂ : dnSpace 1) :
    singleArcForm k j f (g₁ + g₂) = singleArcForm k j f g₁ + singleArcForm k j f g₂ := by
  unfold singleArcForm
  rw [← (singleArcForm_summable hk hj0 hjk f g₁).tsum_add (singleArcForm_summable hk hj0 hjk f g₂)]
  refine tsum_congr fun n => ?_
  rw [coeff_dnSpace_add]
  ring

lemma singleArcForm_conj_symm (f g : dnSpace 1) :
    singleArcForm k j g f = (starRingEnd ℂ) (singleArcForm k j f g) := by
  unfold singleArcForm
  rw [Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- The real σ-weighted energy is summable (from `singleArcForm_summable`). -/
lemma singleArcForm_diag_summable (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) (f : dnSpace 1) :
    Summable (fun n : ℤ => sigma k (censusA j k) n * ‖coeff (1 / 2 : ℝ) f.val n‖ ^ 2) := by
  have hcplx := singleArcForm_summable hk hj0 hjk f f
  have h : Summable (fun n : ℤ =>
      ((sigma k (censusA j k) n * ‖coeff (1 / 2 : ℝ) f.val n‖ ^ 2 : ℝ) : ℂ)) :=
    hcplx.congr (fun n => singleArcForm_term f n)
  exact_mod_cast Complex.summable_ofReal.mp h

/-- The diagonal of `singleArcForm` is the real σ-weighted energy. -/
lemma singleArcForm_diag (_hk : 3 ≤ k) (_hj0 : 0 < j) (_hjk : j < k) (f : dnSpace 1) :
    (singleArcForm k j f f).re
      = ∑' n : ℤ, sigma k (censusA j k) n * ‖coeff (1 / 2 : ℝ) f.val n‖ ^ 2 := by
  have h1 : singleArcForm k j f f
      = ((∑' n : ℤ, sigma k (censusA j k) n * ‖coeff (1 / 2 : ℝ) f.val n‖ ^ 2 : ℝ) : ℂ) := by
    rw [singleArcForm, Complex.ofReal_tsum]
    exact tsum_congr (fun n => singleArcForm_term f n)
  rw [h1, Complex.ofReal_re]

/-! ### The two positivity inputs -/

/-- The guarded (`{0,-1}`-excluded) σ-energy is summable. -/
lemma diag_guarded_summable (hk : 4 ≤ k) (hj2 : 2 ≤ j) (hjk : j + 2 ≤ k) (f : dnSpace 1) :
    Summable (fun n : ℤ =>
      if n = 0 ∨ n = -1 then 0 else sigma k (censusA j k) n * ‖coeff (1 / 2 : ℝ) f.val n‖ ^ 2) := by
  have h3k : 3 ≤ k := by omega
  have hj0 : 0 < j := by omega
  have hjk' : j < k := by omega
  have h1k : 1 ≤ k := by omega
  have ha0 : 0 < censusA j k := censusA_pos hk hjk
  have ha1 : censusA j k < 1 := censusA_lt_one hk hj2
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (singleArcForm_diag_summable h3k hj0 hjk' f).abs
  · split_ifs with h
    · exact le_refl 0
    · exact mul_nonneg
        (sigma_pos_of_ne h1k ha0 ha1 (not_or.mp h).1 (not_or.mp h).2).le (sq_nonneg _)
  · split_ifs with h
    · positivity
    · exact le_abs_self _

/-- **Heads-zero positivity**: a nonzero `f` with `f̂(0)=f̂(-1)=0` has positive energy. -/
lemma heads_zero_pos (hk : 4 ≤ k) (hj2 : 2 ≤ j) (hjk : j + 2 ≤ k) {f : dnSpace 1}
    (h0 : coeff (1 / 2 : ℝ) f.val 0 = 0) (h1 : coeff (1 / 2 : ℝ) f.val (-1) = 0) (hne : f ≠ 0) :
    0 < (singleArcForm k j f f).re := by
  have h3k : 3 ≤ k := by omega
  have hj0 : 0 < j := by omega
  have hjk' : j < k := by omega
  have h1k : 1 ≤ k := by omega
  have ha0 : 0 < censusA j k := censusA_pos hk hjk
  have ha1 : censusA j k < 1 := censusA_lt_one hk hj2
  rw [singleArcForm_diag h3k hj0 hjk']
  have hval : f.val ≠ 0 := fun h => hne (Subtype.ext h)
  have hex : ∃ n, coeff (1 / 2 : ℝ) f.val n ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hval ?_
    ext n
    have hcn := hc n
    rw [coeff] at hcn
    have hw : (weight (1 / 2 : ℝ) n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos _ n).ne'
    simpa using (mul_eq_zero.mp hcn).resolve_left (inv_ne_zero hw)
  obtain ⟨n, hn⟩ := hex
  have hn0 : n ≠ 0 := fun h => hn (by rw [h, h0])
  have hn1 : n ≠ -1 := fun h => hn (by rw [h, h1])
  have hnn : ∀ m : ℤ, 0 ≤ sigma k (censusA j k) m * ‖coeff (1 / 2 : ℝ) f.val m‖ ^ 2 := by
    intro m
    by_cases hm : m = 0 ∨ m = -1
    · rcases hm with rfl | rfl
      · rw [h0]; simp
      · rw [h1]; simp
    · exact mul_nonneg (sigma_pos_of_ne h1k ha0 ha1 (not_or.mp hm).1 (not_or.mp hm).2).le
        (sq_nonneg _)
  refine lt_of_lt_of_le ?_ ((singleArcForm_diag_summable h3k hj0 hjk' f).le_tsum n
    (fun m _ => hnn m))
  exact mul_pos (sigma_pos_of_ne h1k ha0 ha1 hn0 hn1) (by positivity)

/-- **Slice positivity**: `f` with heads `(1/σ₀, -1/σ₋₁)` has positive energy
(consumes `nodeC_Q_lower`). -/
lemma slice_pos (hk : 4 ≤ k) (hj2 : 2 ≤ j) (hjk : j + 2 ≤ k) {f : dnSpace 1}
    (h0 : coeff (1 / 2 : ℝ) f.val 0 = ((1 / sigma k (censusA j k) 0 : ℝ) : ℂ))
    (h1 : coeff (1 / 2 : ℝ) f.val (-1) = ((-1 / sigma k (censusA j k) (-1) : ℝ) : ℂ)) :
    0 < (singleArcForm k j f f).re := by
  have h3k : 3 ≤ k := by omega
  have hj0 : 0 < j := by omega
  have hjk' : j < k := by omega
  have hσ0 : sigma k (censusA j k) 0 < 0 := sigma_census_zero hk hj2 hjk
  have hσ1 : sigma k (censusA j k) (-1) < 0 := sigma_census_negOne hk hj2 hjk
  rw [singleArcForm_diag h3k hj0 hjk']
  have hg := diag_guarded_summable hk hj2 hjk f
  have hsplit : (∑' n : ℤ, sigma k (censusA j k) n * ‖coeff (1 / 2 : ℝ) f.val n‖ ^ 2)
      = sigma k (censusA j k) 0 * ‖coeff (1 / 2 : ℝ) f.val 0‖ ^ 2
        + sigma k (censusA j k) (-1) * ‖coeff (1 / 2 : ℝ) f.val (-1)‖ ^ 2
        + ∑' n : ℤ, (if n = 0 ∨ n = -1 then 0
            else sigma k (censusA j k) n * ‖coeff (1 / 2 : ℝ) f.val n‖ ^ 2) := by
    have e0 : Summable fun n : ℤ =>
        if n = 0 then sigma k (censusA j k) 0 * ‖coeff (1 / 2 : ℝ) f.val 0‖ ^ 2 else 0 :=
      summable_of_ne_finset_zero (s := {0}) fun n hn => by
        simp only [Finset.mem_singleton] at hn; simp [hn]
    have e1 : Summable fun n : ℤ =>
        if n = -1 then sigma k (censusA j k) (-1) * ‖coeff (1 / 2 : ℝ) f.val (-1)‖ ^ 2 else 0 :=
      summable_of_ne_finset_zero (s := {-1}) fun n hn => by
        simp only [Finset.mem_singleton] at hn; simp [hn]
    have hsum0 : (∑' n : ℤ, if n = 0 then
        sigma k (censusA j k) 0 * ‖coeff (1 / 2 : ℝ) f.val 0‖ ^ 2 else 0)
        = sigma k (censusA j k) 0 * ‖coeff (1 / 2 : ℝ) f.val 0‖ ^ 2 := tsum_ite_eq 0 _
    have hsum1 : (∑' n : ℤ, if n = -1 then
        sigma k (censusA j k) (-1) * ‖coeff (1 / 2 : ℝ) f.val (-1)‖ ^ 2 else 0)
        = sigma k (censusA j k) (-1) * ‖coeff (1 / 2 : ℝ) f.val (-1)‖ ^ 2 := tsum_ite_eq (-1) _
    rw [← hsum0, ← hsum1, ← e0.tsum_add e1, ← (e0.add e1).tsum_add hg]
    refine tsum_congr fun n => ?_
    by_cases hn0 : n = 0
    · subst hn0; simp
    · by_cases hn1 : n = -1
      · subst hn1; simp
      · simp [hn0, hn1]
  rw [hsplit]
  have hh0 : sigma k (censusA j k) 0 * ‖coeff (1 / 2 : ℝ) f.val 0‖ ^ 2
      = -(1 / |sigma k (censusA j k) 0|) := by
    rw [h0, Complex.norm_real, Real.norm_eq_abs, sq_abs, abs_of_neg hσ0]; field_simp
  have hh1 : sigma k (censusA j k) (-1) * ‖coeff (1 / 2 : ℝ) f.val (-1)‖ ^ 2
      = -(1 / |sigma k (censusA j k) (-1)|) := by
    rw [h1, Complex.norm_real, Real.norm_eq_abs, sq_abs, abs_of_neg hσ1]; field_simp
  have hne : coeff (1 / 2 : ℝ) f.val 0 ≠ coeff (1 / 2 : ℝ) f.val (-1) := by
    rw [h0, h1, Ne, Complex.ofReal_inj]
    have hp0 : (1 : ℝ) / sigma k (censusA j k) 0 < 0 := div_neg_of_pos_of_neg one_pos hσ0
    have hp1 : (0 : ℝ) < -1 / sigma k (censusA j k) (-1) := div_pos_of_neg_of_neg (by norm_num) hσ1
    linarith
  have hQ := nodeC_Q_lower hk hj2 hjk f.property hne hg
  have hfactor : ‖coeff (1 / 2 : ℝ) f.val 0 - coeff (1 / 2 : ℝ) f.val (-1)‖ ^ 2
      * (|sigma k (censusA j k) 0| * |sigma k (censusA j k) (-1)|
          / (|sigma k (censusA j k) 0| + |sigma k (censusA j k) (-1)|))
      = 1 / |sigma k (censusA j k) 0| + 1 / |sigma k (censusA j k) (-1)| := by
    rw [h0, h1, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      abs_of_neg hσ0, abs_of_neg hσ1]
    have hx : sigma k (censusA j k) 0 ≠ 0 := ne_of_lt hσ0
    have hy : sigma k (censusA j k) (-1) ≠ 0 := ne_of_lt hσ1
    have hxy : -sigma k (censusA j k) 0 + -sigma k (censusA j k) (-1) ≠ 0 := by
      have : (0:ℝ) < -sigma k (censusA j k) 0 + -sigma k (censusA j k) (-1) := by linarith
      linarith
    field_simp
    ring
  rw [hfactor] at hQ
  rw [hh0, hh1]
  linarith

/-! ### The module-level engine and the main theorem -/

/-- A strictly-negative subspace `V` and a radical subspace `W` together have
`finrank ≤ 1` — the paper's C-cap contradiction, run on `↥(dnSpace 1)`. -/
lemma cap_engine (hk : 4 ≤ k) (hj2 : 2 ≤ j) (hjk : j + 2 ≤ k)
    {V W : Submodule ℂ (dnSpace 1)}
    (hV : ∀ x ∈ V, x ≠ 0 → (singleArcForm k j x x).re < 0)
    (hW : ∀ u ∈ W, ∀ w, singleArcForm k j u w = 0)
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] :
    finrank ℂ V + finrank ℂ W ≤ 1 := by
  have h3k : 3 ≤ k := by omega
  have hj0 : 0 < j := by omega
  have hjk' : j < k := by omega
  have hzero : ∀ g : dnSpace 1, singleArcForm k j 0 g = 0 := by
    intro g
    have h := singleArcForm_add_left h3k hj0 hjk' 0 0 g
    rw [add_zero] at h
    linear_combination -h
  have hdisj : V ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hne
    obtain ⟨hxV, hxW⟩ := Submodule.mem_inf.mp hx
    have hlt := hV x hxV hne
    rw [hW x hxW x] at hlt
    simp at hlt
  have hnonpos : ∀ x ∈ V ⊔ W, (singleArcForm k j x x).re ≤ 0 := by
    intro x hx
    rw [Submodule.mem_sup] at hx
    obtain ⟨v, hv, w, hw, rfl⟩ := hx
    have hexp : singleArcForm k j (v + w) (v + w) = singleArcForm k j v v := by
      rw [singleArcForm_add_left h3k hj0 hjk', singleArcForm_add_right h3k hj0 hjk',
        singleArcForm_add_right h3k hj0 hjk']
      have hwv : singleArcForm k j w v = 0 := hW w hw v
      have hww : singleArcForm k j w w = 0 := hW w hw w
      have hvw : singleArcForm k j v w = 0 := by rw [singleArcForm_conj_symm, hwv, map_zero]
      rw [hvw, hwv, hww]; ring
    rw [hexp]
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [hzero]; simp
    · exact (hV v hv hv0).le
  -- head map `f ↦ (f̂(0), f̂(-1))`
  let φ : dnSpace 1 →ₗ[ℂ] ℂ × ℂ :=
    ((coeffLinear (1 / 2 : ℝ) 0).comp (dnSpace 1).subtype).prod
      ((coeffLinear (1 / 2 : ℝ) (-1)).comp (dnSpace 1).subtype)
  have hφ1 : ∀ x : dnSpace 1, (φ x).1 = coeff (1 / 2 : ℝ) x.val 0 := fun _ => rfl
  have hφ2 : ∀ x : dnSpace 1, (φ x).2 = coeff (1 / 2 : ℝ) x.val (-1) := fun _ => rfl
  have hinj : Function.Injective (φ.domRestrict (V ⊔ W)) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hx
    have hc0 : coeff (1 / 2 : ℝ) x.val.val 0 = 0 := by rw [← hφ1 x.val, hx]; rfl
    have hc1 : coeff (1 / 2 : ℝ) x.val.val (-1) = 0 := by rw [← hφ2 x.val, hx]; rfl
    by_contra hxne
    have hxne' : x.val ≠ 0 := fun h => hxne (Subtype.ext h)
    have hpos := heads_zero_pos hk hj2 hjk hc0 hc1 hxne'
    have hle := hnonpos x.val x.property
    linarith
  have hmiss : (((1 / sigma k (censusA j k) 0 : ℝ) : ℂ),
      ((-1 / sigma k (censusA j k) (-1) : ℝ) : ℂ)) ∉ (V ⊔ W).map φ := by
    rintro ⟨x, hx, hxeq⟩
    have hc0 : coeff (1 / 2 : ℝ) x.val 0 = ((1 / sigma k (censusA j k) 0 : ℝ) : ℂ) := by
      rw [← hφ1, hxeq]
    have hc1 : coeff (1 / 2 : ℝ) x.val (-1) = ((-1 / sigma k (censusA j k) (-1) : ℝ) : ℂ) := by
      rw [← hφ2, hxeq]
    have hpos := slice_pos hk hj2 hjk hc0 hc1
    have hle := hnonpos x hx
    linarith
  have hmap_lt : (V ⊔ W).map φ < ⊤ :=
    lt_of_le_of_ne le_top (fun htop => hmiss (by rw [htop]; exact Submodule.mem_top))
  have hfr : finrank ℂ ((V ⊔ W).map φ) ≤ 1 := by
    have h2 : finrank ℂ (ℂ × ℂ) = 2 := by simp [Module.finrank_prod]
    have hlt := Submodule.finrank_lt_finrank_of_lt hmap_lt
    rw [Submodule.topEquiv.finrank_eq] at hlt
    omega
  have heq : finrank ℂ ((V ⊔ W).map φ) = finrank ℂ (V ⊔ W : Submodule ℂ (dnSpace 1)) := by
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
  have hsup : finrank ℂ V + finrank ℂ W = finrank ℂ (V ⊔ W : Submodule ℂ (dnSpace 1)) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [hdisj, finrank_bot] at h
    omega
  omega

/-- **Middle-class single-arc bound.**  For every middle class the single-arc index and nullity
sum to at most one: `SingleArcUpperBound k j`.  Assembles `nodeC_Q_lower` (slice
positivity) via the module-level engine.  Consumed by the conditional capstone
`all_mixed_nullity_zero_of_middle_bounds`. -/
theorem nodeC_singleArcUpperBound (hk : 4 ≤ k) (hj2 : 2 ≤ j) (hjk : j + 2 ≤ k) :
    SingleArcUpperBound k j := by
  have hidx : negativeIndex (fun f : dnSpace 1 => (singleArcForm k j f f).re) = 1 :=
    singleArc_index_one (by omega) (by omega) (by omega)
  -- `negativeIndex = 1` provides a negative subspace of dimension ≥ 1
  have hwit : ∃ V : Submodule ℂ (dnSpace 1),
      (∀ x ∈ V, x ≠ 0 → (singleArcForm k j x x).re < 0) ∧
      FiniteDimensional ℂ V ∧ 1 ≤ finrank ℂ V := by
    by_contra hcon
    push Not at hcon
    have h0 : negativeIndex (fun f : dnSpace 1 => (singleArcForm k j f f).re) = 0 := by
      refine le_antisymm ?_ zero_le
      refine iSup_le fun V => iSup_le fun hneg => iSup_le fun hf => ?_
      have := hf
      have hlt := hcon V hneg hf
      have hz : finrank ℂ V = 0 := by omega
      rw [hz, Nat.cast_zero]
    rw [h0] at hidx
    exact absurd hidx zero_ne_one
  obtain ⟨V₁, hneg₁, hfin₁, hge₁⟩ := hwit
  have := hfin₁
  -- the nullity vanishes: any radical subspace has dimension 0
  have hSN : sesqNullity (singleArcForm k j) ≤ 0 := by
    refine iSup_le fun W => iSup_le fun hW => iSup_le fun hfW => ?_
    have := hfW
    have hcap := cap_engine hk hj2 hjk hneg₁ hW
    have hz : finrank ℂ W = 0 := by omega
    rw [hz, Nat.cast_zero]
  unfold SingleArcUpperBound
  rw [hidx, le_antisymm hSN zero_le]
  simp

end KsIndex.SingleArcReindex
