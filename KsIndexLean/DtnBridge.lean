module

public import KsIndexLean.CircleSobolevMultiplier
public import KsIndexLean.FormIndexDensity

@[expose] public section


/-!
# Half-order Dirichlet-to-Neumann form and its diagonal model

Physical Fourier coefficients give a complex-linear equivalence between the
mean-zero half-order circle space and `DomDiag (dtnSymbol k)`. The equivalence
preserves the sesquilinear form, so it transfers index and nullity algebraically.
No bicontinuity assertion is needed or supplied by this linear equivalence.
The symbol's zero modes `|ℓ| = k - 1` are retained in the nullity calculation.

For `k ≥ 3`, `faithfulNopIndex` gives index `2k - 4` and `faithfulNopNullity`
gives nullity `2`. The theorem `duality_dottedDtnCLM` identifies the form with
the actual half-order Dirichlet-to-Neumann duality pairing, with its arclength
factor `2π`. Nullity is transported through an equivalence, not inferred from
density. Comparison with the disk Neumann Jacobi problem is a separate step.
-/

noncomputable section
open Set
namespace KsIndex.DtnBridge
open KsIndex.CircleSobolev KsIndex.DtNCircle KsIndex.DiagForm KsIndex.FormIndex

/-! ### Symbol bounds: coercive tail (upper bound = existing `dtnSymbol_growth`) -/

lemma one_sub_ratio_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < 1 - ((k : ℝ) - 1) ^ 2 / (k : ℝ) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : ((k : ℝ) - 1) ^ 2 < (k : ℝ) ^ 2 := by nlinarith
  have h2 : ((k : ℝ) - 1) ^ 2 / (k : ℝ) ^ 2 < 1 :=
    (div_lt_one (by positivity)).mpr h1
  linarith

/-- The coercive tail: for `|ℓ| ≥ k` the symbol dominates a positive
multiple of `|ℓ|`.  No bound is claimed at the finitely many small modes
(the symbol VANISHES at `|ℓ| = k − 1`). -/
lemma dtnSymbol_tail_lower {k : ℕ} (hk : 1 ≤ k) (ℓ : NZ)
    (hℓ : (k : ℝ) ≤ |(ℓ.val : ℝ)|) :
    (1 - ((k : ℝ) - 1) ^ 2 / (k : ℝ) ^ 2) * |(ℓ.val : ℝ)| ≤ |dtnSymbol k ℓ| := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hl0 : (0 : ℝ) < |(ℓ.val : ℝ)| := absval_pos ℓ
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq : (k : ℝ) ^ 2 ≤ ((ℓ.val : ℝ)) ^ 2 := by
    rw [← sq_abs ((ℓ.val : ℝ))]
    exact pow_le_pow_left₀ hk0.le hℓ 2
  have hnum : 0 ≤ ((ℓ.val : ℝ)) ^ 2 - ((k : ℝ) - 1) ^ 2 := by nlinarith
  have habs : |dtnSymbol k ℓ| =
      (((ℓ.val : ℝ)) ^ 2 - ((k : ℝ) - 1) ^ 2) / |(ℓ.val : ℝ)| := by
    rw [dtnSymbol, abs_div, abs_abs, abs_of_nonneg hnum]
  rw [habs, le_div_iff₀ hl0]
  have hab : |(ℓ.val : ℝ)| * |(ℓ.val : ℝ)| = ((ℓ.val : ℝ)) ^ 2 := by
    rw [← sq_abs]; ring
  have hratio : ((k : ℝ) - 1) ^ 2 / (k : ℝ) ^ 2 * ((ℓ.val : ℝ)) ^ 2
      ≥ ((k : ℝ) - 1) ^ 2 := by
    rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  calc (1 - ((k : ℝ) - 1) ^ 2 / (k : ℝ) ^ 2) * |(ℓ.val : ℝ)| * |(ℓ.val : ℝ)|
      = ((ℓ.val : ℝ)) ^ 2 - ((k : ℝ) - 1) ^ 2 / (k : ℝ) ^ 2 * ((ℓ.val : ℝ)) ^ 2 := by
        rw [mul_assoc, hab]; ring
    _ ≤ ((ℓ.val : ℝ)) ^ 2 - ((k : ℝ) - 1) ^ 2 := by linarith
    _ = _ := rfl

/-! ### The membership equivalence (summability, cofinite exceptions) -/

/-- The small modes, a finite set (contains the kernel modes). -/
lemma small_modes_finite (k : ℕ) : {ℓ : NZ | |(ℓ.val : ℝ)| < k}.Finite := by
  apply Set.Finite.subset
    ((Set.finite_Icc (-(k : ℤ)) k).preimage Subtype.val_injective.injOn)
  intro ℓ hℓ
  have h : |(ℓ.val : ℝ)| < k := hℓ
  have h' : |ℓ.val| < (k : ℤ) := by exact_mod_cast h
  simp only [Set.mem_preimage, Set.mem_Icc]
  constructor <;> [linarith [neg_abs_le ℓ.val]; linarith [le_abs_self ℓ.val]]

/-- `MemDiag (dtnSymbol k)` is EXACTLY `Ḣ^{1/2}`-summability of the
physical coefficients: coercive tail + finite exceptions + upper bound. -/
theorem memDiag_dtn_iff {k : ℕ} (hk : 1 ≤ k) (x : NZ → ℂ) :
    MemDiag (dtnSymbol k) x ↔
      Summable (fun ℓ : NZ => (1 + |(ℓ.val : ℝ)|) * ‖x ℓ‖ ^ 2) := by
  constructor
  · intro h
    set c : ℝ := 1 - ((k : ℝ) - 1) ^ 2 / (k : ℝ) ^ 2 with hc
    have hc0 : 0 < c := one_sub_ratio_pos hk
    rw [← (small_modes_finite k).summable_compl_iff]
    have hbig : Summable (fun ℓ : ↥({ℓ : NZ | |(ℓ.val : ℝ)| < k}ᶜ) =>
        (2 / c) * (|dtnSymbol k ℓ.val| * ‖x ℓ.val‖ ^ 2)) :=
      (h.subtype _).mul_left _
    apply Summable.of_nonneg_of_le
      (fun ℓ => mul_nonneg (by positivity) (sq_nonneg _)) _ hbig
    rintro ⟨ℓ, hℓ⟩
    have hge : (k : ℝ) ≤ |(ℓ.val : ℝ)| := le_of_not_gt hℓ
    have h1 : (1 : ℝ) ≤ |(ℓ.val : ℝ)| := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have htail := dtnSymbol_tail_lower hk ℓ hge
    have hx0 : (0 : ℝ) ≤ ‖x ℓ‖ ^ 2 := by positivity
    calc (1 + |(ℓ.val : ℝ)|) * ‖x ℓ‖ ^ 2
        ≤ 2 * |(ℓ.val : ℝ)| * ‖x ℓ‖ ^ 2 := by nlinarith
      _ ≤ (2 / c) * (|dtnSymbol k ℓ| * ‖x ℓ‖ ^ 2) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
          nlinarith [mul_le_mul_of_nonneg_left htail
            (by positivity : (0 : ℝ) ≤ 2 * ‖x ℓ‖ ^ 2)]
  · intro h
    apply Summable.of_nonneg_of_le
      (fun ℓ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) _
      (h.mul_left (1 + ((k : ℝ) - 1) ^ 2))
    intro ℓ
    have hg := dtnSymbol_growth k ℓ
    have hx0 : (0 : ℝ) ≤ ‖x ℓ‖ ^ 2 := by positivity
    calc |dtnSymbol k ℓ| * ‖x ℓ‖ ^ 2
        ≤ ((1 + ((k : ℝ) - 1) ^ 2) * (1 + |(ℓ.val : ℝ)|)) * ‖x ℓ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hg hx0
      _ = (1 + ((k : ℝ) - 1) ^ 2) * ((1 + |(ℓ.val : ℝ)|) * ‖x ℓ‖ ^ 2) := by ring

/-! ### Weight and coordinate bookkeeping at `s = 1/2` -/

lemma weight_sq_half (n : ℤ) : weight (1 / 2 : ℝ) n ^ 2 = 1 + |(n : ℝ)| := by
  rw [weight, ← Real.rpow_natCast ((1 + |(n : ℝ)|) ^ ((1 : ℝ) / 2)) 2,
    ← Real.rpow_mul (by positivity)]
  norm_num

/-- The stored (weighted) coordinates of the bridged element. -/
def bridgeFun (x : NZ → ℂ) : ℤ → ℂ :=
  fun n => if h : n = 0 then 0 else (weight (1 / 2 : ℝ) n : ℂ) * x ⟨n, h⟩

lemma bridgeFun_normSq (x : NZ → ℂ) (n : ℤ) :
    ‖bridgeFun x n‖ ^ 2 =
      if h : n = 0 then 0 else (1 + |(n : ℝ)|) * ‖x ⟨n, h⟩‖ ^ 2 := by
  rw [bridgeFun]
  split_ifs with h
  · simp
  · rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (weight_pos _ n), weight_sq_half]

/-- Summability over `ℤ` reduces to `NZ` (the `0` term is a finite set). -/
lemma summable_int_iff_nz (f : ℤ → ℝ) :
    Summable f ↔ Summable (fun ℓ : NZ => f ℓ.val) := by
  rw [← (Set.finite_singleton (0 : ℤ)).summable_compl_iff]
  exact ((Equiv.subtypeEquivRight
    (fun n => by simp : ∀ n : ℤ, n ≠ 0 ↔ n ∈ (({0} : Set ℤ)ᶜ))).summable_iff
    (f := fun m : ↥(({0} : Set ℤ)ᶜ) => f m.val)).symm

/-! ### The bridge equivalence (LINEAR only — not bicontinuous, by design) -/

lemma bridge_memℓp {k : ℕ} (hk : 1 ≤ k) {x : NZ → ℂ}
    (hx : MemDiag (dtnSymbol k) x) : Memℓp (bridgeFun x) 2 := by
  apply memℓp_gen
  have h2 : ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) := by norm_num
  simp only [h2, Real.rpow_natCast]
  rw [summable_int_iff_nz]
  apply Summable.congr ((memDiag_dtn_iff hk x).mp hx)
  intro ℓ
  rw [bridgeFun_normSq, dite_eq_right ℓ.property, Subtype.coe_eta]

def bridgeSpace {k : ℕ} (hk : 1 ≤ k) (x : DomDiag (dtnSymbol k)) :
    Space (1 / 2 : ℝ) :=
  ⟨bridgeFun x.val, bridge_memℓp hk x.property⟩

lemma coeff_bridgeSpace {k : ℕ} (hk : 1 ≤ k) (x : DomDiag (dtnSymbol k))
    (ℓ : NZ) : coeff (1 / 2 : ℝ) (bridgeSpace hk x) ℓ.val = x.val ℓ := by
  have hw : ((weight (1 / 2 : ℝ) ℓ.val : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (weight_pos (1 / 2 : ℝ) ℓ.val).ne'
  rw [coeff]
  show (weight (1 / 2 : ℝ) ℓ.val : ℂ)⁻¹ * bridgeFun x.val ℓ.val = _
  rw [bridgeFun, dite_eq_right ℓ.property, ← mul_assoc, inv_mul_cancel₀ hw, one_mul,
    Subtype.coe_eta]

lemma coeff_bridgeSpace_zero {k : ℕ} (hk : 1 ≤ k) (x : DomDiag (dtnSymbol k)) :
    coeff (1 / 2 : ℝ) (bridgeSpace hk x) 0 = 0 := by
  rw [coeff]
  show _ * bridgeFun x.val 0 = 0
  rw [bridgeFun, dite_eq_left rfl, mul_zero]

lemma invFun_memDiag {k : ℕ} (hk : 1 ≤ k) (u : dotted (1 / 2 : ℝ)) :
    MemDiag (dtnSymbol k) (fun ℓ : NZ => coeff (1 / 2 : ℝ) u.val ℓ.val) := by
  rw [memDiag_dtn_iff hk]
  have h := (hasSum_weighted_sq (1 / 2 : ℝ) u.val).summable
  rw [summable_int_iff_nz] at h
  exact h.congr fun ℓ => by rw [weight_sq_half]

def dtnBridgeEquiv (k : ℕ) (hk : 1 ≤ k) :
    DomDiag (dtnSymbol k) ≃ₗ[ℂ] dotted (1 / 2 : ℝ) where
  toFun x := ⟨bridgeSpace hk x, coeff_bridgeSpace_zero hk x⟩
  invFun u := ⟨fun ℓ => coeff (1 / 2 : ℝ) u.val ℓ.val, invFun_memDiag hk u⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    funext n
    show bridgeFun (x + y).val n = bridgeFun x.val n + bridgeFun y.val n
    simp only [Submodule.coe_add, bridgeFun, Pi.add_apply]
    split_ifs
    · rw [add_zero]
    · ring
  map_smul' c x := by
    apply Subtype.ext
    apply Subtype.ext
    funext n
    show bridgeFun (c • x).val n = c • bridgeFun x.val n
    simp only [SetLike.val_smul, bridgeFun, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · rw [mul_zero]
    · ring
  left_inv x := by
    apply Subtype.ext
    funext ℓ
    exact coeff_bridgeSpace hk x ℓ
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    funext n
    show bridgeFun _ n = _
    rw [bridgeFun]
    split_ifs with h
    · subst h
      rw [← weight_mul_coeff (1 / 2 : ℝ) u.val 0,
        (mem_dotted (1 / 2 : ℝ) u.val).mp u.property, mul_zero]
    · exact weight_mul_coeff (1 / 2 : ℝ) u.val n

lemma dtnBridgeEquiv_coeff (k : ℕ) (hk : 1 ≤ k) (x : DomDiag (dtnSymbol k))
    (ℓ : NZ) :
    coeff (1 / 2 : ℝ) ((dtnBridgeEquiv k hk x) : dotted (1 / 2 : ℝ)).val ℓ.val
      = x.val ℓ :=
  coeff_bridgeSpace hk x ℓ

/-! ### The faithful DtN form -/

/-- The faithful half-order DtN form: `Bdiag` VERBATIM on the physical
Fourier coefficients (conjugate-first; no `2π` — see `duality_dottedDtnCLM`). -/
def faithfulDtnB (k : ℕ) (u v : dotted (1 / 2 : ℝ)) : ℂ :=
  ∑' ℓ : NZ, (dtnSymbol k ℓ : ℂ) *
    (starRingEnd ℂ) (coeff (1 / 2 : ℝ) u.val ℓ.val) *
      coeff (1 / 2 : ℝ) v.val ℓ.val

lemma faithfulDtnB_bridge (k : ℕ) (hk : 1 ≤ k)
    (x y : DomDiag (dtnSymbol k)) :
    faithfulDtnB k (dtnBridgeEquiv k hk x) (dtnBridgeEquiv k hk y)
      = Bdiag (dtnSymbol k) x.val y.val := by
  rw [faithfulDtnB, Bdiag]
  exact tsum_congr fun ℓ => by
    rw [dtnBridgeEquiv_coeff, dtnBridgeEquiv_coeff]

lemma faithfulDtnQ_bridge (k : ℕ) (hk : 1 ≤ k) (x : DomDiag (dtnSymbol k)) :
    (faithfulDtnB k (dtnBridgeEquiv k hk x) (dtnBridgeEquiv k hk x)).re
      = Qdiag (dtnSymbol k) x.val := by
  rw [faithfulDtnB_bridge k hk, Bdiag_self, Complex.ofReal_re]

/-! ### Transfer algebra (generic; both invariants through the equivalence) -/

section Transfer
variable {X Y : Type*} [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

lemma negativeIndex_le_of_equiv (e : X ≃ₗ[ℂ] Y) (Q : X → ℝ) (Q' : Y → ℝ)
    (h : ∀ x, Q' (e x) = Q x) :
    KsIndex.NegativeDensity.negativeIndex Q ≤
      KsIndex.NegativeDensity.negativeIndex Q' := by
  unfold KsIndex.NegativeDensity.negativeIndex
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfin => ?_
  let := hfin
  let eV := Submodule.equivMapOfInjective (e : X →ₗ[ℂ] Y) e.injective V
  have : FiniteDimensional ℂ (V.map (e : X →ₗ[ℂ] Y)) := eV.finiteDimensional
  refine le_iSup_of_le (V.map (e : X →ₗ[ℂ] Y)) (le_iSup_of_le ?_
    (le_iSup_of_le this ?_))
  · rintro y ⟨x, hx, rfl⟩ hy
    show Q' ((e : X →ₗ[ℂ] Y) x) < 0
    rw [show ((e : X →ₗ[ℂ] Y) x) = e x from rfl, h]
    exact hV x hx (fun hz => hy (by rw [hz, map_zero]))
  · rw [← eV.finrank_eq]

lemma negativeIndex_congr (e : X ≃ₗ[ℂ] Y) (Q : X → ℝ) (Q' : Y → ℝ)
    (h : ∀ x, Q' (e x) = Q x) :
    KsIndex.NegativeDensity.negativeIndex Q' =
      KsIndex.NegativeDensity.negativeIndex Q := by
  refine le_antisymm (negativeIndex_le_of_equiv e.symm Q' Q fun y => ?_)
    (negativeIndex_le_of_equiv e Q Q' h)
  rw [← h (e.symm y), e.apply_symm_apply]

/-- The nullity of a sesquilinear form on a module: the supremum of the
dimensions of finite-dimensional subspaces pairing to zero with EVERYTHING
(the general-module mirror of `FormIndex.formNullity` at `D = ⊤`). -/
def sesqNullity (B : X → X → ℂ) : ℕ∞ :=
  ⨆ (V : Submodule ℂ X) (_ : ∀ u ∈ V, ∀ w, B u w = 0)
    (_ : FiniteDimensional ℂ V), (Module.finrank ℂ V : ℕ∞)

lemma sesqNullity_le_of_equiv (e : X ≃ₗ[ℂ] Y) (B : X → X → ℂ)
    (B' : Y → Y → ℂ) (h : ∀ x y, B' (e x) (e y) = B x y) :
    sesqNullity B ≤ sesqNullity B' := by
  unfold sesqNullity
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfin => ?_
  let := hfin
  let eV := Submodule.equivMapOfInjective (e : X →ₗ[ℂ] Y) e.injective V
  have : FiniteDimensional ℂ (V.map (e : X →ₗ[ℂ] Y)) := eV.finiteDimensional
  refine le_iSup_of_le (V.map (e : X →ₗ[ℂ] Y)) (le_iSup_of_le ?_
    (le_iSup_of_le this ?_))
  · rintro y ⟨x, hx, rfl⟩ w
    have hxw := h x (e.symm w)
    rw [e.apply_symm_apply] at hxw
    show B' ((e : X →ₗ[ℂ] Y) x) w = 0
    rw [show ((e : X →ₗ[ℂ] Y) x) = e x from rfl, hxw]
    exact hV x hx (e.symm w)
  · rw [← eV.finrank_eq]

lemma sesqNullity_congr (e : X ≃ₗ[ℂ] Y) (B : X → X → ℂ) (B' : Y → Y → ℂ)
    (h : ∀ x y, B' (e x) (e y) = B x y) :
    sesqNullity B' = sesqNullity B := by
  refine le_antisymm (sesqNullity_le_of_equiv e.symm B' B fun x y => ?_)
    (sesqNullity_le_of_equiv e B B' h)
  rw [← h (e.symm x) (e.symm y), e.apply_symm_apply, e.apply_symm_apply]

end Transfer

/-- `formNullity` over a domain is the subtype-restricted `sesqNullity`
(the `NullOn` mirror of `formIndex_eq_negativeIndex`). -/
lemma formNullity_eq_sesqNullity {ι : Type*}
    (B : (ι → ℂ) → (ι → ℂ) → ℂ) (D : Submodule ℂ (ι → ℂ)) :
    formNullity B D = sesqNullity (fun u v : D => B u.val v.val) := by
  classical
  apply le_antisymm
  · unfold formNullity sesqNullity
    refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfin => ?_
    let := hfin
    let W := V.comap D.subtype
    let e : W ≃ₗ[ℂ] V := Submodule.comapSubtypeEquivOfLe hV.1
    have : FiniteDimensional ℂ W := FiniteDimensional.of_injective
      e.toLinearMap e.injective
    refine le_iSup_of_le W (le_iSup_of_le ?_ (le_iSup_of_le this ?_))
    · intro u hu w
      exact hV.2 u.val hu w.val w.property
    · rw [e.finrank_eq]
  · unfold formNullity sesqNullity
    refine iSup_le fun W => iSup_le fun hW => iSup_le fun hfin => ?_
    let := hfin
    let V := W.map D.subtype
    have hVD : V ≤ D := by
      rintro _ ⟨y, hy, rfl⟩
      exact y.property
    have hdim : Module.finrank ℂ V = Module.finrank ℂ W :=
      Submodule.finrank_map_subtype_eq D W
    have : FiniteDimensional ℂ V := by
      have hi := Submodule.equivMapOfInjective D.subtype
        (Submodule.injective_subtype D) W
      exact Module.Finite.equiv hi
    refine le_iSup_of_le V (le_iSup_of_le ⟨hVD, ?_⟩ (le_iSup_of_le this ?_))
    · rintro _ ⟨y, hy, rfl⟩ v hv
      exact hW y hy ⟨v, hv⟩
    · rw [hdim]

/-! ### The headlines: index `2k − 4`, nullity `2`, and the duality anchor -/

/-- **T-idx.** The faithful half-order DtN form has Morse index `2k − 4`. -/
theorem faithfulNopIndex {k : ℕ} (hk : 3 ≤ k) :
    KsIndex.NegativeDensity.negativeIndex
      (fun u : dotted (1 / 2 : ℝ) => (faithfulDtnB k u u).re)
      = ((2 * k - 4 : ℕ) : ℕ∞) := by
  have hk1 : 1 ≤ k := by omega
  rw [← nop_index hk, formIndex_eq_negativeIndex]
  exact negativeIndex_congr (dtnBridgeEquiv k hk1)
    (fun x : DomDiag (dtnSymbol k) => Qdiag (dtnSymbol k) x.val)
    (fun u => (faithfulDtnB k u u).re)
    (fun x => faithfulDtnQ_bridge k hk1 x)

/-- **T-nul.** The faithful half-order DtN form has nullity `2` — transferred
through the linear equivalence rather than inferred from density. -/
theorem faithfulNopNullity {k : ℕ} (hk : 3 ≤ k) :
    sesqNullity (faithfulDtnB k) = ((2 : ℕ) : ℕ∞) := by
  have hk1 : 1 ≤ k := by omega
  rw [← nop_nullity hk, formNullity_eq_sesqNullity]
  exact sesqNullity_congr (dtnBridgeEquiv k hk1)
    (fun x y : DomDiag (dtnSymbol k) => Bdiag (dtnSymbol k) x.val y.val)
    (faithfulDtnB k)
    (fun x y => faithfulDtnB_bridge k hk1 x y)

/-- `ℤ`-tsums of families vanishing at `0` reduce to `NZ`. -/
lemma tsum_int_eq_nz (f : ℤ → ℂ) (h0 : f 0 = 0) :
    ∑' n : ℤ, f n = ∑' ℓ : NZ, f ℓ.val := by
  rw [← tsum_subtype_eq_of_support_subset
    (s := {n : ℤ | n ≠ 0}) (fun n hn => by
      simp only [Function.mem_support] at hn
      exact fun h => hn (h ▸ h0))]
  rfl

/-- **T-link, the fidelity anchor.** The faithful form IS the actual
half-order DtN duality pairing (`dottedDtnCLM` against the `Ḣ^{1/2}`
element), up to the arclength constant `2π` — not a parallel construction. -/
theorem duality_dottedDtnCLM (k : ℕ) (u v : dotted (1 / 2 : ℝ)) :
    duality (1 / 2 : ℝ) ((dottedDtnCLM k u) : Space (-(1 / 2 : ℝ)))
      (v : Space (1 / 2 : ℝ))
      = (2 * Real.pi : ℂ) * faithfulDtnB k u v := by
  rw [duality_eq_tsum, faithfulDtnB]
  congr 1
  have h0 : (starRingEnd ℂ)
      (coeff (-(1 / 2 : ℝ)) ((dottedDtnCLM k u) : Space (-(1 / 2 : ℝ))) 0)
        * coeff (1 / 2 : ℝ) (v : Space (1 / 2 : ℝ)) 0 = 0 := by
    rw [(mem_dotted _ _).mp (dottedDtnCLM k u).property, map_zero, zero_mul]
  rw [tsum_int_eq_nz _ h0]
  refine tsum_congr fun ℓ => ?_
  rw [coeff_dottedDtnCLM k u ℓ, map_mul, Complex.conj_ofReal]

end KsIndex.DtnBridge
