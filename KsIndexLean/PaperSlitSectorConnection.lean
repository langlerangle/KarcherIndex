module

/-
# The circle sign multiplier and sector coefficients

For circle `L²` functions with Fourier support in `1+3ℤ`, multiplication by
`sigmaField` corresponds to the sector sign operator `sgn` on `Idx = ℤ ⊕ ℤ`.
The two progressions are `inl n ↦ 6n+1` and `inr m ↦ 6m+4`.

The convolution identity from `PaperSlitIntertwiner` reduces to one progression
because the square-wave coefficients vanish except at differences `6k+3`.
At those differences they equal `chat k`; reflection of this kernel identifies
both components of the sector operator.

The phased arc multiplier is `exp(iπα) (cos(πα) I - i sin(πα) σ)`. Its sector
coefficients are therefore `exp(iπα) • mulA α`, including the scalar phase.
The final lemmas glue the two boundary-arc conditions almost everywhere and
transport that full-circle relation to sector coefficients. Sobolev domain
and index/nullity transport are separate interfaces.
-/
public import KsIndexLean.PaperSlitIntertwiner
public import KsIndexLean.PaperSlitSectorAdapter
public import KsIndexLean.FullBoundaryMatching

@[expose] public section


noncomputable section
open scoped Real
open MeasureTheory
namespace KsIndex.PaperSlitAdapter
open KsIndex.Trace KsIndex.CircleQ KsIndex.SIsometry KsIndex.Sector KsIndex.WeakH1

/-- The physical arc-sign coefficient at a cross-half difference is the sector kernel `chat`. -/
lemma circleFourierCoeff_sigmaField_eq_chat (k : ℤ) :
    circleFourierCoeff sigmaField (6 * k + 3) = (chat k : ℂ) := by
  rw [circleFourierCoeff_sigmaField_six_add_three, chat]

/-- `chat` reflection specialized to the `inl` reindex: `chat (a−m−1) = chat (m−a)`. -/
lemma chat_inl_aux (a m : ℤ) : chat (a - m - 1) = chat (m - a) := by
  have h := chat_refl (a - m)
  rw [show -(a - m) = m - a from by ring] at h
  exact h.symm

/-- **inr half**: the `6b+4`-coefficient of `σ·F` (class-supported `F`) is `convS` of the
`{6n+1}`-progression — matching `sgn (inr b)`. -/
lemma sigmaMul_coeff_inr (F : Lp ℂ 2 circleMeasure)
    (hF : ∀ d : ℤ, d % 3 ≠ 1 → circleFourierCoeff F d = 0) (b : ℤ) :
    circleFourierCoeff (sigmaMul F) (6 * b + 4)
      = convS (fun n => circleFourierCoeff F (6 * n + 1)) b := by
  rw [circleFourierCoeff_sigmaMul]
  have hinj : Function.Injective (fun n : ℤ => 6 * n + 1) := fun x y h => by dsimp only at h; omega
  have hsupp : ∀ d ∉ Set.range (fun n : ℤ => 6 * n + 1),
      circleFourierCoeff sigmaField (6 * b + 4 - d) * circleFourierCoeff F d = 0 := by
    intro d hd
    have hmod : d % 6 ≠ 1 := fun h => hd ⟨d / 6, by dsimp only; omega⟩
    by_cases hd3 : d % 3 = 1
    · have hd6 : d % 6 = 4 := by omega
      rw [show (6 * b + 4 - d) = 6 * (b - d / 6) from by omega,
        circleFourierCoeff_sigmaField_six_mul, zero_mul]
    · rw [hF d hd3, mul_zero]
  rw [← hinj.tsum_eq (Function.support_subset_iff'.2 hsupp)]
  unfold convS
  refine tsum_congr (fun n => ?_)
  rw [show (6 * b + 4 - (6 * n + 1)) = 6 * (b - n) + 3 from by ring,
    circleFourierCoeff_sigmaField_eq_chat]

/-- **inl half**: the `6a+1`-coefficient of `σ·F` (class-supported `F`) is `convK Tker` of the
`{6m+4}`-progression — matching `sgn (inl a)`. -/
lemma sigmaMul_coeff_inl (F : Lp ℂ 2 circleMeasure)
    (hF : ∀ d : ℤ, d % 3 ≠ 1 → circleFourierCoeff F d = 0) (a : ℤ) :
    circleFourierCoeff (sigmaMul F) (6 * a + 1)
      = convK Tker (fun m => circleFourierCoeff F (6 * m + 4)) a := by
  rw [circleFourierCoeff_sigmaMul]
  have hinj : Function.Injective (fun m : ℤ => 6 * m + 4) := fun x y h => by dsimp only at h; omega
  have hsupp : ∀ d ∉ Set.range (fun m : ℤ => 6 * m + 4),
      circleFourierCoeff sigmaField (6 * a + 1 - d) * circleFourierCoeff F d = 0 := by
    intro d hd
    have hmod : d % 6 ≠ 4 := fun h => hd ⟨d / 6, by dsimp only; omega⟩
    by_cases hd3 : d % 3 = 1
    · have hd6 : d % 6 = 1 := by omega
      rw [show (6 * a + 1 - d) = 6 * (a - d / 6) from by omega,
        circleFourierCoeff_sigmaField_six_mul, zero_mul]
    · rw [hF d hd3, mul_zero]
  rw [← hinj.tsum_eq (Function.support_subset_iff'.2 hsupp)]
  unfold convK
  refine tsum_congr (fun m => ?_)
  rw [show (6 * a + 1 - (6 * m + 4)) = 6 * (a - m - 1) + 3 from by ring,
    circleFourierCoeff_sigmaField_eq_chat]
  simp only [Tker]
  rw [chat_inl_aux]

/-- **The sector connection.**  For class-supported `F` (Fourier support in `{ℓ % 3 = 1}`), the
physical coefficient function of `σ·F` on the class lattice `Idx = ℤ⊕ℤ` (via `idxToNZ`) equals the
abstract sector half-swap `ς = sgn` applied to `F`'s coefficient function.  This binds the physical
arc-sign multiplication to the sector operator (`convS`/`convK`, kernel `chat`). -/
theorem sectorConnection (F : Lp ℂ 2 circleMeasure)
    (hF : ∀ d : ℤ, d % 3 ≠ 1 → circleFourierCoeff F d = 0) :
    (fun i : Idx => circleFourierCoeff (sigmaMul F) (idxToNZ i).val)
      = sgn (fun i : Idx => circleFourierCoeff F (idxToNZ i).val) := by
  funext i
  cases i with
  | inl a =>
      rw [sgn_inl]
      simp only [idxToNZ_inl_val, idxToNZ_inr_val]
      exact sigmaMul_coeff_inl F hF a
  | inr b =>
      rw [sgn_inr]
      simp only [idxToNZ_inl_val, idxToNZ_inr_val]
      exact sigmaMul_coeff_inr F hF b

/-! ### The phased arc multiplier

The physical multiplier `M_α = exp(iπα)(cos(πα) I - i sin(πα) σ)` becomes
`exp(iπα) • mulA α` under the sector coefficient identification. This is an
`L²` identity; membership in a half-order graph domain is a separate condition.
-/

/-- The physical arc-step multiplier `M_α = e^{iπα}(cos(απ)·I − i sin(απ)·σ)` on `L²`. -/
def arcMul (α : ℝ) (F : Lp ℂ 2 circleMeasure) : Lp ℂ 2 circleMeasure :=
  Complex.exp (Complex.I * (α * Real.pi)) •
    ((Real.cos (α * Real.pi) : ℂ) • F - (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • sigmaMul F)

/-- On class-supported `F`, the physical arc-step multiplier `M_α`
transports (via `idxToNZ`) to `e^{iπα}·mulA α` on the sector coefficients: the scalar phase is retained explicitly. -/
theorem coeff_arcMul_eq_mulA (α : ℝ) (F : Lp ℂ 2 circleMeasure)
    (hF : ∀ d : ℤ, d % 3 ≠ 1 → circleFourierCoeff F d = 0) :
    (fun i : Idx => circleFourierCoeff (arcMul α F) (idxToNZ i).val)
      = Complex.exp (Complex.I * (α * Real.pi)) •
          mulA α (fun i : Idx => circleFourierCoeff F (idxToNZ i).val) := by
  have hi : ∀ i : Idx, circleFourierCoeff (sigmaMul F) (idxToNZ i).val
      = sgn (fun j : Idx => circleFourierCoeff F (idxToNZ j).val) i :=
    congrFun (sectorConnection F hF)
  funext i
  rw [← circleFourierCLE_apply]
  simp only [arcMul, map_smul, map_sub, lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, circleFourierCLE_apply, mulA]
  rw [hi i]

/-! ### `M_α` as the physical arc-step multiplier

`M_α` is exactly multiplication by the arc-step function (`1` on the welded arc1, `e^{2πiα}` on the
slit arc0) — the boundary multiplier the seam produces (`paperSlitCharacter_seam`,
`PaperSlitAdapterAssembly`: `t₁=t₂` on arc1, `t₁=e^{2πiα}t₂` on arc0).  This is the L²-level content
of `t₁ = M_α·t₂`; composing with `coeff_arcMul_eq_mulA` turns the physical seam into `mulA`. -/

/-- The arc-step function: `1` when `Re(w³) ≥ 0` and `e^{2πiα}` otherwise.
Its value on the six arc endpoints is chosen to be `1`. -/
def arcStepFun (α : ℝ) (w : Circle₁) : ℂ :=
  if 0 ≤ ((w : ℂ) ^ 3).re then 1 else Complex.exp (2 * Real.pi * α * Complex.I)

/-- Euler's formula identifies the pointwise multiplier with the arc-step function:
`e^{iπα}(cos απ − i sin απ·σ)` is `1` on arc1 (`σ=+1`) and `e^{2πiα}` on arc0 (`σ=−1`). -/
lemma arcStep_pointwise (α : ℝ) (w : Circle₁) :
    Complex.exp (Complex.I * (α * Real.pi)) *
        ((Real.cos (α * Real.pi) : ℂ) - Complex.I * (Real.sin (α * Real.pi) : ℂ) * sigmaField w)
      = arcStepFun α w := by
  set z : ℂ := (α : ℂ) * (Real.pi : ℂ) with hz
  have hcos : (Real.cos (α * Real.pi) : ℂ) = Complex.cos z := by
    rw [hz, ← Complex.ofReal_mul, Complex.ofReal_cos]
  have hsin : (Real.sin (α * Real.pi) : ℂ) = Complex.sin z := by
    rw [hz, ← Complex.ofReal_mul, Complex.ofReal_sin]
  have hE : Complex.cos z + Complex.I * Complex.sin z = Complex.exp (Complex.I * z) := by
    rw [mul_comm Complex.I z, Complex.exp_mul_I]; ring
  have hEneg : Complex.cos z - Complex.I * Complex.sin z = Complex.exp (-(Complex.I * z)) := by
    rw [show -(Complex.I * z) = (-z) * Complex.I by ring, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg]; ring
  unfold arcStepFun sigmaField
  rw [hcos, hsin]
  split_ifs with h
  · rw [mul_one, hEneg, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  · rw [show (Complex.cos z - Complex.I * Complex.sin z * (-1))
        = Complex.cos z + Complex.I * Complex.sin z by ring, hE, ← Complex.exp_add]
    congr 1
    rw [hz]; ring

/-- The `L²` representative of `arcMul` agrees almost everywhere with
multiplication by `arcStepFun`. -/
lemma arcMul_coe (α : ℝ) (F : Lp ℂ 2 circleMeasure) :
    arcMul α F =ᵐ[circleMeasure] fun w => arcStepFun α w * (F : Circle₁ → ℂ) w := by
  filter_upwards [Lp.coeFn_smul (Complex.exp (Complex.I * (α * Real.pi)))
      ((Real.cos (α * Real.pi) : ℂ) • F - (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • sigmaMul F),
    Lp.coeFn_sub ((Real.cos (α * Real.pi) : ℂ) • F)
      ((Complex.I * (Real.sin (α * Real.pi) : ℂ)) • sigmaMul F),
    Lp.coeFn_smul (Real.cos (α * Real.pi) : ℂ) F,
    Lp.coeFn_smul (Complex.I * (Real.sin (α * Real.pi) : ℂ)) (sigmaMul F),
    sigmaMul_coe F] with w h1 h2 h3 h4 h5
  show (arcMul α F : Circle₁ → ℂ) w = arcStepFun α w * (F : Circle₁ → ℂ) w
  rw [arcMul]
  simp only [h1, h2, h3, h4, h5, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [← arcStep_pointwise α w]
  ring

/-! ### Gluing the boundary-arc relations

Equality on arc1 and multiplication by `exp(2πiα)` on arc0 combine into one
almost-everywhere full-circle relation. The arcs cover the circle up to a null
set, so no pointwise endpoint trace condition is required.
-/

/-- a.e. coefficient form of `arcTrace` (unfolding the boundary-restriction CLM). -/
lemma arcTrace_coe_ae (A : Set Circle₁) (u : ComplexH1) :
    (arcTrace A u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] (diskTraceCLM u : Circle₁ → ℂ) :=
  boundaryRestrict_coe_ae A (diskTraceCLM u)

/-- **The arc-gluing.**  The two seam arc-conditions (arc1: `t₁=t₂`; arc0: `t₁=e^{2πiα}t₂`) glue to
the full-circle multiplier relation `diskTrace u₁ =ᵐ arcStepFun·diskTrace u₂` — the `hrel` for
`seam_coeff_eq_mulA`.  (Matches `paperSlitCharacter_seam` on the paper-slit pair.) -/
lemma seam_full_relation (α : ℝ) (u₁ u₂ : ComplexH1)
    (h1 : arcTrace (boundaryArc 3 1) u₁ = arcTrace (boundaryArc 3 1) u₂)
    (h0 : arcTrace (boundaryArc 3 0) u₁
        = Complex.exp ((2 * Real.pi * α) * Complex.I) • arcTrace (boundaryArc 3 0) u₂) :
    (diskTraceCLM u₁ : Circle₁ → ℂ)
      =ᵐ[circleMeasure] fun w => arcStepFun α w * (diskTraceCLM u₂ : Circle₁ → ℂ) w := by
  have ha1 : (diskTraceCLM u₁ : Circle₁ → ℂ)
      =ᵐ[circleMeasure.restrict (boundaryArc 3 1)] (diskTraceCLM u₂ : Circle₁ → ℂ) :=
    (arcTrace_eq_iff_ae _ u₁ u₂).mp h1
  have hh0 : (arcTrace (boundaryArc 3 0) u₁ : Circle₁ → ℂ)
      =ᵐ[circleMeasure.restrict (boundaryArc 3 0)]
        ((Complex.exp ((2 * Real.pi * α) * Complex.I) • arcTrace (boundaryArc 3 0) u₂ :
          Lp ℂ 2 (circleMeasure.restrict (boundaryArc 3 0))) : Circle₁ → ℂ) :=
    Filter.EventuallyEq.of_eq (congrArg
      (fun f : Lp ℂ 2 (circleMeasure.restrict (boundaryArc 3 0)) => (f : Circle₁ → ℂ)) h0)
  have ha0 : (diskTraceCLM u₁ : Circle₁ → ℂ)
      =ᵐ[circleMeasure.restrict (boundaryArc 3 0)]
        fun w =>
          Complex.exp ((2 * Real.pi * α) * Complex.I) * (diskTraceCLM u₂ : Circle₁ → ℂ) w := by
    filter_upwards [arcTrace_coe_ae (boundaryArc 3 0) u₁, hh0,
      Lp.coeFn_smul (Complex.exp ((2 * Real.pi * α) * Complex.I)) (arcTrace (boundaryArc 3 0) u₂),
      arcTrace_coe_ae (boundaryArc 3 0) u₂] with w hw1 hwh hwsm hw2
    rw [← hw1, hwh, hwsm, Pi.smul_apply, hw2, smul_eq_mul]
  have ha1' := (ae_restrict_iff' (measurableSet_boundaryArc 3 1)).mp ha1
  have ha0' := (ae_restrict_iff' (measurableSet_boundaryArc 3 0)).mp ha0
  filter_upwards [ha1', ha0', boundaryArc_cover_ae (show 1 ≤ 3 by norm_num)] with w hw1 hw0 hw
  rcases hw with hw0mem | hw1mem
  · have hlt : ((w : ℂ) ^ 3).re < 0 := by
      have := (mem_boundaryArc 3 0 w).mp hw0mem; simpa using this
    simp only [arcStepFun]
    split_ifs with hc
    · exact absurd hc (not_le.mpr hlt)
    · exact hw0 hw0mem
  · have hpos : (0 : ℝ) < ((w : ℂ) ^ 3).re := by
      have := (mem_boundaryArc 3 1 w).mp hw1mem
      simp only [pow_one, neg_one_mul] at this; linarith
    simp only [arcStepFun]
    split_ifs with hc
    · rw [one_mul]; exact hw1 hw1mem
    · exact absurd (le_of_lt hpos) hc

/-! ### Transport of the full seam relation

`seam_coeff_eq_mulA` takes two explicit inputs: an almost-everywhere full-circle
multiplier relation and Fourier support of the second trace in `1+3ℤ`.
It then identifies the sector coefficients, including the phase `exp(iπα)`.
-/

/-- **Seam → `mulA`.**  Given the full-circle multiplier relation `t₁ =ᵐ arcStepFun·t₂` and class
support of `t₂` (`{ℓ%3=1}`), the sector coefficients of `t₁` are `e^{iπα}·mulA α` of those of `t₂`
(compose `arcMul_coe` + `coeff_arcMul_eq_mulA`). -/
lemma seam_coeff_eq_mulA (α : ℝ) (t₁ t₂ : Lp ℂ 2 circleMeasure)
    (hrel : t₁ =ᵐ[circleMeasure] fun w => arcStepFun α w * (t₂ : Circle₁ → ℂ) w)
    (hcls : ∀ d : ℤ, d % 3 ≠ 1 → circleFourierCoeff t₂ d = 0) :
    (fun i : Idx => circleFourierCoeff t₁ (idxToNZ i).val)
      = Complex.exp (Complex.I * (α * Real.pi)) •
          mulA α (fun i : Idx => circleFourierCoeff t₂ (idxToNZ i).val) := by
  have hco : circleFourierCoeff t₁ = circleFourierCoeff (arcMul α t₂) :=
    circleFourierCoeff_congr_ae (hrel.trans (arcMul_coe α t₂).symm)
  have hstep : (fun i : Idx => circleFourierCoeff t₁ (idxToNZ i).val)
      = fun i : Idx => circleFourierCoeff (arcMul α t₂) (idxToNZ i).val := by
    funext i; rw [hco]
  rw [hstep]
  exact coeff_arcMul_eq_mulA α t₂ hcls

end KsIndex.PaperSlitAdapter
