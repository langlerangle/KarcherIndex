module

/-
KsIndexLean — Reconstruction and splitting of the k = 3 slit character domain.

Sector coefficients on the residue classes `6n+1` and `6m+4` reconstruct a mean-zero
`H^{1/2}` circle trace. The reconstruction and coefficient extraction are inverse on
traces supported in the class `ℓ % 3 = 1`, which corresponds to character `j % 3 = 2`
under the rotation convention used here.

The seam is realized as an `L²` identity: the upper trace has coefficients
`e^{iπα} • mulA α w` when the lower trace has coefficients `w ∈ Domς`. Its Sobolev
membership follows from the graph-domain hypothesis. Reverse arc gluing converts
this full-circle identity into the two boundary-arc conditions.

For `0 < j < 3`, `j % 3 = 2`, and `sin (πα) ≠ 0`, the linear equivalence `Ψ` splits
`paperSlitCharacterDomain α j` into `Domς` and two zero-trace character remainders.
Its inverse extends the lower and seam-determined upper traces and restores the
remainders. The forward graph-domain membership uses the nonintegral-phase
hypothesis; the inverse construction itself is defined for every real `α`.

`PaperSlitIndexPIN` uses this splitting for the form, index and weak-nullity
identifications. `PaperSlitIndexPINConj` supplies the conjugate character case.
-/
public import KsIndexLean.PaperSlitBoundaryForm

@[expose] public section


noncomputable section
open scoped Real
open MeasureTheory
namespace KsIndex.PaperSlitAdapter
open KsIndex.Trace KsIndex.Sector KsIndex.CircleSobolev KsIndex.FormIndex KsIndex.WeakH1
  KsIndex.CircleQ KsIndex.Spectral

/-! ### The reconstruction `traceOfSector : {v // MemSector v} → dotted (1/2)` -/

/-- The class-lattice injection `Idx → ℤ`: `inl n ↦ 6n+1`, `inr m ↦ 6m+4`. -/
def idxToℤ (i : Idx) : ℤ := (idxToNZ i).val

@[simp] lemma idxToℤ_inl (n : ℤ) : idxToℤ (Sum.inl n) = 6 * n + 1 := rfl
@[simp] lemma idxToℤ_inr (m : ℤ) : idxToℤ (Sum.inr m) = 6 * m + 4 := rfl

lemma idxToℤ_injective : Function.Injective idxToℤ :=
  fun _ _ h => idxToNZ_injective (Subtype.ext h)

/-- The range of `idxToℤ` is exactly the class `{ℓ % 3 = 1}`. -/
lemma idxToℤ_mem_range_iff (ℓ : ℤ) : (∃ i : Idx, idxToℤ i = ℓ) ↔ ℓ % 3 = 1 := by
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | inl n => simp only [idxToℤ_inl]; omega
    | inr m => simp only [idxToℤ_inr]; omega
  · intro h
    obtain ⟨q, hq⟩ : ∃ q : ℤ, ℓ = 3 * q + 1 := ⟨ℓ / 3, by omega⟩
    rcases Int.even_or_odd q with ⟨n, hn⟩ | ⟨k, hk⟩
    · exact ⟨Sum.inl n, by simp only [idxToℤ_inl]; omega⟩
    · exact ⟨Sum.inr k, by simp only [idxToℤ_inr]; omega⟩

/-- Insert sector coefficients on the class lattice, zero elsewhere. -/
def sectorInsertCoeff (v : Idx → ℂ) : ℤ → ℂ := Function.extend idxToℤ v 0

@[simp] lemma sectorInsertCoeff_lattice (v : Idx → ℂ) (i : Idx) :
    sectorInsertCoeff v (idxToℤ i) = v i :=
  idxToℤ_injective.extend_apply v 0 i

lemma sectorInsertCoeff_off (v : Idx → ℂ) (ℓ : ℤ) (hℓ : ¬ ∃ i, idxToℤ i = ℓ) :
    sectorInsertCoeff v ℓ = 0 :=
  Function.extend_apply' _ _ _ hℓ

/-- `1 ≤ |6n+1|` on the reals (integrality). -/
lemma one_le_abs_six_add_one (n : ℤ) : (1 : ℝ) ≤ |6 * (n : ℝ) + 1| := by
  have hz : (6 * n + 1 : ℤ) ≠ 0 := by omega
  have hi : (1 : ℤ) ≤ |6 * n + 1| := Int.one_le_abs hz
  have : ((|6 * n + 1| : ℤ) : ℝ) = |6 * (n : ℝ) + 1| := by rw [Int.cast_abs]; push_cast; ring
  calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
    _ ≤ ((|6 * n + 1| : ℤ) : ℝ) := by exact_mod_cast hi
    _ = |6 * (n : ℝ) + 1| := this

/-- `1 ≤ |6m+4|` on the reals (integrality). -/
lemma one_le_abs_six_add_four (m : ℤ) : (1 : ℝ) ≤ |6 * (m : ℝ) + 4| := by
  have hz : (6 * m + 4 : ℤ) ≠ 0 := by omega
  have hi : (1 : ℤ) ≤ |6 * m + 4| := Int.one_le_abs hz
  have : ((|6 * m + 4| : ℤ) : ℝ) = |6 * (m : ℝ) + 4| := by rw [Int.cast_abs]; push_cast; ring
  calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
    _ ≤ ((|6 * m + 4| : ℤ) : ℝ) := by exact_mod_cast hi
    _ = |6 * (m : ℝ) + 4| := this

/-- Weighted `H^{1/2}` summability of the inserted coefficients, from `MemSector`. -/
lemma sectorInsert_summable {v : Idx → ℂ} (hv : MemSector v) :
    Summable (fun ℓ : ℤ => weight (1 / 2 : ℝ) ℓ ^ 2 * ‖sectorInsertCoeff v ℓ‖ ^ 2) := by
  have hw (m : ℤ) : weight (1 / 2 : ℝ) m ^ 2 = 1 + |(m : ℝ)| := by rw [weight_sq]; norm_num
  have hP : Summable (fun n : ℤ =>
      weight (1 / 2 : ℝ) (idxToℤ (Sum.inl n)) ^ 2 * ‖v (Sum.inl n)‖ ^ 2) := by
    refine (hv.1.mul_left 2).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    rw [idxToℤ_inl, hw, show ((6 * n + 1 : ℤ) : ℝ) = 6 * (n : ℝ) + 1 by push_cast; ring]
    nlinarith [one_le_abs_six_add_one n, sq_nonneg ‖v (Sum.inl n)‖,
      mul_nonneg (by linarith [one_le_abs_six_add_one n] : (0:ℝ) ≤ |6 * (n:ℝ) + 1| - 1)
        (sq_nonneg ‖v (Sum.inl n)‖)]
  have hM : Summable (fun m : ℤ =>
      weight (1 / 2 : ℝ) (idxToℤ (Sum.inr m)) ^ 2 * ‖v (Sum.inr m)‖ ^ 2) := by
    refine (hv.2.mul_left 2).of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    rw [idxToℤ_inr, hw, show ((6 * m + 4 : ℤ) : ℝ) = 6 * (m : ℝ) + 4 by push_cast; ring]
    nlinarith [one_le_abs_six_add_four m, sq_nonneg ‖v (Sum.inr m)‖,
      mul_nonneg (by linarith [one_le_abs_six_add_four m] : (0:ℝ) ≤ |6 * (m:ℝ) + 4| - 1)
        (sq_nonneg ‖v (Sum.inr m)‖)]
  have hs : Summable (fun i : Idx => weight (1 / 2 : ℝ) (idxToℤ i) ^ 2 * ‖v i‖ ^ 2) :=
    Summable.sum _ hP hM
  have he := (summable_extend_zero idxToℤ_injective).mpr hs
  refine he.congr (fun ℓ => ?_)
  by_cases hm : ∃ i, idxToℤ i = ℓ
  · obtain ⟨i, rfl⟩ := hm
    rw [idxToℤ_injective.extend_apply, sectorInsertCoeff_lattice]
  · rw [Function.extend_apply' _ _ _ hm, sectorInsertCoeff_off v ℓ hm]
    simp

/-- The reconstructed `H^{1/2}` trace of a sector vector: class-lattice coefficients `= v`,
zero off the class. -/
def traceReconstruct (v : Idx → ℂ) (hv : MemSector v) : Space (1 / 2 : ℝ) :=
  ofCoefficients (1 / 2 : ℝ) (sectorInsertCoeff v) (sectorInsert_summable hv)

@[simp] lemma coeff_traceReconstruct (v : Idx → ℂ) (hv : MemSector v) (ℓ : ℤ) :
    coeff (1 / 2 : ℝ) (traceReconstruct v hv) ℓ = sectorInsertCoeff v ℓ :=
  coeff_ofCoefficients _ _ _ _

/-- The reconstruction is mean-zero (`0 ∉` class), hence dotted. -/
lemma traceReconstruct_mem_dotted (v : Idx → ℂ) (hv : MemSector v) :
    traceReconstruct v hv ∈ dotted (1 / 2 : ℝ) := by
  rw [mem_dotted, coeff_traceReconstruct]
  exact sectorInsertCoeff_off v 0 (fun h => by have := (idxToℤ_mem_range_iff 0).mp h; omega)

/-- **The reconstruction** `traceOfSector : {v // MemSector v} → dotted (1/2)`. -/
def traceOfSector (v : Idx → ℂ) (hv : MemSector v) : dotted (1 / 2 : ℝ) :=
  ⟨traceReconstruct v hv, traceReconstruct_mem_dotted v hv⟩

@[simp] lemma coeff_traceOfSector (v : Idx → ℂ) (hv : MemSector v) (ℓ : ℤ) :
    coeff (1 / 2 : ℝ) (traceOfSector v hv).val ℓ = sectorInsertCoeff v ℓ :=
  coeff_ofCoefficients (1 / 2 : ℝ) (sectorInsertCoeff v) (sectorInsert_summable hv) ℓ

/-- Class support of the reconstruction: coefficients vanish off `{ℓ % 3 = 1}`. -/
lemma traceOfSector_class_support (v : Idx → ℂ) (hv : MemSector v) :
    ∀ ℓ : ℤ, ℓ % 3 ≠ 1 → coeff (1 / 2 : ℝ) (traceOfSector v hv).val ℓ = 0 := by
  intro ℓ hℓ
  rw [coeff_traceOfSector]
  exact sectorInsertCoeff_off v ℓ (fun h => hℓ ((idxToℤ_mem_range_iff ℓ).mp h))

/-- Round-trip 1: `sectorOfTrace ∘ traceOfSector = id`. -/
lemma sectorOfTrace_traceOfSector (v : Idx → ℂ) (hv : MemSector v) :
    sectorOfTrace (traceOfSector v hv) = v := by
  funext i
  cases i with
  | inl n =>
      rw [sectorOfTrace_inl, show (6 * n + 1 : ℤ) = idxToℤ (Sum.inl n) from rfl,
        coeff_traceOfSector, sectorInsertCoeff_lattice]
  | inr m =>
      rw [sectorOfTrace_inr, show (6 * m + 4 : ℤ) = idxToℤ (Sum.inr m) from rfl,
        coeff_traceOfSector, sectorInsertCoeff_lattice]

/-- Round-trip 2: `traceOfSector ∘ sectorOfTrace = id` on class-supported traces. -/
lemma traceOfSector_sectorOfTrace (f : dotted (1 / 2 : ℝ))
    (hf : ∀ ℓ : ℤ, ℓ % 3 ≠ 1 → coeff (1 / 2 : ℝ) f.val ℓ = 0) :
    traceOfSector (sectorOfTrace f) (memSector_sectorOfTrace f) = f := by
  apply Subtype.ext
  apply coeff_injective (1 / 2 : ℝ)
  funext ℓ
  rw [coeff_traceOfSector]
  by_cases hm : ∃ i, idxToℤ i = ℓ
  · obtain ⟨i, rfl⟩ := hm
    rw [sectorInsertCoeff_lattice]
    cases i with
    | inl n => rw [sectorOfTrace_inl, idxToℤ_inl]
    | inr m => rw [sectorOfTrace_inr, idxToℤ_inr]
  · rw [sectorInsertCoeff_off (sectorOfTrace f) ℓ hm]
    exact (hf ℓ (fun h => hm ((idxToℤ_mem_range_iff ℓ).mpr h))).symm

/-- Character membership (`j ≡ 2 mod 3`): the reconstruction lands in `character (1/2) j 3`. -/
lemma traceOfSector_mem_character {j : ℕ} (hj : j % 3 = 2) (v : Idx → ℂ) (hv : MemSector v) :
    (traceOfSector v hv).val ∈ character (1 / 2 : ℝ) (j : ℤ) (3 : ℤ) := by
  rw [mem_character]
  intro n hn
  have hn3 : n % 3 ≠ 1 := fun h1 => hn ⟨(n + j) / 3, by omega⟩
  exact traceOfSector_class_support v hv n hn3

/-! ### the seam realization (`toL2 t₁ = arcMul α (toL2 t₂)`) -/


/-- Two `L²` functions with equal Fourier coefficients are equal. -/
lemma lp_ext_of_fourierCoeff {u v : Lp ℂ 2 circleMeasure}
    (h : ∀ n : ℤ, circleFourierCoeff u n = circleFourierCoeff v n) : u = v := by
  apply circleFourierCLE.injective
  ext n
  rw [circleFourierCLE_apply, circleFourierCLE_apply, h]

/-- **Class-support preservation for `σ·`.**  If `F` is class-supported (`{d%3=1}`), so is `σ·F`. -/
lemma sigmaMul_class_support (F : Lp ℂ 2 circleMeasure)
    (hF : ∀ d : ℤ, d % 3 ≠ 1 → circleFourierCoeff F d = 0) :
    ∀ d : ℤ, d % 3 ≠ 1 → circleFourierCoeff (sigmaMul F) d = 0 := by
  intro d hd
  rw [circleFourierCoeff_sigmaMul]
  have hzero : (fun e : ℤ => circleFourierCoeff sigmaField (d - e) * circleFourierCoeff F e)
      = fun _ => 0 := by
    funext e
    by_cases he : e % 3 = 1
    · rw [circleFourierCoeff_sigmaField_not_dvd (d - e) (by omega), zero_mul]
    · rw [hF e he, mul_zero]
  rw [hzero, tsum_zero]

/-- **Class-support preservation for `M_α`.**  If `F` is class-supported, so is `arcMul α F`. -/
lemma arcMul_class_support (α : ℝ) (F : Lp ℂ 2 circleMeasure)
    (hF : ∀ d : ℤ, d % 3 ≠ 1 → circleFourierCoeff F d = 0) :
    ∀ d : ℤ, d % 3 ≠ 1 → circleFourierCoeff (arcMul α F) d = 0 := by
  intro d hd
  have hσ := sigmaMul_class_support F hF d hd
  rw [← circleFourierCLE_apply]
  simp only [arcMul, map_smul, map_sub, lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, circleFourierCLE_apply]
  rw [hF d hd, hσ]
  ring

/-- The `L²` realization of a reconstructed trace is class-supported. -/
lemma toL2_traceOfSector_class_support (v : Idx → ℂ) (hv : MemSector v) :
    ∀ d : ℤ, d % 3 ≠ 1 →
      circleFourierCoeff (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (traceOfSector v hv).val) d = 0 := by
  intro d hd
  rw [fourierCoeff_toL2]
  exact traceOfSector_class_support v hv d hd

/-- Class-lattice Fourier coefficients of the `L²` realization of `traceOfSector v` recover `v`. -/
lemma fourierCoeff_toL2_traceOfSector (v : Idx → ℂ) (hv : MemSector v) :
    (fun i : Idx =>
      circleFourierCoeff (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (traceOfSector v hv).val)
        (idxToNZ i).val) = v := by
  funext i
  rw [fourierCoeff_toL2]
  change coeff (1/2 : ℝ) (traceOfSector v hv).val (idxToℤ i) = v i
  rw [coeff_traceOfSector, sectorInsertCoeff_lattice]

/-- **The seam `L²` identity.**  For `w ∈ Domς` (`j≡2`), the reconstructed upper trace
`traceOfSector (e^{iπα}·mulA α w)` realizes in `L²` as `arcMul α` of the reconstructed lower trace
`traceOfSector w`. The upper trace is reconstructed from coefficients using the
given Sobolev-membership witness. -/
lemma seam_toL2 (α : ℝ) (w : Idx → ℂ) (hw : w ∈ Domς)
    (hw' : MemSector (Complex.exp (Complex.I * (α * Real.pi)) • mulA α w)) :
    toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (traceOfSector (Complex.exp (Complex.I * (α * Real.pi)) • mulA α w) hw').val
      = arcMul α (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (traceOfSector w hw.1).val) := by
  apply lp_ext_of_fourierCoeff
  intro d
  rw [fourierCoeff_toL2, coeff_traceOfSector]
  by_cases hm : ∃ i, idxToℤ i = d
  · obtain ⟨i, rfl⟩ := hm
    rw [sectorInsertCoeff_lattice]
    have hcls := toL2_traceOfSector_class_support w hw.1
    have hkey := congrFun (coeff_arcMul_eq_mulA α
      (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (traceOfSector w hw.1).val) hcls) i
    rw [fourierCoeff_toL2_traceOfSector w hw.1] at hkey
    rw [show idxToℤ i = (idxToNZ i).val from rfl, hkey]
  · rw [sectorInsertCoeff_off _ d hm]
    exact (arcMul_class_support α _ (toL2_traceOfSector_class_support w hw.1) d
      (fun h => hm ((idxToℤ_mem_range_iff d).mpr h))).symm

/-- Phase variant of `arcTrace_eq_iff_ae`: an arc-trace scalar relation as an a.e. identity. -/
lemma arcTrace_smul_eq_iff_ae (A : Set Circle₁) (c : ℂ) (u v : ComplexH1) :
    arcTrace A u = c • arcTrace A v ↔
      (diskTraceCLM u : Circle₁ → ℂ)
        =ᵐ[circleMeasure.restrict A] fun w => c * (diskTraceCLM v : Circle₁ → ℂ) w := by
  constructor
  · intro h
    have hcoe : (arcTrace A u : Circle₁ → ℂ)
        =ᵐ[circleMeasure.restrict A] ((c • arcTrace A v : Lp ℂ 2 _) : Circle₁ → ℂ) :=
      Filter.EventuallyEq.of_eq (congrArg
        (fun f : Lp ℂ 2 (circleMeasure.restrict A) => (f : Circle₁ → ℂ)) h)
    filter_upwards [arcTrace_coe_ae A u, hcoe, Lp.coeFn_smul c (arcTrace A v),
      arcTrace_coe_ae A v] with w hu hcw hsm hv
    rw [← hu, hcw, hsm, Pi.smul_apply, hv, smul_eq_mul]
  · intro h
    apply Lp.ext
    filter_upwards [arcTrace_coe_ae A u, h, Lp.coeFn_smul c (arcTrace A v),
      arcTrace_coe_ae A v] with w hu hh hsm hv
    rw [hu, hh, hsm, Pi.smul_apply, hv, smul_eq_mul]

/-- **The reverse arc-gluing.**  The full-circle multiplier relation
`diskTrace u₁ =ᵐ arcStepFun·diskTrace u₂` splits into the two seam arc-conditions (arc1: equality;
arc0: `e^{2πiα}` phase) — the converse of `seam_full_relation`, needed for `Ψ.symm` membership. -/
lemma arcs_of_full_relation (α : ℝ) (u₁ u₂ : ComplexH1)
    (hfull : (diskTraceCLM u₁ : Circle₁ → ℂ)
      =ᵐ[circleMeasure] fun w => arcStepFun α w * (diskTraceCLM u₂ : Circle₁ → ℂ) w) :
    arcTrace (boundaryArc 3 1) u₁ = arcTrace (boundaryArc 3 1) u₂ ∧
    arcTrace (boundaryArc 3 0) u₁
      = Complex.exp ((2 * Real.pi * α) * Complex.I) • arcTrace (boundaryArc 3 0) u₂ := by
  have hres1 := hfull.filter_mono (ae_mono (Measure.restrict_le_self (s := boundaryArc 3 1)))
  have hres0 := hfull.filter_mono (ae_mono (Measure.restrict_le_self (s := boundaryArc 3 0)))
  refine ⟨(arcTrace_eq_iff_ae _ u₁ u₂).mpr (hres1.trans ?_),
    (arcTrace_smul_eq_iff_ae _ _ u₁ u₂).mpr (hres0.trans ?_)⟩
  · rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_boundaryArc 3 1)]
    filter_upwards with w hw
    have hpos : (0 : ℝ) < ((w : ℂ) ^ 3).re := by
      have := (mem_boundaryArc 3 1 w).mp hw
      simp only [pow_one, neg_one_mul] at this; linarith
    simp only [arcStepFun]
    split_ifs with hc
    · rw [one_mul]
    · exact absurd (le_of_lt hpos) hc
  · rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_boundaryArc 3 0)]
    filter_upwards with w hw
    have hlt : ((w : ℂ) ^ 3).re < 0 := by
      have := (mem_boundaryArc 3 0 w).mp hw; simpa using this
    simp only [arcStepFun]
    split_ifs with hc
    · exact absurd hc (not_le.mpr hlt)
    · rfl


/-! ### The sector trace of a disk function (linear, via `coeff`/`halfDiskTrace`) -/

/-- The sector coefficients of a disk function's boundary trace. -/
def sectorTrace (x : ComplexH1) : Idx → ℂ :=
  fun i => coeff (1 / 2 : ℝ) (halfDiskTrace x) (idxToℤ i)

lemma sectorTrace_add (x y : ComplexH1) : sectorTrace (x + y) = sectorTrace x + sectorTrace y := by
  funext i
  show coeff (1 / 2 : ℝ) (halfDiskTrace (x + y)) (idxToℤ i)
    = coeff (1 / 2 : ℝ) (halfDiskTrace x) (idxToℤ i)
      + coeff (1 / 2 : ℝ) (halfDiskTrace y) (idxToℤ i)
  rw [halfDiskTrace_add]
  exact map_add (coeffLinear (1 / 2 : ℝ) (idxToℤ i)) (halfDiskTrace x) (halfDiskTrace y)

lemma sectorTrace_smul (c : ℂ) (x : ComplexH1) : sectorTrace (c • x) = c • sectorTrace x := by
  funext i
  show coeff (1 / 2 : ℝ) (halfDiskTrace (c • x)) (idxToℤ i)
    = c * coeff (1 / 2 : ℝ) (halfDiskTrace x) (idxToℤ i)
  rw [halfDiskTrace_smul]
  exact map_smul (coeffLinear (1 / 2 : ℝ) (idxToℤ i)) c (halfDiskTrace x)

/-- The sector trace agrees with `sectorOfTrace ∘ charTrace` on a character hemisphere. -/
lemma sectorTrace_eq_sectorOfTrace {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) :
    sectorTrace u = sectorOfTrace (charTrace hj0 hjk hu) := by
  funext i
  cases i with
  | inl n =>
      show coeff (1 / 2 : ℝ) (halfDiskTrace u) (6 * n + 1)
        = coeff (1 / 2 : ℝ) (charTrace hj0 hjk hu).val (6 * n + 1)
      rfl
  | inr m =>
      show coeff (1 / 2 : ℝ) (halfDiskTrace u) (6 * m + 4)
        = coeff (1 / 2 : ℝ) (charTrace hj0 hjk hu).val (6 * m + 4)
      rfl

/-- `diskTraceCLM (jext t) = toL2 t` — the extension's `L²` trace is its data. -/
lemma diskTraceCLM_jext (t : dotted (1 / 2 : ℝ)) :
    diskTraceCLM (jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) t) = toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) t.val := by
  rw [← toL2_halfDiskTrace, ← halfDiskTraceCLM_apply, jacobiExtensionCLM_halfTrace]

/-! ### The pair splitting equivalence `Ψ` -/

/-- The zero-trace character remainder submodule. -/
def charRem (j : ℕ) : Submodule ℂ ComplexH1 :=
  zeroTraceDomain Set.univ ⊓ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)

variable {α : ℝ} {j : ℕ}

/-- Component-1 membership: the hemisphere-2 sector trace lands in `Domς`. -/
lemma sectorTrace_mem_Domς (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    (hsin : Real.sin (α * Real.pi) ≠ 0) (u : paperSlitCharacterDomain α j) :
    sectorTrace u.val.2 ∈ Domς := by
  have h := sectorOfTrace_charTrace_mem_Domς hj0 hjk hj hsin u
  rwa [← sectorTrace_eq_sectorOfTrace hj0 hjk (paperSlitCharacter_character u).2] at h

/-- `charTrace` is additive in the hemisphere. -/
lemma charTrace_add {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) {x y : ComplexH1}
    (hx : x ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j))
    (hy : y ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j))
    (hxy : x + y ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) :
    charTrace hj0 hjk hxy = charTrace hj0 hjk hx + charTrace hj0 hjk hy := by
  apply Subtype.ext
  change halfDiskTraceCLM (x + y) = halfDiskTraceCLM x + halfDiskTraceCLM y
  rw [map_add]

/-- `charTrace` is homogeneous in the hemisphere. -/
lemma charTrace_smul {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) (c : ℂ) {x : ComplexH1}
    (hx : x ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j))
    (hcx : c • x ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) :
    charTrace hj0 hjk hcx = c • charTrace hj0 hjk hx := by
  apply Subtype.ext
  change halfDiskTraceCLM (c • x) = c • halfDiskTraceCLM x
  rw [map_smul]

/-- `traceOfSector` is independent of the `MemSector` witness. -/
lemma traceOfSector_proof_irrel (v : Idx → ℂ) (h1 h2 : MemSector v) :
    traceOfSector v h1 = traceOfSector v h2 := by
  apply Subtype.ext
  apply coeff_injective (1 / 2 : ℝ)
  funext ℓ
  simp only [coeff_traceOfSector]

/-- The `MemSector` witness for the upper reconstruction, from `Domς`. -/
lemma memSector_expMulA {w : Idx → ℂ} (hw : w ∈ Domς) :
    MemSector (Complex.exp (Complex.I * (α * Real.pi)) • mulA α w) :=
  memSector_smul _ (mulA_mem_Domς α hw).1

/-- The inverse pair: extend the reconstructed lower trace and the seam-determined upper trace,
add back the remainders. -/
def ΨinvPair (α : ℝ) {j : ℕ} (p : Domς × charRem j × charRem j) : DiskPairH1 :=
  (jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3)
      (traceOfSector (Complex.exp (Complex.I * (α * Real.pi)) • mulA α p.1.val)
        (memSector_expMulA p.1.property)) + p.2.1.val,
   jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (traceOfSector p.1.val p.1.property.1) + p.2.2.val)

/-- **`Ψ.symm` membership.**  The inverse pair lands in `paperSlitCharacterDomain α j`: character on
each hemisphere (jext of a class-supported reconstruction + character remainder), and the seam (the
`L²` seam identity + `arcMul_coe` + reverse arc-gluing). -/
lemma ΨinvPair_mem (α : ℝ) (hj : j % 3 = 2)
    (p : Domς × charRem j × charRem j) : ΨinvPair α p ∈ paperSlitCharacterDomain α j := by
  set w := p.1.val with hwdef
  have hw : w ∈ Domς := p.1.property
  set t2 := traceOfSector w hw.1 with ht2
  set t1 := traceOfSector (Complex.exp (Complex.I * (α * Real.pi)) • mulA α w)
    (memSector_expMulA hw) with ht1
  set r1 := p.2.1.val with hr1
  set r2 := p.2.2.val with hr2
  have hr1mem := p.2.1.property
  have hr2mem := p.2.2.property
  have hr1z : r1 ∈ zeroTraceDomain Set.univ := (Submodule.mem_inf.mp hr1mem).1
  have hr2z : r2 ∈ zeroTraceDomain Set.univ := (Submodule.mem_inf.mp hr2mem).1
  have hr1c : r1 ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j) :=
    (Submodule.mem_inf.mp hr1mem).2
  have hr2c : r2 ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j) :=
    (Submodule.mem_inf.mp hr2mem).2
  -- character membership of the two reconstructions
  have ht1char : t1.val ∈ character (1 / 2 : ℝ) (j : ℤ) (3 : ℤ) :=
    traceOfSector_mem_character hj _ (memSector_expMulA hw)
  have ht2char : t2.val ∈ character (1 / 2 : ℝ) (j : ℤ) (3 : ℤ) :=
    traceOfSector_mem_character hj w hw.1
  have hjext1 : jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) t1
      ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j) :=
    jacobiExtensionH1_mem_character (by norm_num : (2 : ℕ) ≤ 3) j t1.val ht1char
  have hjext2 : jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) t2
      ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j) :=
    jacobiExtensionH1_mem_character (by norm_num : (2 : ℕ) ≤ 3) j t2.val ht2char
  -- disk traces of the two hemispheres
  have hd1 : diskTraceCLM (jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) t1 + r1) = toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) t1.val := by
    rw [map_add, diskTraceCLM_jext, (mem_fullZeroTrace_iff r1).mp hr1z, add_zero]
  have hd2 : diskTraceCLM (jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) t2 + r2) = toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) t2.val := by
    rw [map_add, diskTraceCLM_jext, (mem_fullZeroTrace_iff r2).mp hr2z, add_zero]
  have hseam : toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) t1.val = arcMul α (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) t2.val) :=
    seam_toL2 α w hw (memSector_expMulA hw)
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · -- paperSlitDomain: the seam
    rw [paperSlitDomain, mem_slitTraceDomain]
    have hfull : (diskTraceCLM (ΨinvPair α p).1 : Circle₁ → ℂ)
        =ᵐ[circleMeasure]
          fun x => arcStepFun α x * (diskTraceCLM (ΨinvPair α p).2 : Circle₁ → ℂ) x := by
      show (diskTraceCLM (jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) t1 + r1) : Circle₁ → ℂ)
        =ᵐ[circleMeasure] fun x => arcStepFun α x *
          (diskTraceCLM (jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) t2 + r2) : Circle₁ → ℂ) x
      rw [hd1, hseam, hd2]
      exact arcMul_coe α (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) t2.val)
    exact arcs_of_full_relation α _ _ hfull
  · -- pairCharacterDomain
    rw [mem_pairCharacterDomain_iff]
    exact ⟨(weakCharacterDomain _ _).add_mem hjext1 hr1c,
      (weakCharacterDomain _ _).add_mem hjext2 hr2c⟩

/-! ### Bridge lemmas for the equivalence laws -/

/-- `sectorTrace` in the raw Fourier form (matches the seam identity's shape). -/
lemma sectorTrace_eq_fourier (x : ComplexH1) :
    sectorTrace x = fun i : Idx => circleFourierCoeff (diskTraceCLM x) (idxToNZ i).val := by
  funext i
  show coeff (1 / 2 : ℝ) (halfDiskTrace x) (idxToℤ i)
    = circleFourierCoeff (diskTraceCLM x) (idxToNZ i).val
  rw [show idxToℤ i = (idxToNZ i).val from rfl, coeff_halfDiskTrace]

/-- `traceOfSector` respects equality of the sector vector. -/
lemma traceOfSector_congr {A B : Idx → ℂ} (hAB : A = B) (hA : MemSector A) (hB : MemSector B) :
    traceOfSector A hA = traceOfSector B hB := by
  subst hAB; exact traceOfSector_proof_irrel A hA hB

/-- Reconstructing from a character hemisphere's sector trace recovers its `charTrace`. -/
lemma traceOfSector_sectorTrace {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2) {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j))
    (h : MemSector (sectorTrace u)) :
    traceOfSector (sectorTrace u) h = charTrace hj0 hjk hu := by
  apply Subtype.ext
  apply coeff_injective (1 / 2 : ℝ)
  funext ℓ
  rw [coeff_traceOfSector]
  by_cases hm : ∃ i, idxToℤ i = ℓ
  · obtain ⟨i, rfl⟩ := hm
    rw [sectorInsertCoeff_lattice]
    cases i with
    | inl n =>
        show sectorTrace u (Sum.inl n)
          = coeff (1 / 2 : ℝ) (charTrace hj0 hjk hu).val (idxToℤ (Sum.inl n))
        rw [idxToℤ_inl]; rfl
    | inr m =>
        show sectorTrace u (Sum.inr m)
          = coeff (1 / 2 : ℝ) (charTrace hj0 hjk hu).val (idxToℤ (Sum.inr m))
        rw [idxToℤ_inr]; rfl
  · rw [sectorInsertCoeff_off (sectorTrace u) ℓ hm]
    exact (charTrace_class_support hj0 hjk hj hu ℓ
      (fun h1 => hm ((idxToℤ_mem_range_iff ℓ).mpr h1))).symm

/-- The sector trace of a Jacobi extension is the extended data's class-lattice coefficients. -/
lemma sectorTrace_jext (t : dotted (1 / 2 : ℝ)) :
    sectorTrace (jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) t)
      = fun i : Idx => coeff (1 / 2 : ℝ) t.val (idxToℤ i) := by
  funext i
  show coeff (1 / 2 : ℝ) (halfDiskTrace (jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) t)) (idxToℤ i)
    = coeff (1 / 2 : ℝ) t.val (idxToℤ i)
  rw [← halfDiskTraceCLM_apply, jacobiExtensionCLM_halfTrace]

/-- `circleFourierCoeff` of the zero function vanishes. -/
lemma circleFourierCoeff_zero (n : ℤ) : circleFourierCoeff (0 : Lp ℂ 2 circleMeasure) n = 0 := by
  rw [← circleFourierCLE_apply, map_zero]; rfl

/-- The sector trace of a full-zero-trace function vanishes. -/
lemma sectorTrace_zeroTrace {r : ComplexH1} (hr : r ∈ zeroTraceDomain Set.univ) :
    sectorTrace r = 0 := by
  funext i
  rw [sectorTrace_eq_fourier, (mem_fullZeroTrace_iff r).mp hr]
  exact circleFourierCoeff_zero _

/-- `halfDiskTraceCLM` of a full-zero-trace function vanishes. -/
lemma halfDiskTraceCLM_zeroTrace {r : ComplexH1} (hr : r ∈ zeroTraceDomain Set.univ) :
    halfDiskTraceCLM r = 0 := by
  apply toL2_injective (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [map_zero, halfDiskTraceCLM_apply, toL2_halfDiskTrace, (mem_fullZeroTrace_iff r).mp hr]

/-- The sector trace of `jext (traceOfSector v)` recovers `v`. -/
lemma sectorTrace_jext_traceOfSector (v : Idx → ℂ) (hv : MemSector v) :
    sectorTrace (jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (traceOfSector v hv)) = v := by
  rw [sectorTrace_jext]
  funext i
  show coeff (1 / 2 : ℝ) (traceOfSector v hv).val (idxToℤ i) = v i
  rw [coeff_traceOfSector, sectorInsertCoeff_lattice]

/-- `charTrace` of a `jext t + (zero-trace remainder)` recovers `t`. -/
lemma charTrace_jext_rem {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) (t : dotted (1 / 2 : ℝ))
    {r : ComplexH1} (hr : r ∈ zeroTraceDomain Set.univ)
    (hmem : jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) t + r
      ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) :
    charTrace hj0 hjk hmem = t := by
  apply Subtype.ext
  change halfDiskTraceCLM (jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) t + r) = t.val
  rw [map_add, halfDiskTraceCLM_zeroTrace hr, add_zero, jacobiExtensionCLM_halfTrace]

/-! ### `ΨinvPair` component computations (for `right_inv`) -/

/-- The Domς component of `Ψ ∘ Ψ.symm`. -/
lemma sectorTrace_ΨinvPair_snd (α : ℝ) (p : Domς × charRem j × charRem j) :
    sectorTrace (ΨinvPair α p).2 = p.1.val := by
  show sectorTrace (jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (traceOfSector p.1.val p.1.property.1) + p.2.2.val)
    = p.1.val
  rw [sectorTrace_add, sectorTrace_jext_traceOfSector,
    sectorTrace_zeroTrace (Submodule.mem_inf.mp p.2.2.property).1, add_zero]

/-- Hemisphere-1 `charTrace` of the reconstruction. -/
lemma charTrace_ΨinvPair_fst {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) (α : ℝ)
    (p : Domς × charRem j × charRem j)
    (hmem : (ΨinvPair α p).1 ∈ weakCharacterDomain (-(2 * Real.pi) / 3)
      (KsIndex.FormIndex.zeta 3 ^ j)) :
    charTrace hj0 hjk hmem = traceOfSector
      (Complex.exp (Complex.I * (α * Real.pi)) • mulA α p.1.val) (memSector_expMulA p.1.property) :=
  charTrace_jext_rem hj0 hjk _ (Submodule.mem_inf.mp p.2.1.property).1 hmem

/-- Hemisphere-2 `charTrace` of the reconstruction. -/
lemma charTrace_ΨinvPair_snd {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) (α : ℝ)
    (p : Domς × charRem j × charRem j)
    (hmem : (ΨinvPair α p).2 ∈ weakCharacterDomain (-(2 * Real.pi) / 3)
      (KsIndex.FormIndex.zeta 3 ^ j)) :
    charTrace hj0 hjk hmem = traceOfSector p.1.val p.1.property.1 :=
  charTrace_jext_rem hj0 hjk _ (Submodule.mem_inf.mp p.2.2.property).1 hmem

/-- Remainder-1 cancellation. -/
lemma ΨinvPair_fst_sub (α : ℝ) (p : Domς × charRem j × charRem j) :
    (ΨinvPair α p).1 - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (traceOfSector
        (Complex.exp (Complex.I * (α * Real.pi)) • mulA α p.1.val) (memSector_expMulA p.1.property))
      = p.2.1.val := by
  show jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (traceOfSector
        (Complex.exp (Complex.I * (α * Real.pi)) • mulA α p.1.val) (memSector_expMulA p.1.property))
      + p.2.1.val
      - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (traceOfSector
        (Complex.exp (Complex.I * (α * Real.pi)) • mulA α p.1.val) (memSector_expMulA p.1.property))
      = p.2.1.val
  abel

/-- Remainder-2 cancellation. -/
lemma ΨinvPair_snd_sub (α : ℝ) (p : Domς × charRem j × charRem j) :
    (ΨinvPair α p).2 - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (traceOfSector p.1.val p.1.property.1)
      = p.2.2.val := by
  show jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (traceOfSector p.1.val p.1.property.1) + p.2.2.val
      - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (traceOfSector p.1.val p.1.property.1) = p.2.2.val
  abel

/-! ### The pair splitting equivalence `Ψ` -/

set_option maxHeartbeats 800000 in
/-- For `0 < j < 3`, `j % 3 = 2` and `sin (πα) ≠ 0`, the slit character domain splits as
the sector graph-domain `Domς` (hemisphere-2 trace) times two zero-trace character remainders. -/
def Ψ (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2) (hsin : Real.sin (α * Real.pi) ≠ 0) :
    paperSlitCharacterDomain α j ≃ₗ[ℂ] Domς × charRem j × charRem j where
  toFun u :=
    (⟨sectorTrace u.val.2, sectorTrace_mem_Domς hj0 hjk hj hsin u⟩,
     ⟨u.val.1 - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character u).1),
        charHemi_remainder_mem hj0 hjk (paperSlitCharacter_character u).1⟩,
     ⟨u.val.2 - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character u).2),
        charHemi_remainder_mem hj0 hjk (paperSlitCharacter_character u).2⟩)
  map_add' u v := by
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · show sectorTrace (u + v).val.2 = sectorTrace u.val.2 + sectorTrace v.val.2
      rw [show (u + v).val.2 = u.val.2 + v.val.2 from rfl, sectorTrace_add]
    · show (u + v).val.1
          - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character (u + v)).1)
        = (u.val.1 - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character u).1))
          + (v.val.1
              - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character v).1))
      rw [charTrace_add hj0 hjk (paperSlitCharacter_character u).1
          (paperSlitCharacter_character v).1 (paperSlitCharacter_character (u + v)).1, map_add,
        show (u + v).val.1 = u.val.1 + v.val.1 from rfl]
      abel
    · show (u + v).val.2
          - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character (u + v)).2)
        = (u.val.2 - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character u).2))
          + (v.val.2
              - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character v).2))
      rw [charTrace_add hj0 hjk (paperSlitCharacter_character u).2
          (paperSlitCharacter_character v).2 (paperSlitCharacter_character (u + v)).2, map_add,
        show (u + v).val.2 = u.val.2 + v.val.2 from rfl]
      abel
  map_smul' c u := by
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · show sectorTrace (c • u).val.2 = c • sectorTrace u.val.2
      rw [show (c • u).val.2 = c • u.val.2 from rfl, sectorTrace_smul]
    · show (c • u).val.1
          - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character (c • u)).1)
        = c • (u.val.1
            - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character u).1))
      rw [charTrace_smul hj0 hjk c (paperSlitCharacter_character u).1
          (paperSlitCharacter_character (c • u)).1, map_smul,
        show (c • u).val.1 = c • u.val.1 from rfl, smul_sub]
    · show (c • u).val.2
          - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character (c • u)).2)
        = c • (u.val.2
            - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character u).2))
      rw [charTrace_smul hj0 hjk c (paperSlitCharacter_character u).2
          (paperSlitCharacter_character (c • u)).2, map_smul,
        show (c • u).val.2 = c • u.val.2 from rfl, smul_sub]
  invFun p := ⟨ΨinvPair α p, ΨinvPair_mem α hj p⟩
  left_inv u := by
    apply Subtype.ext
    have hseam : Complex.exp (Complex.I * (α * Real.pi)) • mulA α (sectorTrace u.val.2)
        = sectorTrace u.val.1 := by
      rw [sectorTrace_eq_fourier u.val.1, sectorTrace_eq_fourier u.val.2]
      exact (paperSlit_seam_coeff_eq_mulA hj u).symm
    have hH2 : MemSector (sectorTrace u.val.1) := hseam ▸
      memSector_expMulA (sectorTrace_mem_Domς hj0 hjk hj hsin u)
    refine Prod.ext ?_ ?_
    · -- hemisphere 1
      show jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (traceOfSector
            (Complex.exp (Complex.I * (α * Real.pi)) • mulA α (sectorTrace u.val.2))
            (memSector_expMulA (sectorTrace_mem_Domς hj0 hjk hj hsin u)))
          + (u.val.1
              - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character u).1))
        = u.val.1
      rw [traceOfSector_congr hseam _ hH2,
        traceOfSector_sectorTrace hj0 hjk hj (paperSlitCharacter_character u).1 hH2]
      abel
    · -- hemisphere 2
      show jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (traceOfSector (sectorTrace u.val.2)
            ((sectorTrace_mem_Domς hj0 hjk hj hsin u).1))
          + (u.val.2
              - jacobiExtensionCLM (by norm_num : (2 : ℕ) ≤ 3) (charTrace hj0 hjk (paperSlitCharacter_character u).2))
        = u.val.2
      rw [traceOfSector_sectorTrace hj0 hjk hj (paperSlitCharacter_character u).2
        ((sectorTrace_mem_Domς hj0 hjk hj hsin u).1)]
      abel
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · exact sectorTrace_ΨinvPair_snd α p
    · dsimp only
      rw [charTrace_ΨinvPair_fst hj0 hjk α p
        (paperSlitCharacter_character ⟨ΨinvPair α p, ΨinvPair_mem α hj p⟩).1]
      exact ΨinvPair_fst_sub α p
    · dsimp only
      rw [charTrace_ΨinvPair_snd hj0 hjk α p
        (paperSlitCharacter_character ⟨ΨinvPair α p, ΨinvPair_mem α hj p⟩).2]
      exact ΨinvPair_snd_sub α p


end KsIndex.PaperSlitAdapter
