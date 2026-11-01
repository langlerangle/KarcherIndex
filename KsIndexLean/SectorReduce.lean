module

/-
KsIndexLean — SectorReduce: circle-model parametrizations of the R_α eigenspaces.

For the reduction in [ksindexi, iop-qop_equiv], a circle sequence `w` lifts to

    ι_tan w = (inl = w, inr = i·coefT α·convS w),
    coefT α = sin(απ)/(1+cos(απ)).

For `w ∈ MemDom` this belongs to the sector domain `Domς`. When
`1+cos(απ) ≠ 0`, it lies in the eigenvalue `−1` space of `R_α`, satisfies
`M_α u = P u`, and pulls `NQform` back to `2·Qform (coefT α)`.
The corresponding eigenvalue `+1` construction uses
`coefC α = −sin(απ)/(1−cos(απ))` and requires `1−cos(απ) ≠ 0`.
On `0 < α < 1`, these coefficients are the tangent and negative cotangent
of `απ/2`; the sign disappears in the quadratic form's squared parameter.

Restriction to the `inl` coordinates recovers `w`. The reverse reconstruction
holds on the respective eigenspace with the stated denominator hypothesis.
Domain membership supplies the weighted summability needed for convolution;
the definitions themselves are total on arbitrary coefficient sequences.
-/
public import KsIndexLean.SectorForm

@[expose] public section


noncomputable section

namespace KsIndex.SectorReduce

open KsIndex.CircleQ KsIndex.SIsometry KsIndex.Sector KsIndex.SectorForm

/-- Restriction to the `+`-half (`inl`) lattice. It is a left inverse of
both embeddings and a right inverse on the respective eigenspaces under the
nonzero-denominator hypotheses of the reconstruction lemmas. -/
def restrictL (u : Idx → ℂ) : ℤ → ℂ := fun n => u (Sum.inl n)

@[simp] lemma restrictL_apply (u : Idx → ℂ) (n : ℤ) : restrictL u n = u (Sum.inl n) := rfl

/-- `restrictL` as a genuine `ℂ`-linear map — it is just the projection onto the
`inl`-coordinates, hence linear *unconditionally* (no summability needed, unlike
the embeddings `ι`).  This is the map the index transport rides on. -/
def restrictLₗ : (Idx → ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun := restrictL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma restrictLₗ_apply (u : Idx → ℂ) : restrictLₗ u = restrictL u := rfl

/-- The `inl`-restriction of a sector-domain vector is a circle-domain vector:
`u ∈ Domς ⟹ restrictL u ∈ MemDom`.  The two circle summabilities are exactly
`MemSector u`'s `inl` half and `MemSector (ς u)`'s `inr` half — the latter
because `convS (restrictL u) = (ς u)|_inr` by definition of `ς`.  (This is
where the `ς`-bundling of the domain pays off.) -/
lemma restrictL_memDom {u : Idx → ℂ} (hu : u ∈ Domς) : MemDom (restrictL u) := by
  have h := mem_Domς.mp hu
  -- `convS (restrictL u) m` is *definitionally* `ς u (inr m)` (`sgn_inr` is `rfl`).
  exact ⟨h.1.1, h.2.2⟩

/-- The `tan`-embedding coefficient `sin(απ)/(1+cos(απ))`, equal to
`tan(απ/2)` on `0 < α < 1`. -/
def coefT (α : ℝ) : ℝ := Real.sin (α * Real.pi) / (1 + Real.cos (α * Real.pi))

/-- The coefficient map `w ↦ (inl = w, inr = i·coefT·convS w)`.
For `w ∈ MemDom` and `1+cos(απ) ≠ 0`, it parametrizes the eigenvalue `−1`
space of `R_α` inside `Domς`. -/
def iotaTan (α : ℝ) (w : ℤ → ℂ) : Idx → ℂ := fun i => i.elim
  (fun n => w n)
  (fun m => (Complex.I * (coefT α : ℂ)) * convS w m)

@[simp] lemma iotaTan_inl (α : ℝ) (w : ℤ → ℂ) (n : ℤ) :
    iotaTan α w (.inl n) = w n := rfl

@[simp] lemma iotaTan_inr (α : ℝ) (w : ℤ → ℂ) (m : ℤ) :
    iotaTan α w (.inr m) = (Complex.I * (coefT α : ℂ)) * convS w m := rfl

/-- The half-swap `ς` of an embedded vector: `ς(ι_tan w) = (inl = i·coefT·w,
inr = convS w)` — the `inl`-half collapses via `T∘S = id`. -/
lemma sgn_iotaTan (α : ℝ) {w : ℤ → ℂ} (hw : Summable fun n : ℤ => ‖w n‖ ^ 2) :
    sgn (iotaTan α w) = fun i => i.elim
      (fun a => (Complex.I * (coefT α : ℂ)) * w a)
      (fun b => convS w b) := by
  funext i
  cases i with
  | inl a =>
      change convK Tker (fun m => iotaTan α w (Sum.inr m)) a
          = (Complex.I * (coefT α : ℂ)) * w a
      have hlam : (fun m : ℤ => iotaTan α w (Sum.inr m))
          = (Complex.I * (coefT α : ℂ)) • convS w := by
        funext m; simp [iotaTan_inr]
      rw [hlam, convK_smul, smul_eq_mul]
      congr 1
      exact convK_TS_eq hw a
  | inr b =>
      change convS (fun n => iotaTan α w (Sum.inl n)) b = convS w b
      have hlam : (fun n : ℤ => iotaTan α w (Sum.inl n)) = w := by funext n; rfl
      rw [hlam]

/-- **The eigenvalue condition** `M_α(ι_tan w) = P(ι_tan w)`, i.e.
`ι_tan w ∈ ker(R_α + I)` ([ksindexi] `iop-qop_equiv` item 1, `+` case).
Elementary trig: `sin²+cos²=1` and `1+cos απ ≠ 0`. -/
lemma mulA_iotaTan (α : ℝ) (hα : (1 : ℝ) + Real.cos (α * Real.pi) ≠ 0)
    {w : ℤ → ℂ} (hw : Summable fun n : ℤ => ‖w n‖ ^ 2) :
    mulA α (iotaTan α w) = parity (iotaTan α w) := by
  have R1 : Real.cos (α * Real.pi) + Real.sin (α * Real.pi) * coefT α = 1 := by
    have hpy := Real.sin_sq_add_cos_sq (α * Real.pi)
    rw [coefT]; field_simp; linear_combination hpy
  have R2 : coefT α * (1 + Real.cos (α * Real.pi)) = Real.sin (α * Real.pi) := by
    rw [coefT, div_mul_cancel₀ _ hα]
  have hR1 : (Real.cos (α * Real.pi) : ℂ)
      + (Real.sin (α * Real.pi) : ℂ) * (coefT α : ℂ) = 1 := by exact_mod_cast R1
  have hR2 : (coefT α : ℂ) * (1 + (Real.cos (α * Real.pi) : ℂ))
      = (Real.sin (α * Real.pi) : ℂ) := by exact_mod_cast R2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hsi : ∀ a : ℤ, sgn (iotaTan α w) (Sum.inl a)
      = (Complex.I * (coefT α : ℂ)) * w a :=
    fun a => congrFun (sgn_iotaTan α hw) (Sum.inl a)
  have hsr : ∀ b : ℤ, sgn (iotaTan α w) (Sum.inr b) = convS w b :=
    fun b => congrFun (sgn_iotaTan α hw) (Sum.inr b)
  funext i
  cases i with
  | inl n =>
      simp only [mulA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsi, parity_inl,
        iotaTan_inl]
      linear_combination (w n) * hR1
        - (w n) * (Real.sin (α * Real.pi) : ℂ) * (coefT α : ℂ) * hI
  | inr m =>
      simp only [mulA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsr, parity_inr,
        iotaTan_inr]
      linear_combination (convS w m) * Complex.I * hR2

/-- The DtN energy of an embedded vector is the circle form `Q_{coefT}`:
`Ndiag (ι_tan w) = CircleQ.Qform (coefT α) w`. -/
lemma Ndiag_iotaTan (α : ℝ) (w : ℤ → ℂ) : Ndiag (iotaTan α w) = Qform (coefT α) w := by
  have h1 : (∑' n : ℤ, sigP n * ‖iotaTan α w (Sum.inl n)‖ ^ 2)
      = ∑' n : ℤ, sigP n * ‖w n‖ ^ 2 :=
    tsum_congr fun n => by rw [iotaTan_inl]
  have h2 : (∑' m : ℤ, sigM m * ‖iotaTan α w (Sum.inr m)‖ ^ 2)
      = coefT α ^ 2 * ∑' m : ℤ, sigM m * ‖convS w m‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr fun m => by
      rw [iotaTan_inr]
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
        mul_pow, sq_abs]
      ring
  rw [Ndiag, Qform, h1, h2]

/-- **`𝓝_α(ι_tan w, ι_tan w) = 2·Q_{coefT}(w)`** ([ksindexi] `iop-qop_equiv`
item 2): on `ker(R_α + I)`, `M_α u = P u`, so `𝓝_α` doubles the DtN energy,
which is the circle form at `s = coefT α = tan(απ/2)`. -/
lemma NQform_iotaTan (α : ℝ) (hα : (1 : ℝ) + Real.cos (α * Real.pi) ≠ 0)
    {w : ℤ → ℂ} (hw : Summable fun n : ℤ => ‖w n‖ ^ 2) :
    NQform α (iotaTan α w) = 2 * Qform (coefT α) w := by
  rw [NQform, mulA_iotaTan α hα hw, Ndiag_parity]
  simp only [Ndiag_iotaTan]
  ring

/-- **`ι_tan` lands in the domain**: `w ∈ H^{1/2}_{(+,2;3)}` (`CircleQ.MemDom`)
lifts to `ι_tan w ∈ H^{1/2}_{ς,(2;3)}` (`Domς`).  Both halves inherit the
`H^{1/2}` weight from `w` and `convS w`; the coefficient `i·coefT` is a fixed
scalar, and `ς(ι_tan w) = (i·coefT·w, convS w)` is a mere reshuffle of the same
two pieces. -/
lemma iotaTan_mem_Domς (α : ℝ) {w : ℤ → ℂ} (hw : MemDom w) :
    iotaTan α w ∈ Domς := by
  have hl2 : Summable (fun n : ℤ => ‖w n‖ ^ 2) := CircleQ.summable_normSq hw.1
  have hsi : ∀ a : ℤ, sgn (iotaTan α w) (Sum.inl a)
      = (Complex.I * (coefT α : ℂ)) * w a :=
    fun a => congrFun (sgn_iotaTan α hl2) (Sum.inl a)
  have hsr : ∀ b : ℤ, sgn (iotaTan α w) (Sum.inr b) = convS w b :=
    fun b => congrFun (sgn_iotaTan α hl2) (Sum.inr b)
  rw [mem_Domς]
  refine ⟨⟨hw.1.congr fun n => ?_, (hw.2.mul_left (coefT α ^ 2)).congr fun m => ?_⟩,
    (hw.1.mul_left (coefT α ^ 2)).congr fun n => ?_, hw.2.congr fun m => ?_⟩
  · rw [iotaTan_inl]
  · rw [iotaTan_inr]
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
      mul_pow, sq_abs]; ring
  · rw [hsi]
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
      mul_pow, sq_abs]; ring
  · rw [hsr]

/-- `restrictL` undoes `ι_tan`: `restrictL (ι_tan w) = w`. -/
@[simp] lemma restrictL_iotaTan (α : ℝ) (w : ℤ → ℂ) : restrictL (iotaTan α w) = w := rfl

/-- **Surjectivity onto the eigenspace** ([ksindexi] `iop-qop_equiv` item 1, `+`):
every `u` with `M_α u = P u` is the `ι_tan`-image of its own `inl`-restriction.
With the domain-membership lemmas and `1+cos(απ) ≠ 0`, this identifies
`MemDom` with the eigenvalue `−1` space inside `Domς`.  The `inr` coefficients are forced by the `inr`-component of the
eigenvalue equation: `(1+cos απ)·u(inr) = i·sin απ·convS(u|inl)`. -/
lemma iotaTan_reconstruct (α : ℝ) (hα : (1 : ℝ) + Real.cos (α * Real.pi) ≠ 0)
    {u : Idx → ℂ} (heig : mulA α u = parity u) :
    u = iotaTan α (restrictL u) := by
  have R2 : coefT α * (1 + Real.cos (α * Real.pi)) = Real.sin (α * Real.pi) := by
    rw [coefT, div_mul_cancel₀ _ hα]
  have hR2 : (coefT α : ℂ) * (1 + (Real.cos (α * Real.pi) : ℂ))
      = (Real.sin (α * Real.pi) : ℂ) := by exact_mod_cast R2
  have h1cos : (1 : ℂ) + (Real.cos (α * Real.pi) : ℂ) ≠ 0 := by
    have h : ((1 + Real.cos (α * Real.pi) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
    simpa using h
  funext i
  cases i with
  | inl n => rfl
  | inr m =>
      have heig_m := congrFun heig (Sum.inr m)
      simp only [mulA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sgn_inr, parity_inr] at heig_m
      change u (Sum.inr m)
        = (Complex.I * (coefT α : ℂ)) * convS (fun n : ℤ => u (Sum.inl n)) m
      apply mul_left_cancel₀ h1cos
      linear_combination heig_m
        - Complex.I * convS (fun n : ℤ => u (Sum.inl n)) m * hR2

/-! ### The `cot` eigenspace `ker(R_α − I)`

The mirror of the `tan` branch.  A `+`-half sequence `w` lifts to

    ι_cot w = (inl = w,  inr = i·(−sin απ/(1−cos απ))·convS w) ∈ ker(R_α − I),

on which `M_α (ι_cot w) = −P (ι_cot w)`, so `𝓝_α(ι_cot w) = 2·Ndiag = 2·Q_s(w)`
with `s = coefC α = −sin απ/(1−cos απ) = −cot(απ/2)`; only `s²`
enters `Qform`.  Elementary trig again: `sin²+cos²=1` and `1−cos απ ≠ 0`. -/

/-- The `cot`-embedding coefficient `−sin(απ)/(1−cos(απ)) = −cot(απ/2)`. -/
def coefC (α : ℝ) : ℝ := (-Real.sin (α * Real.pi)) / (1 - Real.cos (α * Real.pi))

/-- The coefficient map `w ↦ (inl = w, inr = i·coefC·convS w)`.
For `w ∈ MemDom` and `1−cos(απ) ≠ 0`, it parametrizes the eigenvalue `+1`
space of `R_α` inside `Domς`. -/
def iotaCot (α : ℝ) (w : ℤ → ℂ) : Idx → ℂ := fun i => i.elim
  (fun n => w n)
  (fun m => (Complex.I * (coefC α : ℂ)) * convS w m)

@[simp] lemma iotaCot_inl (α : ℝ) (w : ℤ → ℂ) (n : ℤ) :
    iotaCot α w (.inl n) = w n := rfl

@[simp] lemma iotaCot_inr (α : ℝ) (w : ℤ → ℂ) (m : ℤ) :
    iotaCot α w (.inr m) = (Complex.I * (coefC α : ℂ)) * convS w m := rfl

/-- The half-swap `ς` of a `cot`-embedded vector: `ς(ι_cot w) = (inl = i·coefC·w,
inr = convS w)` — same collapse via `T∘S = id`. -/
lemma sgn_iotaCot (α : ℝ) {w : ℤ → ℂ} (hw : Summable fun n : ℤ => ‖w n‖ ^ 2) :
    sgn (iotaCot α w) = fun i => i.elim
      (fun a => (Complex.I * (coefC α : ℂ)) * w a)
      (fun b => convS w b) := by
  funext i
  cases i with
  | inl a =>
      change convK Tker (fun m => iotaCot α w (Sum.inr m)) a
          = (Complex.I * (coefC α : ℂ)) * w a
      have hlam : (fun m : ℤ => iotaCot α w (Sum.inr m))
          = (Complex.I * (coefC α : ℂ)) • convS w := by
        funext m; simp [iotaCot_inr]
      rw [hlam, convK_smul, smul_eq_mul]
      congr 1
      exact convK_TS_eq hw a
  | inr b =>
      change convS (fun n => iotaCot α w (Sum.inl n)) b = convS w b
      have hlam : (fun n : ℤ => iotaCot α w (Sum.inl n)) = w := by funext n; rfl
      rw [hlam]

/-- **The eigenvalue condition** `M_α(ι_cot w) = −P(ι_cot w)`, i.e.
`ι_cot w ∈ ker(R_α − I)` ([ksindexi] `iop-qop_equiv` item 1, `−` case).
Elementary trig: `sin²+cos²=1` and `1−cos απ ≠ 0`. -/
lemma mulA_iotaCot (α : ℝ) (hα : (1 : ℝ) - Real.cos (α * Real.pi) ≠ 0)
    {w : ℤ → ℂ} (hw : Summable fun n : ℤ => ‖w n‖ ^ 2) :
    mulA α (iotaCot α w) = -parity (iotaCot α w) := by
  have C1 : Real.cos (α * Real.pi) + Real.sin (α * Real.pi) * coefC α = -1 := by
    have hpy := Real.sin_sq_add_cos_sq (α * Real.pi)
    rw [coefC]; field_simp; linear_combination -hpy
  have C2 : coefC α * (1 - Real.cos (α * Real.pi)) = -Real.sin (α * Real.pi) := by
    rw [coefC, div_mul_cancel₀ _ hα]
  have hC1 : (Real.cos (α * Real.pi) : ℂ)
      + (Real.sin (α * Real.pi) : ℂ) * (coefC α : ℂ) = -1 := by exact_mod_cast C1
  have hC2 : (coefC α : ℂ) * (1 - (Real.cos (α * Real.pi) : ℂ))
      = -(Real.sin (α * Real.pi) : ℂ) := by exact_mod_cast C2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hsi : ∀ a : ℤ, sgn (iotaCot α w) (Sum.inl a)
      = (Complex.I * (coefC α : ℂ)) * w a :=
    fun a => congrFun (sgn_iotaCot α hw) (Sum.inl a)
  have hsr : ∀ b : ℤ, sgn (iotaCot α w) (Sum.inr b) = convS w b :=
    fun b => congrFun (sgn_iotaCot α hw) (Sum.inr b)
  funext i
  cases i with
  | inl n =>
      simp only [mulA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsi, Pi.neg_apply,
        parity_inl, iotaCot_inl]
      linear_combination (w n) * hC1
        - (w n) * (Real.sin (α * Real.pi) : ℂ) * (coefC α : ℂ) * hI
  | inr m =>
      simp only [mulA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsr, Pi.neg_apply,
        parity_inr, iotaCot_inr, neg_neg]
      linear_combination -(convS w m) * Complex.I * hC2

/-- The DtN energy of a `cot`-embedded vector is the circle form `Q_{coefC}`:
`Ndiag (ι_cot w) = CircleQ.Qform (coefC α) w`. -/
lemma Ndiag_iotaCot (α : ℝ) (w : ℤ → ℂ) : Ndiag (iotaCot α w) = Qform (coefC α) w := by
  have h1 : (∑' n : ℤ, sigP n * ‖iotaCot α w (Sum.inl n)‖ ^ 2)
      = ∑' n : ℤ, sigP n * ‖w n‖ ^ 2 :=
    tsum_congr fun n => by rw [iotaCot_inl]
  have h2 : (∑' m : ℤ, sigM m * ‖iotaCot α w (Sum.inr m)‖ ^ 2)
      = coefC α ^ 2 * ∑' m : ℤ, sigM m * ‖convS w m‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr fun m => by
      rw [iotaCot_inr]
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
        mul_pow, sq_abs]
      ring
  rw [Ndiag, Qform, h1, h2]

/-- **`𝓝_α(ι_cot w, ι_cot w) = 2·Q_{coefC}(w)`** ([ksindexi] `iop-qop_equiv`
item 2, `−` case): on `ker(R_α − I)`, `M_α u = −P u`, so `𝓝_α` doubles the DtN
energy, which is the circle form at `s = coefC α`. On `0 < α < 1`,
this coefficient is `−cot(απ/2)`; only its square enters the form. -/
lemma NQform_iotaCot (α : ℝ) (hα : (1 : ℝ) - Real.cos (α * Real.pi) ≠ 0)
    {w : ℤ → ℂ} (hw : Summable fun n : ℤ => ‖w n‖ ^ 2) :
    NQform α (iotaCot α w) = 2 * Qform (coefC α) w := by
  rw [NQform, mulA_iotaCot α hα hw, Ndiag_neg, Ndiag_parity]
  simp only [Ndiag_iotaCot]
  ring

/-- **`ι_cot` lands in the domain**: mirror of `iotaTan_mem_Domς` — `w ∈ MemDom`
lifts to `ι_cot w ∈ Domς`. -/
lemma iotaCot_mem_Domς (α : ℝ) {w : ℤ → ℂ} (hw : MemDom w) :
    iotaCot α w ∈ Domς := by
  have hl2 : Summable (fun n : ℤ => ‖w n‖ ^ 2) := CircleQ.summable_normSq hw.1
  have hsi : ∀ a : ℤ, sgn (iotaCot α w) (Sum.inl a)
      = (Complex.I * (coefC α : ℂ)) * w a :=
    fun a => congrFun (sgn_iotaCot α hl2) (Sum.inl a)
  have hsr : ∀ b : ℤ, sgn (iotaCot α w) (Sum.inr b) = convS w b :=
    fun b => congrFun (sgn_iotaCot α hl2) (Sum.inr b)
  rw [mem_Domς]
  refine ⟨⟨hw.1.congr fun n => ?_, (hw.2.mul_left (coefC α ^ 2)).congr fun m => ?_⟩,
    (hw.1.mul_left (coefC α ^ 2)).congr fun n => ?_, hw.2.congr fun m => ?_⟩
  · rw [iotaCot_inl]
  · rw [iotaCot_inr]
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
      mul_pow, sq_abs]; ring
  · rw [hsi]
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
      mul_pow, sq_abs]; ring
  · rw [hsr]

/-- `restrictL` undoes `ι_cot`: `restrictL (ι_cot w) = w`. -/
@[simp] lemma restrictL_iotaCot (α : ℝ) (w : ℤ → ℂ) : restrictL (iotaCot α w) = w := rfl

/-- **Surjectivity onto the eigenspace** ([ksindexi] `iop-qop_equiv` item 1, `−`):
every `u` with `M_α u = −P u` is the `ι_cot`-image of its own `inl`-restriction.
Mirror of `iotaTan_reconstruct`; the `inr` coefficients are forced by
`(1−cos απ)·u(inr) = −i·sin απ·convS(u|inl)`. -/
lemma iotaCot_reconstruct (α : ℝ) (hα : (1 : ℝ) - Real.cos (α * Real.pi) ≠ 0)
    {u : Idx → ℂ} (heig : mulA α u = -parity u) :
    u = iotaCot α (restrictL u) := by
  have C2 : coefC α * (1 - Real.cos (α * Real.pi)) = -Real.sin (α * Real.pi) := by
    rw [coefC, div_mul_cancel₀ _ hα]
  have hC2 : (coefC α : ℂ) * (1 - (Real.cos (α * Real.pi) : ℂ))
      = -(Real.sin (α * Real.pi) : ℂ) := by exact_mod_cast C2
  have h1mcos : (1 : ℂ) - (Real.cos (α * Real.pi) : ℂ) ≠ 0 := by
    have h : ((1 - Real.cos (α * Real.pi) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
    simpa using h
  funext i
  cases i with
  | inl n => rfl
  | inr m =>
      have heig_m := congrFun heig (Sum.inr m)
      simp only [mulA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sgn_inr, Pi.neg_apply,
        parity_inr, neg_neg] at heig_m
      change u (Sum.inr m)
        = (Complex.I * (coefC α : ℂ)) * convS (fun n : ℤ => u (Sum.inl n)) m
      apply mul_left_cancel₀ h1mcos
      linear_combination -heig_m
        - Complex.I * convS (fun n : ℤ => u (Sum.inl n)) m * hC2

end KsIndex.SectorReduce
