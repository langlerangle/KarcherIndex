module

/-
KsIndexLean — Sector: the `(2;3)` two-parity sector coefficient model.

Coefficient spaces and operators for the `𝓝_{3,α}` reduction (`iop-qop_equiv`).
The full sector `H^{1/2}_{ς,(2;3)}(S¹)` has Fourier support on
`(1+6ℤ) ∪ (4+6ℤ)` ([ksindexi] ll. 4236–4266) — the two half-lattices the
circle core already carries.  So the sector is modeled on `ℤ ⊕ ℤ`:

    u (Sum.inl n) = û(6n+1)   (the `+` half, `H_{(+,2;3)}`)
    u (Sum.inr m) = û(6m+4)   (the `−` half, `H_{(-,2;3)}`).

This is exactly the abstract `ι → ℂ` of `FormIndex.lean` at `ι = ℤ ⊕ ℤ`, so
the generic Morse index/nullity constructions apply to the α-shifted
form `𝓝_{3,α}` defined in `SectorForm`.

This file contains the model, the parity operator `P` (a pure sign flip on the
`−` half, [ksindexi] l. 4281), the `N₃` diagonal energy `⟨N₃u,u⟩` (the existing
`sigP`/`sigM` symbols read through the two halves), the half-swap `ς` (`sgn`:
`+` half ↦ `−` half via `convS`, `−` half ↦ `+` half via `convK Tker`; `ς² = 1`
is `convK_TS_eq`/`convK_ST_eq`), the ς-invariant domain `Domς` (the paper's
`H^{1/2}_{ς,(2;3)}`, l. 3990), the multipliers `M_α`, `M_α†` (l. 3968), and the
involution `R_α = −M_α†P` (l. 4444) with the algebra `M_α†M_α = M_αM_α† = I`,
`PM_α† = M_αP`, `R_α² = I` and the eigenvector dictionary `M_α u = ±P u ⟺
R_α u = ∓u`.  The form `𝓝_{3,α}` is built on top in `SectorForm`.
-/
public import KsIndexLean.SIsometry

@[expose] public section


noncomputable section

namespace KsIndex.Sector

open KsIndex.CircleQ KsIndex.SIsometry

/-- The `(2;3)`-sector index type: `inl` carries the `+` half (`ℓ = 6n+1`),
`inr` the `−` half (`ℓ = 6m+4`). -/
abbrev Idx : Type := ℤ ⊕ ℤ

/-! ### The parity operator `P` -/

/-- The parity Fourier multiplier `P` ([ksindexi] l. 4281): `+1` on the `+`
half, `−1` on the `−` half. -/
def parity (u : Idx → ℂ) : Idx → ℂ :=
  fun i => i.elim (fun n => u (.inl n)) (fun m => -(u (.inr m)))

@[simp] lemma parity_inl (u : Idx → ℂ) (n : ℤ) : parity u (.inl n) = u (.inl n) := rfl

@[simp] lemma parity_inr (u : Idx → ℂ) (m : ℤ) : parity u (.inr m) = -(u (.inr m)) := rfl

/-- `P` is an involution: `P² = I`. -/
lemma parity_involutive (u : Idx → ℂ) : parity (parity u) = u := by
  funext i
  cases i with
  | inl n => simp
  | inr m => simp

/-- `P` is complex-linear in the coefficient sequence. -/
lemma parity_add (u v : Idx → ℂ) : parity (u + v) = parity u + parity v := by
  funext i
  cases i with
  | inl n => simp
  | inr m => simp only [parity_inr, Pi.add_apply]; ring

lemma parity_smul (c : ℂ) (u : Idx → ℂ) : parity (c • u) = c • parity u := by
  funext i
  cases i with
  | inl n => simp
  | inr m => simp [mul_neg]

/-! ### The DtN diagonal energy `⟨N₃ u, u⟩` -/

/-- The Dirichlet-to-Neumann diagonal energy on the sector: `σ₃` read through
the two half-lattices via the existing `sigP`/`sigM` symbols. -/
def Ndiag (u : Idx → ℂ) : ℝ :=
  (∑' n : ℤ, sigP n * ‖u (.inl n)‖ ^ 2) + (∑' m : ℤ, sigM m * ‖u (.inr m)‖ ^ 2)

/-- Sum of squared sector coefficients, corresponding to normalized circle
`L²` mass; arclength mass has the additional factor `2π`. -/
def normSqS (u : Idx → ℂ) : ℝ :=
  (∑' n : ℤ, ‖u (.inl n)‖ ^ 2) + (∑' m : ℤ, ‖u (.inr m)‖ ^ 2)

/-! ### Sector membership -/

/-- Membership in `H^{1/2}_{(2;3)}(S¹)` at the coefficient level: both halves
satisfy the homogeneous half-order weight condition. The frequencies exclude
zero, so this gives the same membership as the inhomogeneous condition.
`MemSectorς` additionally requires the sign-multiplied sequence to belong. -/
def MemSector (u : Idx → ℂ) : Prop :=
  Summable (fun n : ℤ => |6 * (n : ℝ) + 1| * ‖u (.inl n)‖ ^ 2)
    ∧ Summable (fun m : ℤ => |6 * (m : ℝ) + 4| * ‖u (.inr m)‖ ^ 2)

/-- The parity operator preserves sector membership (it only flips signs, and
`‖-z‖ = ‖z‖`). -/
lemma memSector_parity {u : Idx → ℂ} (hu : MemSector u) : MemSector (parity u) := by
  refine ⟨hu.1.congr fun n => ?_, hu.2.congr fun m => ?_⟩
  · simp
  · simp

/-! ### The half-swap `ς` (`sgn`)

`ς` ([ksindexi] l. 4290) swaps the two halves: the `+` half maps to the `−`
half via `S = convS`, and the `−` half maps back via the adjoint
`T = convK Tker`. By `chat_refl`, `T` represents multiplication by the sign
function on the `−` half. Thus `ς` is a unitary multiplication operator on
circle functions, represented here by convolution of Fourier coefficients. Its
defining property `ς² = 1` is the pair `T∘S = id` / `S∘T = id`
(`convK_TS_eq` / `convK_ST_eq`). -/

/-- The `L²` (square-summable) condition on the sector: each half is `ℓ²`. -/
def SectorL2 (u : Idx → ℂ) : Prop :=
  (Summable fun n : ℤ => ‖u (Sum.inl n)‖ ^ 2)
    ∧ (Summable fun m : ℤ => ‖u (Sum.inr m)‖ ^ 2)

/-- The half-swap `ς`: `+` half `↦ −` half via `S`, `−` half `↦ +` half via `T`. -/
def sgn (u : Idx → ℂ) : Idx → ℂ := fun i => i.elim
  (fun a => convK Tker (fun m => u (Sum.inr m)) a)
  (fun b => convS (fun n => u (Sum.inl n)) b)

@[simp] lemma sgn_inl (u : Idx → ℂ) (a : ℤ) :
    sgn u (.inl a) = convK Tker (fun m => u (Sum.inr m)) a := rfl

@[simp] lemma sgn_inr (u : Idx → ℂ) (b : ℤ) :
    sgn u (.inr b) = convS (fun n => u (Sum.inl n)) b := rfl

/-- `ς` is homogeneous (unconditional). -/
lemma sgn_smul (c : ℂ) (u : Idx → ℂ) : sgn (c • u) = c • sgn u := by
  funext i
  cases i with
  | inl a =>
      have hlam : (fun m : ℤ => (c • u) (Sum.inr m)) = c • (fun m : ℤ => u (Sum.inr m)) := by
        funext m; rfl
      change convK Tker (fun m => (c • u) (Sum.inr m)) a
          = c • convK Tker (fun m => u (Sum.inr m)) a
      rw [hlam, convK_smul]
  | inr b =>
      have hlam : (fun n : ℤ => (c • u) (Sum.inl n)) = c • (fun n : ℤ => u (Sum.inl n)) := by
        funext n; rfl
      change convS (fun n => (c • u) (Sum.inl n)) b = c • convS (fun n => u (Sum.inl n)) b
      rw [hlam, ← convK_Sker, convK_smul, convK_Sker]

/-- `ς` is additive on `ℓ²` sector inputs. -/
lemma sgn_add {u v : Idx → ℂ} (hu : SectorL2 u) (hv : SectorL2 v) :
    sgn (u + v) = sgn u + sgn v := by
  funext i
  cases i with
  | inl a =>
      have hlam : (fun m : ℤ => (u + v) (Sum.inr m))
          = (fun m : ℤ => u (Sum.inr m)) + (fun m : ℤ => v (Sum.inr m)) := by
        funext m; rfl
      change convK Tker (fun m => (u + v) (Sum.inr m)) a
          = convK Tker (fun m => u (Sum.inr m)) a
            + convK Tker (fun m => v (Sum.inr m)) a
      rw [hlam, convK_add Tker_row hu.2 hv.2]
  | inr b =>
      have hlam : (fun n : ℤ => (u + v) (Sum.inl n))
          = (fun n : ℤ => u (Sum.inl n)) + (fun n : ℤ => v (Sum.inl n)) := by
        funext n; rfl
      change convS (fun n => (u + v) (Sum.inl n)) b
          = convS (fun n => u (Sum.inl n)) b + convS (fun n => v (Sum.inl n)) b
      rw [hlam, ← convK_Sker, convK_add Sker_row hu.1 hv.1, convK_Sker, convK_Sker]

/-- `ς` preserves the sector `ℓ²` condition (it is unitary). -/
lemma sectorL2_sgn {u : Idx → ℂ} (hu : SectorL2 u) : SectorL2 (sgn u) :=
  ⟨(summable_convK_sq Tker_mul Tker_orth Tker_row Tker_row1 hu.2).congr
      fun a => by rw [sgn_inl],
    (summable_convS_sq hu.1).congr fun b => by rw [sgn_inr]⟩

/-- `ς² = 1` on square-summable sector sequences. On the `+` half this uses
`T∘S = id` (`convK_TS_eq`); on the `−` half it uses `S∘T = id` (`convK_ST_eq`). -/
lemma sgn_involutive {u : Idx → ℂ} (hu : SectorL2 u) : sgn (sgn u) = u := by
  funext i
  cases i with
  | inl a =>
      have h : sgn (sgn u) (Sum.inl a)
          = convK Tker (convK Sker (fun n => u (Sum.inl n))) a := by
        simp only [sgn_inl, sgn_inr, ← convK_Sker]
      rw [h, convK_TS_eq hu.1 a]
  | inr b =>
      have h : sgn (sgn u) (Sum.inr b)
          = convK Sker (convK Tker (fun m => u (Sum.inr m))) b := by
        simp only [sgn_inr, sgn_inl, ← convK_Sker]
      rw [h, convK_ST_eq hu.2 b]

/-! ### Commutation with the parity -/

/-- **`Pς = −ςP`** ([ksindexi] l. 4294): `ς` anti-commutes with the parity `P`.
(Unconditional — pure sign bookkeeping through the two halves.) -/
lemma parity_sgn (u : Idx → ℂ) : parity (sgn u) = - sgn (parity u) := by
  funext i
  cases i with
  | inl a =>
      have hlam : (fun m : ℤ => parity u (Sum.inr m))
          = (-1 : ℂ) • (fun m : ℤ => u (Sum.inr m)) := by
        funext m; simp only [parity_inr, Pi.smul_apply, neg_one_smul]
      simp only [parity_inl, sgn_inl, Pi.neg_apply]
      rw [hlam, convK_smul, neg_one_smul, neg_neg]
  | inr b =>
      have hlam : (fun n : ℤ => parity u (Sum.inl n)) = (fun n : ℤ => u (Sum.inl n)) := by
        funext n; rw [parity_inl]
      simp only [parity_inr, sgn_inr, Pi.neg_apply]
      rw [hlam]

/-- The DtN diagonal energy is parity-invariant — the form-level content of
`[P, N₃] = 0` ([ksindexi] l. 4297), expressed here for the diagonal energy. -/
lemma Ndiag_parity (u : Idx → ℂ) : Ndiag (parity u) = Ndiag u := by
  simp only [Ndiag, parity_inl, parity_inr, norm_neg]

/-- The DtN diagonal energy is negation-invariant (norms ignore the sign). -/
lemma Ndiag_neg (u : Idx → ℂ) : Ndiag (-u) = Ndiag u := by
  simp only [Ndiag, Pi.neg_apply, norm_neg]

/-- The sector `L²` energy is parity-invariant (`P` is unitary). -/
lemma normSqS_parity (u : Idx → ℂ) : normSqS (parity u) = normSqS u := by
  simp only [normSqS, parity_inl, parity_inr, norm_neg]

/-! ### The ς-invariant domain `H^{1/2}_{ς,(2;3)}`

Closure under linear operations of the sector `H^{1/2}` condition, then the ς-invariant
domain `MemSectorς u := MemSector u ∧ MemSector (ς u)` — verbatim the paper's
`H^{1/2}_ς(S¹) = {u ∈ H^{1/2} : ς u ∈ H^{1/2}}` ([ksindexi] l. 3990), read
through the `(2;3)` sector model.  It is the space on which
`M_α u = (cos απ)u − i(sin απ)·ς u` lands back in `H^{1/2}` for every `α`
([ksindexi] l. 4005), and it is ς-invariant by `ς² = 1`. -/

/-- `MemSector` contains `0`. -/
lemma memSector_zero : MemSector (0 : Idx → ℂ) := by
  constructor
  · exact summable_zero.congr fun n => by simp
  · exact summable_zero.congr fun m => by simp

/-- `MemSector` is closed under scalar multiplication. -/
lemma memSector_smul (c : ℂ) {u : Idx → ℂ} (hu : MemSector u) : MemSector (c • u) := by
  constructor
  · refine (hu.1.mul_left (‖c‖ ^ 2)).congr fun n => ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]; ring
  · refine (hu.2.mul_left (‖c‖ ^ 2)).congr fun m => ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]; ring

/-- `MemSector` is closed under addition. -/
lemma memSector_add {u v : Idx → ℂ} (hu : MemSector u) (hv : MemSector v) :
    MemSector (u + v) := by
  constructor
  · refine ((hu.1.add hv.1).mul_left 2).of_nonneg_of_le (fun n => by positivity) fun n => ?_
    have h1 : ‖(u + v) (Sum.inl n)‖ ≤ ‖u (Sum.inl n)‖ + ‖v (Sum.inl n)‖ := by
      simp only [Pi.add_apply]; exact norm_add_le _ _
    have hX : ‖(u + v) (Sum.inl n)‖ ^ 2
        ≤ 2 * ‖u (Sum.inl n)‖ ^ 2 + 2 * ‖v (Sum.inl n)‖ ^ 2 := by
      nlinarith [norm_nonneg ((u + v) (Sum.inl n)), norm_nonneg (u (Sum.inl n)),
        norm_nonneg (v (Sum.inl n)), sq_nonneg (‖u (Sum.inl n)‖ - ‖v (Sum.inl n)‖)]
    calc |6 * (n : ℝ) + 1| * ‖(u + v) (Sum.inl n)‖ ^ 2
        ≤ |6 * (n : ℝ) + 1| * (2 * ‖u (Sum.inl n)‖ ^ 2 + 2 * ‖v (Sum.inl n)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hX (abs_nonneg _)
      _ = 2 * (|6 * (n : ℝ) + 1| * ‖u (Sum.inl n)‖ ^ 2
            + |6 * (n : ℝ) + 1| * ‖v (Sum.inl n)‖ ^ 2) := by ring
  · refine ((hu.2.add hv.2).mul_left 2).of_nonneg_of_le (fun m => by positivity) fun m => ?_
    have h1 : ‖(u + v) (Sum.inr m)‖ ≤ ‖u (Sum.inr m)‖ + ‖v (Sum.inr m)‖ := by
      simp only [Pi.add_apply]; exact norm_add_le _ _
    have hX : ‖(u + v) (Sum.inr m)‖ ^ 2
        ≤ 2 * ‖u (Sum.inr m)‖ ^ 2 + 2 * ‖v (Sum.inr m)‖ ^ 2 := by
      nlinarith [norm_nonneg ((u + v) (Sum.inr m)), norm_nonneg (u (Sum.inr m)),
        norm_nonneg (v (Sum.inr m)), sq_nonneg (‖u (Sum.inr m)‖ - ‖v (Sum.inr m)‖)]
    calc |6 * (m : ℝ) + 4| * ‖(u + v) (Sum.inr m)‖ ^ 2
        ≤ |6 * (m : ℝ) + 4| * (2 * ‖u (Sum.inr m)‖ ^ 2 + 2 * ‖v (Sum.inr m)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hX (abs_nonneg _)
      _ = 2 * (|6 * (m : ℝ) + 4| * ‖u (Sum.inr m)‖ ^ 2
            + |6 * (m : ℝ) + 4| * ‖v (Sum.inr m)‖ ^ 2) := by ring

/-- The sector `H^{1/2}` condition implies the `L²` condition (weights `≥ 1`). -/
lemma memSector_sectorL2 {u : Idx → ℂ} (hu : MemSector u) : SectorL2 u := by
  refine ⟨hu.1.of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_,
    hu.2.of_nonneg_of_le (fun m => sq_nonneg _) fun m => ?_⟩
  · have hw : (1 : ℝ) ≤ |6 * (n : ℝ) + 1| := by
      have h6 : (6 * (n : ℝ) + 1) = ((6 * n + 1 : ℤ) : ℝ) := by push_cast; ring
      rw [h6, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs (by omega)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ |6 * (n : ℝ) + 1| - 1)
      (sq_nonneg ‖u (Sum.inl n)‖)]
  · have hw : (1 : ℝ) ≤ |6 * (m : ℝ) + 4| := by
      have h6 : (6 * (m : ℝ) + 4) = ((6 * m + 4 : ℤ) : ℝ) := by push_cast; ring
      rw [h6, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs (by omega)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ |6 * (m : ℝ) + 4| - 1)
      (sq_nonneg ‖u (Sum.inr m)‖)]

/-- `ς 0 = 0`. -/
lemma sgn_zero : sgn (0 : Idx → ℂ) = 0 := by
  simpa using sgn_smul (0 : ℂ) (0 : Idx → ℂ)

/-- **The ς-invariant sector domain** `H^{1/2}_{ς,(2;3)}` ([ksindexi] l. 3990):
both `u` and its half-swap `ς u` satisfy the sector `H^{1/2}` condition.
Bundled (not derived) exactly as `CircleQ.MemDom` bundles `convS u`, since ς is
multiplication by the `±1` sign pattern and does not preserve `H^{1/2}`. -/
def MemSectorς (u : Idx → ℂ) : Prop := MemSector u ∧ MemSector (sgn u)

lemma memSectorς_zero : MemSectorς (0 : Idx → ℂ) :=
  ⟨memSector_zero, by rw [sgn_zero]; exact memSector_zero⟩

lemma memSectorς_smul (c : ℂ) {u : Idx → ℂ} (hu : MemSectorς u) : MemSectorς (c • u) :=
  ⟨memSector_smul c hu.1, by rw [sgn_smul]; exact memSector_smul c hu.2⟩

lemma memSectorς_add {u v : Idx → ℂ} (hu : MemSectorς u) (hv : MemSectorς v) :
    MemSectorς (u + v) :=
  ⟨memSector_add hu.1 hv.1, by
    rw [sgn_add (memSector_sectorL2 hu.1) (memSector_sectorL2 hv.1)]
    exact memSector_add hu.2 hv.2⟩

/-- The domain `H^{1/2}_{ς,(2;3)}(S¹)` (coefficient model) as a complex
subspace of the sector sequence space. -/
def Domς : Submodule ℂ (Idx → ℂ) where
  carrier := {u | MemSectorς u}
  zero_mem' := memSectorς_zero
  add_mem' := fun hu hv => memSectorς_add hu hv
  smul_mem' := fun c _ hu => memSectorς_smul c hu

@[simp] lemma mem_Domς {u : Idx → ℂ} : u ∈ Domς ↔ MemSectorς u := Iff.rfl

/-- **`ς` preserves the domain** (`H^{1/2}_ς` is ς-invariant) — from `ς² = 1`
alone, no `H^{1/2}`-boundedness of ς needed. -/
lemma sgn_mem_domς {u : Idx → ℂ} (hu : MemSectorς u) : MemSectorς (sgn u) :=
  ⟨hu.2, by rw [sgn_involutive (memSector_sectorL2 hu.1)]; exact hu.1⟩

/-- `ς` as a self-map of the domain submodule. -/
lemma sgn_mem_Domς {u : Idx → ℂ} (hu : u ∈ Domς) : sgn u ∈ Domς := sgn_mem_domς hu

/-! ### The α-multiplier `M_α`

`M_α = (cos απ)·I − i(sin απ)·ς = e^{−iςαπ}` ([ksindexi] l. 3968): the rotation
of the boundary condition mixing the identity and the sign multiplier ς.  Only
its definition and structural facts (linearity and domain invariance) are
needed here; `SectorForm` defines the α-shifted form `𝓝_{3,α}` from it. -/

/-- The α-multiplier `M_α u = (cos απ)u − i(sin απ)·ς u` ([ksindexi] l. 3968). -/
def mulA (α : ℝ) (u : Idx → ℂ) : Idx → ℂ :=
  (Real.cos (α * Real.pi) : ℂ) • u
    - (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • sgn u

/-- `M_α` is additive on `ℓ²` sector inputs (via `sgn_add`). -/
lemma mulA_add (α : ℝ) {u v : Idx → ℂ} (hu : SectorL2 u) (hv : SectorL2 v) :
    mulA α (u + v) = mulA α u + mulA α v := by
  simp only [mulA, sgn_add hu hv, smul_add]
  abel

/-- `M_α` is homogeneous (unconditional). -/
lemma mulA_smul (α : ℝ) (c : ℂ) (u : Idx → ℂ) : mulA α (c • u) = c • mulA α u := by
  have h1 : (Real.cos (α * Real.pi) : ℂ) • (c • u)
      = c • (Real.cos (α * Real.pi) : ℂ) • u := smul_comm _ _ _
  have h2 : (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • (c • sgn u)
      = c • (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • sgn u := smul_comm _ _ _
  simp only [mulA, sgn_smul, smul_sub, h1, h2]

/-- **`M_α` maps the domain `H^{1/2}_ς` to itself**, for every `α`
([ksindexi] l. 4005) — immediate from `Domς` being a submodule and ς-invariant. -/
lemma mulA_mem_Domς (α : ℝ) {u : Idx → ℂ} (hu : u ∈ Domς) : mulA α u ∈ Domς := by
  unfold mulA
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hu)
    (Submodule.smul_mem _ _ (sgn_mem_Domς hu))

/-- The `L²` sector condition is preserved under scalar multiplication. -/
lemma sectorL2_smul (c : ℂ) {u : Idx → ℂ} (hu : SectorL2 u) : SectorL2 (c • u) := by
  refine ⟨(hu.1.mul_left (‖c‖ ^ 2)).congr fun n => ?_,
    (hu.2.mul_left (‖c‖ ^ 2)).congr fun m => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

/-! ### The adjoint multiplier `M_α†` and the involution `R_α`

`M_α† = (cos απ)I + i(sin απ)ς` is defined by formula ([ksindexi] l. 3968 with
the opposite sign); we never invoke that it is the genuine `L²`-adjoint — only
the algebra `M_α† M_α = I` and `P M_α† = M_α P`, both consequences of `ς² = 1`
and `Pς = −ςP`. -/

/-- The adjoint multiplier `M_α† u = (cos απ)u + i(sin απ)·ς u`. -/
def mulAdag (α : ℝ) (u : Idx → ℂ) : Idx → ℂ :=
  (Real.cos (α * Real.pi) : ℂ) • u
    + (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • sgn u

lemma mulAdag_add (α : ℝ) {u v : Idx → ℂ} (hu : SectorL2 u) (hv : SectorL2 v) :
    mulAdag α (u + v) = mulAdag α u + mulAdag α v := by
  simp only [mulAdag, sgn_add hu hv, smul_add]; abel

lemma mulAdag_smul (α : ℝ) (c : ℂ) (u : Idx → ℂ) : mulAdag α (c • u) = c • mulAdag α u := by
  have h1 : (Real.cos (α * Real.pi) : ℂ) • (c • u)
      = c • (Real.cos (α * Real.pi) : ℂ) • u := smul_comm _ _ _
  have h2 : (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • (c • sgn u)
      = c • (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • sgn u := smul_comm _ _ _
  simp only [mulAdag, sgn_smul, smul_add, h1, h2]

lemma mulAdag_mem_Domς (α : ℝ) {u : Idx → ℂ} (hu : u ∈ Domς) : mulAdag α u ∈ Domς := by
  unfold mulAdag
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu)
    (Submodule.smul_mem _ _ (sgn_mem_Domς hu))

/-- **`P M_α† = M_α P`** — the vector identity underlying `R_α`'s structure,
from `Pς = −ςP`. -/
lemma parity_mulAdag (α : ℝ) (u : Idx → ℂ) : parity (mulAdag α u) = mulA α (parity u) := by
  simp only [mulAdag, mulA, parity_add, parity_smul, parity_sgn, smul_neg, sub_eq_add_neg]

/-- `P` preserves the `L²` sector condition. -/
lemma sectorL2_parity {u : Idx → ℂ} (hu : SectorL2 u) : SectorL2 (parity u) := by
  refine ⟨hu.1.congr fun n => ?_, hu.2.congr fun m => ?_⟩
  · simp
  · simp

lemma parity_neg (u : Idx → ℂ) : parity (-u) = -parity u := by
  rw [← neg_one_smul ℂ u, parity_smul, neg_one_smul]

lemma mulAdag_neg (α : ℝ) (u : Idx → ℂ) : mulAdag α (-u) = -mulAdag α u := by
  rw [← neg_one_smul ℂ u, mulAdag_smul, neg_one_smul]

/-- `P` preserves the domain `H^{1/2}_ς`. -/
lemma parity_mem_Domς {u : Idx → ℂ} (hu : u ∈ Domς) : parity u ∈ Domς := by
  refine ⟨memSector_parity hu.1, ?_⟩
  have hsp : sgn (parity u) = (-1 : ℂ) • parity (sgn u) := by
    rw [neg_smul, one_smul, parity_sgn u, neg_neg]
  rw [hsp]
  exact memSector_smul (-1) (memSector_parity hu.2)

/-- **`M_α† M_α = I`** — from `ς² = 1` and `cos² + sin² = 1`. -/
lemma mulAdag_mulA (α : ℝ) {u : Idx → ℂ} (hu : SectorL2 u) : mulAdag α (mulA α u) = u := by
  have hς : SectorL2 (sgn u) := sectorL2_sgn hu
  have hs : sgn (mulA α u)
      = (Real.cos (α * Real.pi) : ℂ) • sgn u
        - (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • u := by
    have e1 : mulA α u
        = (Real.cos (α * Real.pi) : ℂ) • u
          + (-(Complex.I * (Real.sin (α * Real.pi) : ℂ))) • sgn u := by
      rw [mulA, sub_eq_add_neg, neg_smul]
    rw [e1, sgn_add (sectorL2_smul _ hu) (sectorL2_smul _ hς), sgn_smul, sgn_smul,
      sgn_involutive hu, neg_smul, ← sub_eq_add_neg]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  simp only [mulAdag]
  rw [hs]
  simp only [mulA]
  match_scalars
  all_goals try ring
  all_goals rw [hI]
  all_goals linear_combination Complex.sin_sq_add_cos_sq ((α : ℂ) * (Real.pi : ℂ))

/-! ### The involution `R_α` -/

/-- The operator `R_α = −M_α† P` ([ksindexi] l. 4444), on the sector. -/
def rop (α : ℝ) (u : Idx → ℂ) : Idx → ℂ := -(mulAdag α (parity u))

lemma rop_mem_Domς (α : ℝ) {u : Idx → ℂ} (hu : u ∈ Domς) : rop α u ∈ Domς := by
  unfold rop
  exact Submodule.neg_mem _ (mulAdag_mem_Domς α (parity_mem_Domς hu))

lemma rop_add (α : ℝ) {u v : Idx → ℂ} (hu : SectorL2 u) (hv : SectorL2 v) :
    rop α (u + v) = rop α u + rop α v := by
  unfold rop
  rw [parity_add, mulAdag_add α (sectorL2_parity hu) (sectorL2_parity hv), neg_add]

lemma rop_smul (α : ℝ) (c : ℂ) (u : Idx → ℂ) : rop α (c • u) = c • rop α u := by
  unfold rop
  rw [parity_smul, mulAdag_smul, smul_neg]

lemma rop_sub (α : ℝ) {u v : Idx → ℂ} (hu : SectorL2 u) (hv : SectorL2 v) :
    rop α (u - v) = rop α u - rop α v := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ v, rop_add α hu (sectorL2_smul (-1) hv),
    rop_smul, neg_one_smul, ← sub_eq_add_neg]

/-- **`R_α² = I`** — the involution property ([ksindexi] `rop_props`), from
`P M_α† = M_α P`, `M_α† M_α = I`, and `P² = I`. -/
lemma rop_involutive (α : ℝ) {u : Idx → ℂ} (hu : SectorL2 u) : rop α (rop α u) = u := by
  unfold rop
  rw [parity_neg, parity_mulAdag, parity_involutive, mulAdag_neg, mulAdag_mulA α hu, neg_neg]

lemma mulA_neg (α : ℝ) (u : Idx → ℂ) : mulA α (-u) = -mulA α u := by
  rw [← neg_one_smul ℂ u, mulA_smul, neg_one_smul]

/-- **`M_α M_α† = I`** (the other inverse; from `ς² = 1` and `cos² + sin² = 1`). -/
lemma mulA_mulAdag (α : ℝ) {u : Idx → ℂ} (hu : SectorL2 u) : mulA α (mulAdag α u) = u := by
  have hς : SectorL2 (sgn u) := sectorL2_sgn hu
  have hs : sgn (mulAdag α u)
      = (Real.cos (α * Real.pi) : ℂ) • sgn u
        + (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • u := by
    simp only [mulAdag]
    rw [sgn_add (sectorL2_smul _ hu) (sectorL2_smul _ hς), sgn_smul, sgn_smul,
      sgn_involutive hu]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  simp only [mulA]
  rw [hs]
  simp only [mulAdag]
  match_scalars
  all_goals try ring
  all_goals rw [hI]
  all_goals linear_combination Complex.sin_sq_add_cos_sq ((α : ℂ) * (Real.pi : ℂ))

/-- **`M_α† P = P M_α`** (the other order; from `parity_mulAdag` and `P² = I`). -/
lemma mulAdag_parity (α : ℝ) (u : Idx → ℂ) : mulAdag α (parity u) = parity (mulA α u) := by
  have h := parity_mulAdag α (parity u)
  rw [parity_involutive] at h
  rw [← h, parity_involutive]

/-! ### `R_α` on the eigenvectors

`R_α = −M_α† P` acts as a scalar on the two eigenspaces of the reduction: on a
`+`-eigenvector (`M_α u = P u`) it is `−I`, on a `−`-eigenvector (`M_α u = −P u`)
it is `+I`.  Both follow purely from `M_α† M_α = I`.  (These package the
eigenvalue conditions `mulA_iota{Tan,Cot}` of `SectorReduce` into the `rop`
language the form-symmetry `NBform_rop` speaks.) -/

/-- On a `+`-eigenvector `M_α u = P u`, `R_α u = −u` (so `u ∈ ker(R_α + I)`). -/
lemma rop_eq_neg_of_mulA_eq_parity (α : ℝ) {u : Idx → ℂ} (hu : SectorL2 u)
    (h : mulA α u = parity u) : rop α u = -u := by
  rw [rop, ← h, mulAdag_mulA α hu]

/-- On a `−`-eigenvector `M_α u = −P u`, `R_α u = u` (so `u ∈ ker(R_α − I)`). -/
lemma rop_eq_self_of_mulA_eq_neg_parity (α : ℝ) {u : Idx → ℂ} (hu : SectorL2 u)
    (h : mulA α u = -parity u) : rop α u = u := by
  have hp : parity u = -mulA α u := by rw [h, neg_neg]
  rw [rop, hp, mulAdag_neg, mulAdag_mulA α hu, neg_neg]

/-- Converse of `rop_eq_neg_of_mulA_eq_parity`: `R_α u = −u ⟹ M_α u = P u`
(apply `M_α` to `M_α† P u = u`, using `M_α M_α† = I`). -/
lemma mulA_eq_parity_of_rop_eq_neg (α : ℝ) {u : Idx → ℂ} (hu : SectorL2 u)
    (h : rop α u = -u) : mulA α u = parity u := by
  have h' : -(mulAdag α (parity u)) = -u := h
  have h1 : mulAdag α (parity u) = u := neg_inj.mp h'
  have h2 := mulA_mulAdag α (sectorL2_parity hu)
  rwa [h1] at h2

/-- Converse of `rop_eq_self_of_mulA_eq_neg_parity`: `R_α u = u ⟹ M_α u = −P u`. -/
lemma mulA_eq_neg_parity_of_rop_eq_self (α : ℝ) {u : Idx → ℂ} (hu : SectorL2 u)
    (h : rop α u = u) : mulA α u = -parity u := by
  have h' : -(mulAdag α (parity u)) = u := h
  have h1 : mulAdag α (parity u) = -u := neg_eq_iff_eq_neg.mp h'
  have h2 := mulA_mulAdag α (sectorL2_parity hu)
  rw [h1, mulA_neg] at h2
  exact neg_eq_iff_eq_neg.mp h2

end KsIndex.Sector
