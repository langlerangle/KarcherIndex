module

/-
# Twisted one-period domains and sector index transport

For `m > 0`, a translation eigenfunction satisfying `u (n + 2) = ζ * u n`
is determined by copies `0` and `1`. The inverse extension assigns
`ζ^q * v r` to copy `n = 2q + r`. The condition `ζ^m = 1` makes the
extension compatible with the cyclic identification of the `2m` copies.

`TwistedCc k ζ` consists of pairs smooth on the open disks and across
the two seams, zero outside the closed disks, and vanishing near the
punctures. The seam from copy `0` to copy `1` is untwisted. Across the
other seam, `glueTw` uses `v 1` on the closed disk and
`ζ * v 0 (1 / conj w)` outside. `DomTw` expresses this domain in
uncurried coordinates for the form-index construction.

Restriction and extension preserve the eigenspace of `rotE` with
multiplier `a` and eigenvalue `μ`. For `‖ζ‖ = 1`, the Jacobi form on
the translation eigenspace equals `m` times the one-period form of its
restriction. `formIndex_sector_eq` combines this identity with domain
transport and positive scaling to identify the two indices, assuming
`m > 0` and `ζ^m = 1`. In the untwisted case, `twistedCc_one` identifies
`TwistedCc k 1` with `CcSmooth k 1`.
-/
public import KsIndexLean.SurfaceSym
public import KsIndexLean.SectorIndex

@[expose] public section


noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped ContDiff

namespace KsIndex.Twisted

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.FormIndex
  KsIndex.SectorIndex

variable {k m : ℕ}

instance : NeZero (2 * 1) := ⟨by norm_num⟩

/-! ### The twisted glue and the twisted one-period space -/

/-- The glued function across the twisted seam `(1, 0)`: `v_1` on the closed disk,
`ζ · v_0 (1/w̄)` outside. -/
def glueTw (ζ : ℂ) (v : ZMod (2 * 1) → ℂ → ℂ) (w : ℂ) : ℂ :=
  if ‖w‖ ≤ 1 then v 1 w else ζ * v 0 (1 / (starRingEnd ℂ) w)

lemma glueTw_add (ζ : ℂ) (u v : ZMod (2 * 1) → ℂ → ℂ) :
    glueTw ζ (u + v) = glueTw ζ u + glueTw ζ v := by
  funext w
  simp only [glueTw, Pi.add_apply]
  split_ifs <;> ring

lemma glueTw_smul (ζ c : ℂ) (u : ZMod (2 * 1) → ℂ → ℂ) :
    glueTw ζ (c • u) = c • glueTw ζ u := by
  funext w
  simp only [glueTw, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

lemma glueTw_zero (ζ : ℂ) : glueTw ζ (0 : ZMod (2 * 1) → ℂ → ℂ) = 0 := by
  funext w
  simp only [glueTw, Pi.zero_apply, mul_zero]
  split_ifs <;> rfl

/-- Smoothness of a one-period pair with twist `ζ`: smooth on each open disk, smooth across the
untwisted seam `(0,1)` and across the twisted seam `(1,0)`, vanishing outside the closed disk. -/
def IsSmoothTw (k : ℕ) (ζ : ℂ) (v : ZMod (2 * 1) → ℂ → ℂ) : Prop :=
  (∀ n, ContDiffOn ℝ ∞ (v n) disk)
    ∧ (∀ w ∈ seamArc k 1 0, ContDiffAt ℝ ∞ (glue v 0) w)
    ∧ (∀ w ∈ seamArc k 1 1, ContDiffAt ℝ ∞ (glueTw ζ v) w)
    ∧ (∀ n w, 1 < ‖w‖ → v n w = 0)

lemma isSmoothTw_zero (k : ℕ) (ζ : ℂ) : IsSmoothTw k ζ 0 := by
  refine ⟨fun n => contDiffOn_const, fun w _ => ?_, fun w _ => ?_, fun n w _ => rfl⟩
  · rw [glue_zero]; exact contDiffAt_const
  · rw [glueTw_zero]; exact contDiffAt_const

lemma isSmoothTw_add {ζ : ℂ} {u v : ZMod (2 * 1) → ℂ → ℂ} (hu : IsSmoothTw k ζ u)
    (hv : IsSmoothTw k ζ v) : IsSmoothTw k ζ (u + v) := by
  refine ⟨fun n => (hu.1 n).add (hv.1 n), fun w hw => ?_, fun w hw => ?_, fun n w hw => ?_⟩
  · rw [glue_add]; exact (hu.2.1 w hw).add (hv.2.1 w hw)
  · rw [glueTw_add]; exact (hu.2.2.1 w hw).add (hv.2.2.1 w hw)
  · simp only [Pi.add_apply, hu.2.2.2 n w hw, hv.2.2.2 n w hw, add_zero]

lemma isSmoothTw_smul {ζ : ℂ} (c : ℂ) {u : ZMod (2 * 1) → ℂ → ℂ} (hu : IsSmoothTw k ζ u) :
    IsSmoothTw k ζ (c • u) := by
  refine ⟨fun n => (hu.1 n).const_smul c, fun w hw => ?_, fun w hw => ?_, fun n w hw => ?_⟩
  · rw [glue_smul]; exact (hu.2.1 w hw).const_smul c
  · rw [glueTw_smul]; exact (hu.2.2.1 w hw).const_smul c
  · simp only [Pi.smul_apply, hu.2.2.2 n w hw, smul_zero]

/-- `C_c^∞` of the twisted one period: the twisted-smooth pairs vanishing near the punctures. -/
def TwistedCc (k : ℕ) (ζ : ℂ) : Submodule ℂ (ZMod (2 * 1) → ℂ → ℂ) where
  carrier := {v | IsSmoothTw k ζ v ∧ SuppAwayP k 1 v}
  zero_mem' := ⟨isSmoothTw_zero k ζ, suppAwayP_zero k 1⟩
  add_mem' := fun hu hv => ⟨isSmoothTw_add hu.1 hv.1, suppAwayP_add hu.2 hv.2⟩
  smul_mem' := fun c _ hu => ⟨isSmoothTw_smul c hu.1, suppAwayP_smul c hu.2⟩

/-- The twisted one-period domain in the uncurried coordinates used by `FormIndex`. -/
def DomTw (k : ℕ) (ζ : ℂ) : Submodule ℂ (ZMod (2 * 1) × ℂ → ℂ) :=
  (TwistedCc k ζ).map (uncurryE 1).toLinearMap

lemma mem_DomTw {ζ : ℂ} {V : ZMod (2 * 1) × ℂ → ℂ} :
    V ∈ DomTw k ζ ↔ (uncurryE 1).symm V ∈ TwistedCc k ζ :=
  Submodule.mem_map_equiv (TwistedCc k ζ)

/-! ### Scaling of the one-copy Jacobi summand by a constant -/

lemma gradSq_const_mul (c : ℂ) (f : ℂ → ℂ) (w : ℂ) :
    gradSq (fun z => c * f z) w = ‖c‖ ^ 2 * gradSq f w := by
  by_cases hc : c = 0
  · subst hc
    simp [gradSq]
  by_cases hf : DifferentiableAt ℝ f w
  · have h : fderiv ℝ (fun z => c * f z) w = c • fderiv ℝ f w := fderiv_const_mul hf c
    simp [gradSq, h, mul_pow]
    ring
  · have hf' : ¬ DifferentiableAt ℝ (fun z => c * f z) w := by
      intro h
      have : DifferentiableAt ℝ (fun z => c⁻¹ * (c * f z)) w := h.const_mul _
      refine hf (this.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_))
      simp [hc]
    simp [gradSq, fderiv_zero_of_not_differentiableAt hf,
      fderiv_zero_of_not_differentiableAt hf']

lemma dirichletG_const_mul (k : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    dirichletG k (fun z => c * f z) = ‖c‖ ^ 2 * dirichletG k f := by
  unfold dirichletG
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [gradSq_const_mul]
  ring

lemma potentialG_const_mul (k : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    potentialG k (fun z => c * f z) = ‖c‖ ^ 2 * potentialG k f := by
  unfold potentialG
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [norm_mul]
  ring

/-- A unimodular multiple of a copy contributes the same Jacobi summand. -/
lemma summand_unit_mul (k : ℕ) {c : ℂ} (hc : ‖c‖ = 1) (f : ℂ → ℂ) :
    dirichletG k (fun z => c * f z) - potentialG k (fun z => c * f z)
      = dirichletG k f - potentialG k f := by
  rw [dirichletG_const_mul, potentialG_const_mul, hc]
  ring

/-! ### Restriction to one period and quasi-periodic extension -/

/-- Restriction of a function on `Ξ_{k,m}` to the copies `{0, 1}`. -/
def restrE (m : ℕ) : (ZMod (2 * m) × ℂ → ℂ) →ₗ[ℂ] (ZMod (2 * 1) × ℂ → ℂ) where
  toFun U := fun p => U (((p.1.val : ℕ) : ZMod (2 * m)), p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma restrE_apply (U : ZMod (2 * m) × ℂ → ℂ) (p : ZMod (2 * 1) × ℂ) :
    restrE m U p = U (((p.1.val : ℕ) : ZMod (2 * m)), p.2) := rfl

/-- Quasi-periodic extension of a one-period pair: copy `n = 2q + r` carries `ζ^q · v_r`. -/
def extE (m : ℕ) (ζ : ℂ) : (ZMod (2 * 1) × ℂ → ℂ) →ₗ[ℂ] (ZMod (2 * m) × ℂ → ℂ) where
  toFun V := fun p => ζ ^ (p.1.val / 2) * V (((p.1.val % 2 : ℕ) : ZMod (2 * 1)), p.2)
  map_add' _ _ := by funext p; simp [mul_add]
  map_smul' _ _ := by funext p; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma extE_apply (ζ : ℂ) (V : ZMod (2 * 1) × ℂ → ℂ) (p : ZMod (2 * m) × ℂ) :
    extE m ζ V p = ζ ^ (p.1.val / 2) * V (((p.1.val % 2 : ℕ) : ZMod (2 * 1)), p.2) := rfl

/-- The translation eigen-condition, pointwise. -/
lemma mem_shift_iff {ζ : ℂ} {U : ZMod (2 * m) × ℂ → ℂ} :
    U ∈ Module.End.eigenspace (shiftE m) ζ ↔ ∀ n w, U (n + 2, w) = ζ * U (n, w) := by
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · intro h n w
    have := congr_fun h (n, w)
    simpa [shiftE_apply] using this
  · intro h
    funext p
    simp [shiftE_apply, h]

lemma shift_iter {ζ : ℂ} {U : ZMod (2 * m) × ℂ → ℂ}
    (hU : ∀ n w, U (n + 2, w) = ζ * U (n, w)) (r q : ℕ) (w : ℂ) :
    U (((r + 2 * q : ℕ) : ZMod (2 * m)), w) = ζ ^ q * U ((r : ZMod (2 * m)), w) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h : ((r + 2 * (q + 1) : ℕ) : ZMod (2 * m)) = ((r + 2 * q : ℕ) : ZMod (2 * m)) + 2 := by
      push_cast; ring
    rw [h, hU, ih, pow_succ]
    ring

lemma val_decomp [NeZero m] (n : ZMod (2 * m)) :
    n = ((n.val % 2 + 2 * (n.val / 2) : ℕ) : ZMod (2 * m)) := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  rw [Nat.mod_add_div, ZMod.natCast_zmod_val]

/-- A function in the translation eigenspace is its own quasi-periodic extension. -/
lemma sector_val [NeZero m] {ζ : ℂ} {U : ZMod (2 * m) × ℂ → ℂ}
    (hU : ∀ n w, U (n + 2, w) = ζ * U (n, w)) (n : ZMod (2 * m)) (w : ℂ) :
    U (n, w) = ζ ^ (n.val / 2) * U (((n.val % 2 : ℕ) : ZMod (2 * m)), w) := by
  conv_lhs => rw [val_decomp n]
  exact shift_iter hU _ _ w

lemma val_lt_two (r : ZMod (2 * 1)) : r.val < 2 := ZMod.val_lt r

lemma restrE_extE [NeZero m] (ζ : ℂ) (V : ZMod (2 * 1) × ℂ → ℂ) :
    restrE m (extE m ζ V) = V := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  funext p
  have hlt : p.1.val < 2 * m := by have := val_lt_two p.1; have := NeZero.ne m; omega
  simp only [restrE_apply, extE_apply, ZMod.val_cast_of_lt hlt]
  rw [Nat.div_eq_of_lt (val_lt_two p.1), Nat.mod_eq_of_lt (val_lt_two p.1), pow_zero, one_mul,
    ZMod.natCast_zmod_val]

lemma extE_restrE [NeZero m] {ζ : ℂ} {U : ZMod (2 * m) × ℂ → ℂ}
    (hU : ∀ n w, U (n + 2, w) = ζ * U (n, w)) : extE m ζ (restrE m U) = U := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  funext p
  obtain ⟨n, w⟩ := p
  have hv : (((n.val % 2 : ℕ) : ZMod (2 * 1))).val = n.val % 2 := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
  simp only [extE_apply, restrE_apply, hv]
  exact (sector_val hU n w).symm

/-! ### Rotation compatibility -/

lemma restrE_rotE (a : ℂ) (U : ZMod (2 * m) × ℂ → ℂ) :
    restrE m (rotE m a U) = rotE 1 a (restrE m U) := rfl

lemma extE_rotE (ζ a : ℂ) (V : ZMod (2 * 1) × ℂ → ℂ) :
    extE m ζ (rotE 1 a V) = rotE m a (extE m ζ V) := rfl

lemma restrE_mem_rot {a μ : ℂ} {U : ZMod (2 * m) × ℂ → ℂ}
    (hU : U ∈ Module.End.eigenspace (rotE m a) μ) :
    restrE m U ∈ Module.End.eigenspace (rotE 1 a) μ := by
  rw [Module.End.mem_eigenspace_iff] at hU ⊢
  rw [← restrE_rotE, hU, map_smul]

lemma extE_mem_rot {ζ a μ : ℂ} {V : ZMod (2 * 1) × ℂ → ℂ}
    (hV : V ∈ Module.End.eigenspace (rotE 1 a) μ) :
    extE m ζ V ∈ Module.End.eigenspace (rotE m a) μ := by
  rw [Module.End.mem_eigenspace_iff] at hV ⊢
  rw [← extE_rotE, hV, map_smul]

/-! ### Seam indices -/

lemma parity_val [NeZero m] (n : ZMod (2 * m)) : (parity m n).val = n.val % 2 := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  rw [parity, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

lemma seamArc_eq [NeZero m] (n : ZMod (2 * m)) : seamArc k m n = arc k ((n + 1).val % 2) := by
  rw [seamArc, parity_val]

lemma val_two_mod_two [NeZero m] : ((2 : ZMod (2 * m)).val) % 2 = 0 := by
  rw [ZMod.val_two_eq_two_mod, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 m)]

lemma val_zero_two : ((0 : ZMod (2 * 1)).val : ℕ) = 0 := rfl
lemma val_one_two : ((1 : ZMod (2 * 1)).val : ℕ) = 1 := rfl

lemma seamArc_one_zero : seamArc k 1 0 = arc k 1 := by
  rw [seamArc_eq, zero_add, val_one_two]

lemma seamArc_one_one : seamArc k 1 1 = arc k 0 := by
  rw [seamArc_eq, one_add_one_eq_two, val_two_mod_two]

/-! ### Restriction lands in the twisted space -/

/-- The curried restriction. -/
def resF (m : ℕ) (u : ZMod (2 * m) → ℂ → ℂ) : ZMod (2 * 1) → ℂ → ℂ :=
  fun r w => u ((r.val : ℕ) : ZMod (2 * m)) w

lemma uncurry_symm_restrE (U : ZMod (2 * m) × ℂ → ℂ) :
    (uncurryE 1).symm (restrE m U) = resF m ((uncurryE m).symm U) := rfl

lemma resF_mem [NeZero m] {ζ : ℂ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ CcSmooth k m)
    (hU : ∀ n w, u (n + 2) w = ζ * u n w) : resF m u ∈ TwistedCc k ζ := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have : Fact (1 < 2 * m) := ⟨by have := NeZero.ne m; omega⟩
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, ⟨ε, hε, hz⟩⟩ := hu
  refine ⟨⟨fun r => hsm1 _, fun w hw => ?_, fun w hw => ?_, fun r w hw => hsm3 _ w hw⟩,
    ⟨ε, hε, fun r w hw => hz _ w hw⟩⟩
  · have hg : glue (resF m u) 0 = glue u 0 := by
      funext w
      simp only [glue, resF, zero_add, val_zero_two, val_one_two, Nat.cast_zero, Nat.cast_one]
    rw [hg]
    refine hsm2 0 w ?_
    rw [seamArc_eq, zero_add, ZMod.val_one, show (1 : ℕ) % 2 = 1 from rfl]
    rwa [seamArc_one_zero] at hw
  · have hg : glueTw ζ (resF m u) = glue u 1 := by
      funext w
      simp only [glueTw, glue, resF, val_zero_two, val_one_two, Nat.cast_zero, Nat.cast_one,
        one_add_one_eq_two]
      split_ifs
      · rfl
      · rw [← hU 0 _, zero_add]
    rw [hg]
    refine hsm2 1 w ?_
    rw [seamArc_eq, one_add_one_eq_two, val_two_mod_two]
    rwa [seamArc_one_one] at hw

/-! ### Extension lands in the sector -/

/-- The curried extension. -/
def extF (m : ℕ) (ζ : ℂ) (v : ZMod (2 * 1) → ℂ → ℂ) : ZMod (2 * m) → ℂ → ℂ :=
  fun n w => ζ ^ (n.val / 2) * v ((n.val % 2 : ℕ) : ZMod (2 * 1)) w

lemma uncurry_symm_extE (ζ : ℂ) (V : ZMod (2 * 1) × ℂ → ℂ) :
    (uncurryE m).symm (extE m ζ V) = extF m ζ ((uncurryE 1).symm V) := rfl

/-- The glued extension across the seam `(n, n+1)` is `ζ^q` times the glued pair across the
corresponding one-period seam. -/
lemma glue_extF [NeZero m] {ζ : ℂ} (hζm : ζ ^ m = 1) (v : ZMod (2 * 1) → ℂ → ℂ)
    (n : ZMod (2 * m)) :
    glue (extF m ζ v) n = fun w => ζ ^ (n.val / 2) *
      (if n.val % 2 = 0 then glue v 0 w else glueTw ζ v w) := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have : Fact (1 < 2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have hlt := ZMod.val_lt n
  have hval : (n + 1).val = (n.val + 1) % (2 * m) := by rw [ZMod.val_add, ZMod.val_one]
  funext w
  simp only [glue, extF]
  rcases Nat.even_or_odd' n.val with ⟨q, hq | hq⟩
  · -- even copy: `(n+1).val = n.val + 1`, same `q`, `r = 1`
    have h1 : (n + 1).val = n.val + 1 := by rw [hval]; exact Nat.mod_eq_of_lt (by omega)
    have hr0 : n.val % 2 = 0 := by omega
    have hq0 : n.val / 2 = q := by omega
    have hq1 : (n.val + 1) / 2 = q := by omega
    have hr1 : (n.val + 1) % 2 = 1 := by omega
    simp only [h1, hr0, hq0, hq1, hr1, if_true, Nat.cast_zero, Nat.cast_one, zero_add]
    split_ifs <;> rfl
  · -- odd copy
    have hr1 : n.val % 2 = 1 := by omega
    have hq0 : n.val / 2 = q := by omega
    simp only [hr1, hq0, one_ne_zero, if_false, glueTw, Nat.cast_one]
    by_cases hwrap : n.val + 1 < 2 * m
    · have h1 : (n + 1).val = n.val + 1 := by rw [hval]; exact Nat.mod_eq_of_lt hwrap
      have hq1 : (n.val + 1) / 2 = q + 1 := by omega
      have hr0 : (n.val + 1) % 2 = 0 := by omega
      simp only [h1, hq1, hr0, Nat.cast_zero]
      split_ifs
      · rfl
      · rw [pow_succ]; ring
    · have h1 : (n + 1).val = 0 := by
        rw [hval]
        have : n.val + 1 = 2 * m := by omega
        rw [this, Nat.mod_self]
      have hqm : q + 1 = m := by omega
      simp only [h1, Nat.zero_div, Nat.zero_mod, Nat.cast_zero, pow_zero, one_mul]
      split_ifs
      · rfl
      · rw [← mul_assoc, ← pow_succ, hqm, hζm, one_mul]

lemma extF_mem [NeZero m] {ζ : ℂ} (hζm : ζ ^ m = 1) {v : ZMod (2 * 1) → ℂ → ℂ}
    (hv : v ∈ TwistedCc k ζ) : extF m ζ v ∈ CcSmooth k m := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have : Fact (1 < 2 * m) := ⟨by have := NeZero.ne m; omega⟩
  obtain ⟨⟨hsm1, hsm2, hsm3, hsm4⟩, ⟨ε, hε, hz⟩⟩ := hv
  refine ⟨⟨fun n => contDiffOn_const.mul (hsm1 _), fun n w hw => ?_, fun n w hw => ?_⟩,
    ⟨ε, hε, fun n w hw => ?_⟩⟩
  · rw [glue_extF hζm]
    refine contDiffAt_const.mul ?_
    have hval : (n + 1).val = (n.val + 1) % (2 * m) := by rw [ZMod.val_add, ZMod.val_one]
    rw [seamArc_eq] at hw
    by_cases hr : n.val % 2 = 0
    · simp only [hr, if_true]
      refine hsm2 w ?_
      rw [seamArc_one_zero]
      have hlt := ZMod.val_lt n
      have h1 : (n + 1).val = n.val + 1 := by rw [hval]; exact Nat.mod_eq_of_lt (by omega)
      have : (n + 1).val % 2 = 1 := by rw [h1]; omega
      rwa [this] at hw
    · simp only [hr, if_false]
      refine hsm3 w ?_
      rw [seamArc_one_one]
      have hlt := ZMod.val_lt n
      have : (n + 1).val % 2 = 0 := by
        rw [hval]
        by_cases hwrap : n.val + 1 < 2 * m
        · rw [Nat.mod_eq_of_lt hwrap]; omega
        · have : n.val + 1 = 2 * m := by omega
          rw [this, Nat.mod_self]
      rwa [this] at hw
  · simp only [extF, hsm4 _ w hw, mul_zero]
  · simp only [extF, hz _ w hw, mul_zero]

lemma extE_mem_shift [NeZero m] {ζ : ℂ} (hζm : ζ ^ m = 1) (V : ZMod (2 * 1) × ℂ → ℂ) :
    extE m ζ V ∈ Module.End.eigenspace (shiftE m) ζ := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  rw [mem_shift_iff]
  intro n w
  simp only [extE_apply]
  have hlt := ZMod.val_lt n
  have hval : (n + 2).val = (n.val + 2) % (2 * m) := by
    rw [ZMod.val_add, ZMod.val_two_eq_two_mod, Nat.add_mod_mod]
  by_cases hwrap : n.val + 2 < 2 * m
  · rw [hval, Nat.mod_eq_of_lt hwrap]
    have h1 : (n.val + 2) / 2 = n.val / 2 + 1 := by omega
    have h2 : (n.val + 2) % 2 = n.val % 2 := by omega
    rw [h1, h2, pow_succ]; ring
  · have h0 : (n + 2).val = n.val + 2 - 2 * m := by
      rw [hval]
      have : n.val + 2 - 2 * m < 2 * m := by omega
      conv_lhs => rw [show n.val + 2 = (n.val + 2 - 2 * m) + 1 * (2 * m) by omega]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt this]
    rw [h0]
    have h1 : n.val / 2 + 1 = (n.val + 2 - 2 * m) / 2 + m := by omega
    have h2 : (n.val + 2 - 2 * m) % 2 = n.val % 2 := by omega
    rw [h2, ← mul_assoc, ← pow_succ', h1, pow_add, hζm]
    ring

/-! ### The form on a sector is `m` times the one-period form -/

lemma sum_zmod_mod_two [NeZero m] (f : ℕ → ℝ) :
    ∑ n : ZMod (2 * m), f (n.val % 2) = m * (f 0 + f 1) := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have hsum : ∑ n : ZMod (2 * m), f (n.val % 2) = ∑ i ∈ Finset.range (2 * m), f (i % 2) := by
    symm
    refine Finset.sum_bij' (fun i _ => (i : ZMod (2 * m))) (fun n _ => n.val) ?_ ?_ ?_ ?_ ?_
    · intros; exact Finset.mem_univ _
    · intro n _; exact Finset.mem_range.mpr (ZMod.val_lt n)
    · intro i hi; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hi)
    · intro n _; exact ZMod.natCast_zmod_val n
    · intro i hi; rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hi)]
  rw [hsum]
  clear hsum this
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Nat.mul_mod_right, show (2 * m + 1) % 2 = 1 by omega]
    push_cast; ring

lemma sum_zmod_two (g : ZMod (2 * 1) → ℝ) : ∑ r, g r = g 0 + g 1 := by
  rw [show (Finset.univ : Finset (ZMod (2 * 1))) = {0, 1} by decide, Finset.sum_pair (by decide)]

lemma Qs_eq_mul_restr [NeZero m] {ζ : ℂ} (hζ : ‖ζ‖ = 1) {U : ZMod (2 * m) × ℂ → ℂ}
    (hU : ∀ n w, U (n + 2, w) = ζ * U (n, w)) :
    Qs k m U = m * Qs k 1 (restrE m U) := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  simp only [Qs, uncurry_symm_restrE, jacobiQ]
  set u := (uncurryE m).symm U with hu
  have hterm : ∀ n : ZMod (2 * m), dirichletG k (u n) - potentialG k (u n)
      = dirichletG k (u ((n.val % 2 : ℕ) : ZMod (2 * m)))
        - potentialG k (u ((n.val % 2 : ℕ) : ZMod (2 * m))) := by
    intro n
    have hfun : u n = fun w => ζ ^ (n.val / 2) * u ((n.val % 2 : ℕ) : ZMod (2 * m)) w :=
      funext fun w => sector_val hU n w
    rw [hfun]
    exact summand_unit_mul k (by rw [norm_pow, hζ, one_pow]) _
  rw [Finset.sum_congr rfl fun n _ => hterm n]
  rw [sum_zmod_mod_two (fun r => dirichletG k (u ((r : ℕ) : ZMod (2 * m)))
    - potentialG k (u ((r : ℕ) : ZMod (2 * m))))]
  congr 1
  rw [sum_zmod_two]
  rfl

/-! ### The transport theorem -/

/-- For `m > 0`, `‖ζ‖ = 1` and `ζ^m = 1`, restriction to one period
preserves the form index of the joint `rotE m a` and translation eigenspace.
The target is the twisted domain with the same `rotE 1 a` eigenvalue `μ`. -/
theorem formIndex_sector_eq [NeZero m] {a μ ζ : ℂ} (hζ : ‖ζ‖ = 1) (hζm : ζ ^ m = 1) :
    formIndex (Qs k m)
        ((Dom k m ⊓ Module.End.eigenspace (rotE m a) μ) ⊓ Module.End.eigenspace (shiftE m) ζ)
      = formIndex (Qs k 1) (DomTw k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [← formIndex_smul_pos (Q := Qs k 1)
    (D := DomTw k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ) hm]
  refine formIndex_transport (restrE m) ?_ ?_ ?_ ?_
  · intro U hU
    obtain ⟨⟨hD, hR⟩, hS⟩ := hU
    refine Submodule.mem_inf.mpr ⟨?_, restrE_mem_rot hR⟩
    rw [mem_DomTw, uncurry_symm_restrE]
    exact resF_mem (mem_Dom.mp hD) (mem_shift_iff.mp hS)
  · intro U hU V hV h
    rw [← extE_restrE (mem_shift_iff.mp hU.2), ← extE_restrE (mem_shift_iff.mp hV.2), h]
  · intro V hV
    obtain ⟨hD, hR⟩ := Submodule.mem_inf.mp hV
    refine ⟨extE m ζ V, ?_, restrE_extE ζ V⟩
    refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, extE_mem_rot hR⟩,
      extE_mem_shift hζm V⟩
    rw [mem_Dom, uncurry_symm_extE]
    exact extF_mem hζm (mem_DomTw.mp hD)
  · intro U hU
    exact Qs_eq_mul_restr hζ (mem_shift_iff.mp hU.2)

/-- The untwisted case `ζ = 1`: the twisted domain equals `CcSmooth k 1`. -/
lemma twistedCc_one (k : ℕ) : TwistedCc k 1 = CcSmooth k 1 := by
  ext v
  change (IsSmoothTw k 1 v ∧ SuppAwayP k 1 v) ↔ (IsSmooth k 1 v ∧ SuppAwayP k 1 v)
  have h2 : (1 + 1 : ZMod (2 * 1)) = 0 := by decide
  have hg : glue v 1 = glueTw 1 v := by
    funext w; simp only [glue, glueTw, one_mul, h2]
  have hn : ∀ r : ZMod (2 * 1), r = 0 ∨ r = 1 := by decide
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    refine ⟨⟨h1, fun n w hw => ?_, h4⟩, h5⟩
    rcases hn n with rfl | rfl
    · exact h2 w hw
    · rw [hg]; exact h3 w hw
  · rintro ⟨⟨h1, h2, h4⟩, h5⟩
    exact ⟨⟨h1, fun w hw => h2 0 w hw, fun w hw => hg ▸ h2 1 w hw, h4⟩, h5⟩

end KsIndex.Twisted
