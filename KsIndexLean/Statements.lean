module

/-
KsIndexLean — Circle-level index, nullity and threshold results for [ksindexi].

`Dom` realizes the trace domain as a complex subspace of integer-indexed
sequences. The Hermitian form `Bform` is conjugate-linear in its first slot
and recovers `Qform` on the diagonal. Index and radical nullity are defined
in `ℕ∞` as suprema of finite-dimensional subspace dimensions; their finiteness
is proved, not imposed in the definitions. These definitions use no topology
on `Dom`.

The head-coordinate argument proves `ind s + nul s ≤ 1` for every real `s`:
a nonpositive subspace cannot contain a nonzero vector with zero head
coordinate. Here the sequence index is `0`, corresponding to physical
frequency `1` on the `6n+1` lattice.

For `s > 0`, the attained variational infimum `gam s` gives the sign dictionary:
index is one exactly when `gam s < 0`, and radical nullity is one exactly
when `gam s = 0`. Continuity, strict monotonicity and the two endpoint signs
then give a unique crossing in `(1, √3)` and the classification `circle_main`.
The lower endpoint sign uses the direct trial-field proof in `GammaOne`;
`GammaOnePaperRoute` separately follows the paper's index-based derivation.
These are circle-form results; geometric surface transports are separate.
-/
public import KsIndexLean.CircleQ
public import KsIndexLean.Threshold
public import KsIndexLean.GammaOne

@[expose] public section


noncomputable section

namespace KsIndex.Statements

open KsIndex.CircleQ KsIndex.Threshold Real Set

/-! ### Closure of the domain: `MemDom` is a subspace condition -/

lemma convS_smul (c : ℂ) (u : ℤ → ℂ) (m : ℤ) :
    convS (c • u) m = c * convS u m :=
  GammaOne.convS_smul' c u m

lemma convS_add {u v : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2)
    (hv : Summable fun n : ℤ => ‖v n‖ ^ 2) (m : ℤ) :
    convS (u + v) m = convS u m + convS v m := by
  have h := (summable_conv_term hu m).tsum_add (summable_conv_term hv m)
  rw [convS, convS, convS, ← h]
  congr 1
  funext n
  simp only [Pi.add_apply]
  ring

lemma memDom_zero : MemDom (0 : ℤ → ℂ) := by
  constructor
  · exact summable_zero.congr fun n => by simp
  · exact summable_zero.congr fun m => by simp [convS]

lemma memDom_smul (c : ℂ) {u : ℤ → ℂ} (hu : MemDom u) : MemDom (c • u) :=
  GammaOne.memDom_smul' c hu

lemma memDom_add {u v : ℤ → ℂ} (hu : MemDom u) (hv : MemDom v) :
    MemDom (u + v) := by
  constructor
  · refine ((hu.1.add hv.1).mul_left 2).of_nonneg_of_le
      (fun n => by positivity) fun n => ?_
    have h1 : ‖(u + v) n‖ ≤ ‖u n‖ + ‖v n‖ := by
      simp only [Pi.add_apply]
      exact norm_add_le _ _
    have hX : ‖(u + v) n‖ ^ 2 ≤ 2 * ‖u n‖ ^ 2 + 2 * ‖v n‖ ^ 2 := by
      nlinarith [norm_nonneg ((u + v) n), norm_nonneg (u n), norm_nonneg (v n),
        sq_nonneg (‖u n‖ - ‖v n‖)]
    calc |6 * (n : ℝ) + 1| * ‖(u + v) n‖ ^ 2
        ≤ |6 * (n : ℝ) + 1| * (2 * ‖u n‖ ^ 2 + 2 * ‖v n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hX (abs_nonneg _)
      _ = 2 * (|6 * (n : ℝ) + 1| * ‖u n‖ ^ 2
            + |6 * (n : ℝ) + 1| * ‖v n‖ ^ 2) := by ring
  · have hconv := convS_add (summable_normSq hu.1) (summable_normSq hv.1)
    refine ((hu.2.add hv.2).mul_left 2).of_nonneg_of_le
      (fun m => by positivity) fun m => ?_
    have h1 : ‖convS (u + v) m‖ ≤ ‖convS u m‖ + ‖convS v m‖ := by
      rw [hconv m]
      exact norm_add_le _ _
    have hX : ‖convS (u + v) m‖ ^ 2
        ≤ 2 * ‖convS u m‖ ^ 2 + 2 * ‖convS v m‖ ^ 2 := by
      nlinarith [norm_nonneg (convS (u + v) m), norm_nonneg (convS u m),
        norm_nonneg (convS v m), sq_nonneg (‖convS u m‖ - ‖convS v m‖)]
    calc |6 * (m : ℝ) + 4| * ‖convS (u + v) m‖ ^ 2
        ≤ |6 * (m : ℝ) + 4| * (2 * ‖convS u m‖ ^ 2 + 2 * ‖convS v m‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hX (abs_nonneg _)
      _ = 2 * (|6 * (m : ℝ) + 4| * ‖convS u m‖ ^ 2
            + |6 * (m : ℝ) + 4| * ‖convS v m‖ ^ 2) := by ring

/-- The trace space `H^{1/2}_{ς,(+,2;3)}(S¹)` (coefficient model) as a
complex subspace of the full sequence space. -/
def Dom : Submodule ℂ (ℤ → ℂ) where
  carrier := {u | MemDom u}
  zero_mem' := memDom_zero
  add_mem' := fun hu hv => memDom_add hu hv
  smul_mem' := fun c _ hu => memDom_smul c hu

@[simp] lemma mem_Dom {u : ℤ → ℂ} : u ∈ Dom ↔ MemDom u := Iff.rfl

/-! ### The polarized form and the spectral counts -/

/-- The polarized Hermitian form `B_s` of `Q_s`, conjugate-linear in the
first slot. On `Dom × Dom` all sums converge absolutely. Outside the
domain the expression remains defined by Lean’s totalized `tsum`; the
variational results below require domain membership. -/
def Bform (s : ℝ) (u v : ℤ → ℂ) : ℂ :=
  (∑' n : ℤ, (sigP n : ℂ) * ((starRingEnd ℂ) (u n) * v n))
    + (s : ℂ) ^ 2 *
      ∑' m : ℤ, (sigM m : ℂ) * ((starRingEnd ℂ) (convS u m) * convS v m)

/-- On the diagonal the polarized form recovers `Q_s`, so `Bform` really
is a polarization of `Qform`. -/
lemma Bform_self (s : ℝ) (u : ℤ → ℂ) : Bform s u u = (Qform s u : ℂ) := by
  have h1 : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Bform, Qform, h1]
  push_cast [Complex.ofReal_tsum]
  ring

/-! #### Sesquilinear structure of `Bform` on the domain -/

/-- Absolute summability of the `+`-lattice pairing sum for two domain
elements (AM–GM: `|σ|‖u‖‖v‖ ≤ 3|ℓ|‖u‖‖v‖ ≤ (3/2)|ℓ|(‖u‖² + ‖v‖²)`). -/
lemma summable_pairP {u v : ℤ → ℂ}
    (hu : Summable fun n : ℤ => |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2)
    (hv : Summable fun n : ℤ => |6 * (n : ℝ) + 1| * ‖v n‖ ^ 2) :
    Summable fun n : ℤ => (sigP n : ℂ) * ((starRingEnd ℂ) (u n) * v n) := by
  refine Summable.of_norm ?_
  refine ((hu.add hv).mul_left (3 / 2)).of_nonneg_of_le (fun n => norm_nonneg _)
    fun n => ?_
  have hσ := abs_sigP_le n
  have hn : ‖(sigP n : ℂ) * ((starRingEnd ℂ) (u n) * v n)‖
      = |sigP n| * (‖u n‖ * ‖v n‖) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, starRingEnd_apply,
      norm_star]
  rw [hn]
  nlinarith [sq_nonneg (‖u n‖ - ‖v n‖), norm_nonneg (u n), norm_nonneg (v n),
    abs_nonneg (6 * (n : ℝ) + 1), abs_nonneg (sigP n),
    mul_le_mul_of_nonneg_right hσ
      (mul_nonneg (norm_nonneg (u n)) (norm_nonneg (v n)))]

/-- Absolute summability of the `-`-lattice pairing sum. -/
lemma summable_pairM {u v : ℤ → ℂ}
    (hu : Summable fun m : ℤ => |6 * (m : ℝ) + 4| * ‖convS u m‖ ^ 2)
    (hv : Summable fun m : ℤ => |6 * (m : ℝ) + 4| * ‖convS v m‖ ^ 2) :
    Summable fun m : ℤ =>
      (sigM m : ℂ) * ((starRingEnd ℂ) (convS u m) * convS v m) := by
  refine Summable.of_norm ?_
  refine ((hu.add hv).mul_left (3 / 2)).of_nonneg_of_le (fun m => norm_nonneg _)
    fun m => ?_
  have hσ := abs_sigM_le m
  have hn : ‖(sigM m : ℂ) * ((starRingEnd ℂ) (convS u m) * convS v m)‖
      = |sigM m| * (‖convS u m‖ * ‖convS v m‖) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, starRingEnd_apply,
      norm_star]
  rw [hn]
  nlinarith [sq_nonneg (‖convS u m‖ - ‖convS v m‖), norm_nonneg (convS u m),
    norm_nonneg (convS v m), abs_nonneg (6 * (m : ℝ) + 4), abs_nonneg (sigM m),
    mul_le_mul_of_nonneg_right hσ
      (mul_nonneg (norm_nonneg (convS u m)) (norm_nonneg (convS v m)))]

/-- Pointwise conjugation of a pairing summand. -/
lemma star_pair (σ : ℝ) (a b : ℂ) :
    star ((σ : ℂ) * ((starRingEnd ℂ) a * b))
      = (σ : ℂ) * ((starRingEnd ℂ) b * a) := by
  have h : star ((σ : ℂ) * ((starRingEnd ℂ) a * b))
      = (starRingEnd ℂ) ((σ : ℂ) * ((starRingEnd ℂ) a * b)) := rfl
  rw [h, map_mul, map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
  ring

/-- Hermitian symmetry of `B_s` (unconditional: conjugation commutes with
`tsum` because it is an isometry, including nonsummable inputs). -/
lemma Bform_conj_symm (s : ℝ) (u v : ℤ → ℂ) :
    Bform s v u = (starRingEnd ℂ) (Bform s u v) := by
  rw [Bform, Bform, starRingEnd_apply, star_add, star_mul', tsum_star, tsum_star]
  congr 1
  · exact tsum_congr fun n => (star_pair (sigP n) (u n) (v n)).symm
  · congr 1
    · simp [star_pow, Complex.conj_ofReal]
    · exact tsum_congr fun m => (star_pair (sigM m) (convS u m) (convS v m)).symm

/-- Additivity of `B_s` in the first slot, on the domain. -/
lemma Bform_add_left {s : ℝ} {u₁ u₂ v : ℤ → ℂ} (h₁ : MemDom u₁)
    (h₂ : MemDom u₂) (hv : MemDom v) :
    Bform s (u₁ + u₂) v = Bform s u₁ v + Bform s u₂ v := by
  have e₁ := (summable_pairP h₁.1 hv.1).tsum_add (summable_pairP h₂.1 hv.1)
  have e₂ := (summable_pairM h₁.2 hv.2).tsum_add (summable_pairM h₂.2 hv.2)
  have hA : (∑' n : ℤ, (sigP n : ℂ) * ((starRingEnd ℂ) ((u₁ + u₂) n) * v n))
      = (∑' n : ℤ, (sigP n : ℂ) * ((starRingEnd ℂ) (u₁ n) * v n))
        + ∑' n : ℤ, (sigP n : ℂ) * ((starRingEnd ℂ) (u₂ n) * v n) := by
    rw [← e₁]
    exact tsum_congr fun n => by
      simp only [Pi.add_apply, map_add]
      ring
  have hB : (∑' m : ℤ,
        (sigM m : ℂ) * ((starRingEnd ℂ) (convS (u₁ + u₂) m) * convS v m))
      = (∑' m : ℤ, (sigM m : ℂ) * ((starRingEnd ℂ) (convS u₁ m) * convS v m))
        + ∑' m : ℤ, (sigM m : ℂ) * ((starRingEnd ℂ) (convS u₂ m) * convS v m) := by
    rw [← e₂]
    exact tsum_congr fun m => by
      rw [convS_add (summable_normSq h₁.1) (summable_normSq h₂.1)]
      simp only [map_add]
      ring
  rw [Bform, Bform, Bform, hA, hB]
  ring

/-- Additivity of `B_s` in the second slot (from the first via Hermitian
symmetry). -/
lemma Bform_add_right {s : ℝ} {u v₁ v₂ : ℤ → ℂ} (hu : MemDom u)
    (h₁ : MemDom v₁) (h₂ : MemDom v₂) :
    Bform s u (v₁ + v₂) = Bform s u v₁ + Bform s u v₂ := by
  rw [Bform_conj_symm s (v₁ + v₂) u, Bform_add_left h₁ h₂ hu, map_add,
    ← Bform_conj_symm s v₁ u, ← Bform_conj_symm s v₂ u]

lemma convS_zero (m : ℤ) : convS (0 : ℤ → ℂ) m = 0 := by
  simp [convS]

lemma Qform_zero (s : ℝ) : Qform s (0 : ℤ → ℂ) = 0 := by
  simp [Qform, convS_zero]

/-- `V` is a `Q_s`-negative subspace: contained in the domain, with
`Q_s < 0` away from `0`. -/
def IsNegOn (s : ℝ) (V : Submodule ℂ (ℤ → ℂ)) : Prop :=
  V ≤ Dom ∧ ∀ u ∈ V, u ≠ 0 → Qform s u < 0

/-- `V` lies in the radical of `B_s`: contained in the domain and pairing
to `0` with every domain element. -/
def IsNullOn (s : ℝ) (V : Submodule ℂ (ℤ → ℂ)) : Prop :=
  V ≤ Dom ∧ ∀ u ∈ V, ∀ v : ℤ → ℂ, MemDom v → Bform s u v = 0

/-- The Morse index of `Q_s`: the supremum of `finrank` over
finite-dimensional `Q_s`-negative subspaces of the domain. -/
def ind (s : ℝ) : ℕ∞ :=
  ⨆ (V : Submodule ℂ (ℤ → ℂ)) (_ : IsNegOn s V) (_ : FiniteDimensional ℂ V),
    (Module.finrank ℂ V : ℕ∞)

/-- The nullity of `Q_s`: the supremum of `finrank` over
finite-dimensional subspaces of the radical of `B_s`. -/
def nul (s : ℝ) : ℕ∞ :=
  ⨆ (V : Submodule ℂ (ℤ → ℂ)) (_ : IsNullOn s V) (_ : FiniteDimensional ℂ V),
    (Module.finrank ℂ V : ℕ∞)

/-! ### The target theorems -/

/-- The head-coordinate mechanism: a finite-dimensional subspace of the
domain on which `Q_s` is nonpositive has dimension at most `1`.  If it
were `≥ 2`, the evaluation-at-the-head functional `u ↦ u 0` would have a
nonzero kernel element, contradicting `Qform_pos_of_head_zero`. -/
lemma finrank_le_one_of_nonpos {s : ℝ} {W : Submodule ℂ (ℤ → ℂ)}
    [FiniteDimensional ℂ W] (hle : W ≤ Dom)
    (hW : ∀ u ∈ W, Qform s u ≤ 0) : Module.finrank ℂ W ≤ 1 := by
  by_contra hc
  push Not at hc
  set φ : ↥W →ₗ[ℂ] ℂ :=
    (LinearMap.proj 0 : (ℤ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype with hφ
  have hrank := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank ℂ (LinearMap.range φ) ≤ 1 := by
    simpa [Module.finrank_self] using (LinearMap.range φ).finrank_le
  have hker : 1 ≤ Module.finrank ℂ (LinearMap.ker φ) := by omega
  have hne : LinearMap.ker φ ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker
    omega
  obtain ⟨x, hxmem, hxne⟩ := (Submodule.ne_bot_iff _).mp hne
  have hx0 : (x : ℤ → ℂ) 0 = 0 := by
    have h := LinearMap.mem_ker.mp hxmem
    simpa [hφ] using h
  have hcne : (x : ℤ → ℂ) ≠ 0 := by
    simpa using hxne
  obtain ⟨n, hn⟩ := Function.ne_iff.mp hcne
  have hpos := Qform_pos_of_head_zero (s := s) (mem_Dom.mp (hle x.2)) hx0
    ⟨n, by simpa using hn⟩
  have hnp := hW _ x.2
  linarith

/-- On the sum of a negative subspace and a radical subspace, `Q_s` is
nonpositive: the radical component drops out of the energy. -/
lemma qform_nonpos_on_sup {s : ℝ} {V₁ V₂ : Submodule ℂ (ℤ → ℂ)}
    (h₁ : IsNegOn s V₁) (h₂ : IsNullOn s V₂) :
    ∀ u ∈ V₁ ⊔ V₂, Qform s u ≤ 0 := by
  intro u hu
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
  have hd₁ : MemDom u₁ := h₁.1 hu₁
  have hd₂ : MemDom u₂ := h₂.1 hu₂
  have hnull := h₂.2 u₂ hu₂
  have h12 : Bform s u₁ u₂ = 0 := by
    rw [Bform_conj_symm s u₂ u₁, hnull u₁ hd₁, map_zero]
  have key : (Qform s (u₁ + u₂) : ℂ) = (Qform s u₁ : ℂ) := by
    rw [← Bform_self, ← Bform_self,
      Bform_add_left hd₁ hd₂ (memDom_add hd₁ hd₂),
      hnull _ (memDom_add hd₁ hd₂), add_zero,
      Bform_add_right hd₁ hd₁ hd₂, h12, add_zero]
  have keyR : Qform s (u₁ + u₂) = Qform s u₁ := by
    exact_mod_cast key
  rw [keyR]
  rcases eq_or_ne u₁ 0 with rfl | hne
  · exact le_of_eq (Qform_zero s)
  · exact le_of_lt (h₁.2 u₁ hu₁ hne)

/-- The joint bound at the finrank level: a negative subspace and a
radical subspace intersect trivially (a shared nonzero vector would have
`Q_s < 0` and `Q_s = 0` at once), so their dimensions add along the sum,
where `Q_s` is nonpositive. -/
lemma finrank_add_finrank_le_one {s : ℝ} {V₁ V₂ : Submodule ℂ (ℤ → ℂ)}
    (h₁ : IsNegOn s V₁) (h₂ : IsNullOn s V₂)
    [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂] :
    Module.finrank ℂ V₁ + Module.finrank ℂ V₂ ≤ 1 := by
  have hdisj : V₁ ⊓ V₂ = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu₁, hu₂⟩ := Submodule.mem_inf.mp hu
    rw [Submodule.mem_bot]
    by_contra hne
    have hneg := h₁.2 u hu₁ hne
    have h0 : Bform s u u = 0 := h₂.2 u hu₂ u (h₁.1 hu₁)
    have hcast : (Qform s u : ℂ) = 0 := by rw [← Bform_self, h0]
    have := Complex.ofReal_eq_zero.mp hcast
    linarith
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
  rw [hdisj, finrank_bot] at hsum
  have hW : Module.finrank ℂ ↥(V₁ ⊔ V₂) ≤ 1 :=
    finrank_le_one_of_nonpos (sup_le h₁.1 h₂.1) (qform_nonpos_on_sup h₁ h₂)
  omega

theorem ind_le_one (s : ℝ) : ind s ≤ 1 := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have := hfd
  have hnp : ∀ u ∈ V, Qform s u ≤ 0 := by
    intro u hu
    rcases eq_or_ne u 0 with rfl | hne
    · exact le_of_eq (Qform_zero s)
    · exact le_of_lt (hV.2 u hu hne)
  exact_mod_cast finrank_le_one_of_nonpos hV.1 hnp

theorem nul_le_one (s : ℝ) : nul s ≤ 1 := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have := hfd
  have hnp : ∀ u ∈ V, Qform s u ≤ 0 := by
    intro u hu
    have h0 : Bform s u u = 0 := hV.2 u hu u (hV.1 hu)
    have hcast : (Qform s u : ℂ) = 0 := by rw [← Bform_self, h0]
    exact le_of_eq (Complex.ofReal_eq_zero.mp hcast)
  exact_mod_cast finrank_le_one_of_nonpos hV.1 hnp

lemma exists_neg_of_ind_ne_zero {s : ℝ} (h : ind s ≠ 0) :
    ∃ V : Submodule ℂ (ℤ → ℂ), IsNegOn s V ∧ FiniteDimensional ℂ V ∧
      1 ≤ Module.finrank ℂ V := by
  by_contra hc
  push Not at hc
  apply h
  refine le_antisymm ?_ zero_le
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have := hc V hV hfd
  simp [Nat.lt_one_iff.mp this]

lemma exists_null_of_nul_ne_zero {s : ℝ} (h : nul s ≠ 0) :
    ∃ V : Submodule ℂ (ℤ → ℂ), IsNullOn s V ∧ FiniteDimensional ℂ V ∧
      1 ≤ Module.finrank ℂ V := by
  by_contra hc
  push Not at hc
  apply h
  refine le_antisymm ?_ zero_le
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have := hc V hV hfd
  simp [Nat.lt_one_iff.mp this]

/-- [ksindexi, `qop_ind_plus_nul_above`]: for every real `s` the index and
nullity of `Q_s` together do not exceed `1`.  Mechanism (the head
coordinate): any nonzero domain element vanishing at the head frequency `ℓ = 1`
has strictly positive energy (`Qform_pos_of_head_zero`), so no
2-dimensional subspace can be `Q_s`-nonpositive — and a negative
subspace plus a radical subspace is such a subspace. -/
theorem ind_add_nul_le_one (s : ℝ) : ind s + nul s ≤ 1 := by
  rcases eq_or_ne (ind s) 0 with h0 | h0
  · rw [h0, zero_add]
    exact nul_le_one s
  rcases eq_or_ne (nul s) 0 with h1 | h1
  · rw [h1, add_zero]
    exact ind_le_one s
  exfalso
  obtain ⟨V₁, hV₁, hfd₁, hr₁⟩ := exists_neg_of_ind_ne_zero h0
  obtain ⟨V₂, hV₂, hfd₂, hr₂⟩ := exists_null_of_nul_ne_zero h1
  have := hfd₁
  have := hfd₂
  have := finrank_add_finrank_le_one hV₁ hV₂
  omega

/-! ### Scaling, positivity, and the variational radical argument -/

lemma normSq_zero : normSq (0 : ℤ → ℂ) = 0 := by
  simp [normSq]

lemma normSq_smul (c : ℂ) (u : ℤ → ℂ) :
    normSq (c • u) = ‖c‖ ^ 2 * normSq u :=
  GammaOne.normSq_smul' c u

lemma Qform_smul (s : ℝ) (c : ℂ) (u : ℤ → ℂ) :
    Qform s (c • u) = ‖c‖ ^ 2 * Qform s u :=
  GammaOne.Qform_smul' s c u

lemma Bform_smul_right (s : ℝ) (c : ℂ) (u v : ℤ → ℂ) :
    Bform s u (c • v) = c * Bform s u v := by
  rw [Bform, Bform]
  have h1 : (∑' n : ℤ, (sigP n : ℂ) * ((starRingEnd ℂ) (u n) * (c • v) n))
      = c * ∑' n : ℤ, (sigP n : ℂ) * ((starRingEnd ℂ) (u n) * v n) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  have h2 : (∑' m : ℤ,
        (sigM m : ℂ) * ((starRingEnd ℂ) (convS u m) * convS (c • v) m))
      = c * ∑' m : ℤ, (sigM m : ℂ) * ((starRingEnd ℂ) (convS u m) * convS v m) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun m => by
      rw [convS_smul]
      ring
  rw [h1, h2]
  ring

lemma Bform_smul_left (s : ℝ) (c : ℂ) (u v : ℤ → ℂ) :
    Bform s (c • u) v = (starRingEnd ℂ) c * Bform s u v := by
  rw [Bform, Bform]
  have h1 : (∑' n : ℤ, (sigP n : ℂ) * ((starRingEnd ℂ) ((c • u) n) * v n))
      = (starRingEnd ℂ) c
        * ∑' n : ℤ, (sigP n : ℂ) * ((starRingEnd ℂ) (u n) * v n) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      ring
  have h2 : (∑' m : ℤ,
        (sigM m : ℂ) * ((starRingEnd ℂ) (convS (c • u) m) * convS v m))
      = (starRingEnd ℂ) c
        * ∑' m : ℤ, (sigM m : ℂ) * ((starRingEnd ℂ) (convS u m) * convS v m) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun m => by
      rw [convS_smul]
      simp only [map_mul]
      ring
  rw [h1, h2]
  ring

lemma normSq_pos {u : ℤ → ℂ} (hu : MemDom u) (hne : u ≠ 0) : 0 < normSq u := by
  obtain ⟨n, hn⟩ := Function.ne_iff.mp hne
  have hsum := summable_normSq hu.1
  have hle : ‖u n‖ ^ 2 ≤ normSq u := hsum.le_tsum n fun m _ => sq_nonneg _
  have hpos : 0 < ‖u n‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (by simpa using hn)) 2
  linarith

lemma normSq_nonneg (u : ℤ → ℂ) : 0 ≤ normSq u :=
  tsum_nonneg fun _ => sq_nonneg _

/-- Homogeneous form of the eigenvalue bound: `γ(s)·‖u‖² ≤ Q_s(u)` on the
whole domain. -/
lemma gam_mul_normSq_le {s : ℝ} {u : ℤ → ℂ} (hu : MemDom u) :
    gam s * normSq u ≤ Qform s u := by
  rcases eq_or_ne u 0 with rfl | hne
  · rw [normSq_zero, Qform_zero, mul_zero]
  · have hpos : 0 < normSq u := normSq_pos hu hne
    set c : ℂ := (((Real.sqrt (normSq u))⁻¹ : ℝ) : ℂ) with hc
    have hc2 : ‖c‖ ^ 2 = (normSq u)⁻¹ := by
      rw [hc, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
        Real.sq_sqrt hpos.le]
    have hn1 : normSq (c • u) = 1 := by
      rw [normSq_smul, hc2, inv_mul_cancel₀ hpos.ne']
    have h := gam_le (s := s) (memDom_smul c hu) hn1
    rw [Qform_smul, hc2] at h
    have h2 := mul_le_mul_of_nonneg_right h hpos.le
    calc gam s * normSq u ≤ (normSq u)⁻¹ * Qform s u * normSq u := h2
      _ = Qform s u := by field_simp

/-- The discriminant trick: if `0 ≤ 2ta + t²b` for every real `t`, with
`b ≥ 0`, then `a = 0` (witness `t = -a/(b+1)`). -/
lemma discriminant_aux {a b : ℝ} (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b) : a = 0 := by
  by_contra ha
  have ha2 : 0 < a ^ 2 := by positivity
  have hb1 : (0 : ℝ) < b + 1 := by linarith
  have h2 := h (-(a / (b + 1)))
  have key : 2 * (-(a / (b + 1))) * a + (-(a / (b + 1))) ^ 2 * b
      = -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
    field_simp
    ring
  rw [key, neg_div] at h2
  have hlt : 0 < a ^ 2 * (b + 2) / (b + 1) ^ 2 :=
    div_pos (by nlinarith) (by positivity)
  linarith

/-- Expansion of the energy of a sum via the polarized form. -/
lemma Qform_add_expand {s : ℝ} {u w : ℤ → ℂ} (hu : MemDom u)
    (hw : MemDom w) :
    (Qform s (u + w) : ℂ) = (Qform s u : ℂ) + Bform s u w
      + (starRingEnd ℂ) (Bform s u w) + (Qform s w : ℂ) := by
  rw [← Bform_self, Bform_add_left hu hw (memDom_add hu hw),
    Bform_add_right hu hu hw, Bform_add_right hw hu hw,
    Bform_conj_symm s u w, Bform_self, Bform_self]
  ring

/-- The variational Euler–Lagrange argument, with no operator anywhere:
a zero-energy vector of a globally nonnegative `Q_s` lies in the radical
of `B_s`.  Real part by the discriminant trick on `Q(u + tv) ≥ 0`,
imaginary part by replacing `v` with `iv`. -/
lemma bform_eq_zero_of_min {s : ℝ} {u : ℤ → ℂ} (hu : MemDom u)
    (hQ0 : Qform s u = 0) (hpos : ∀ w, MemDom w → 0 ≤ Qform s w) :
    ∀ v, MemDom v → Bform s u v = 0 := by
  have hre : ∀ v, MemDom v → (Bform s u v).re = 0 := by
    intro v hv
    refine discriminant_aux (hpos v hv) fun t => ?_
    have hmemtv : MemDom ((t : ℂ) • v) := memDom_smul _ hv
    have hexp := Qform_add_expand hu hmemtv (s := s)
    rw [Bform_smul_right, Qform_smul, hQ0] at hexp
    have hnt : ‖((t : ℝ) : ℂ)‖ ^ 2 = t ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hnt] at hexp
    have hreal := congrArg Complex.re hexp
    simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re,
      Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add] at hreal
    have hkey := hpos _ (memDom_add hu hmemtv)
    rw [hreal] at hkey
    linarith
  intro v hv
  have h1 := hre v hv
  have h2 := hre (Complex.I • v) (memDom_smul _ hv)
  rw [Bform_smul_right] at h2
  have him : (Bform s u v).im = 0 := by
    simpa [Complex.mul_re] using h2
  exact Complex.ext (by simpa using h1) (by simpa using him)

/-- Sign dictionary, negative side: the index is `1` exactly when the
least-eigenvalue function is negative (the minimizer of
`exists_minimizer` spans a negative line; conversely a negative vector
forces `gam s < 0`). -/
theorem ind_eq_one_iff {s : ℝ} (hs : 0 < s) : ind s = 1 ↔ gam s < 0 := by
  constructor
  · intro h
    obtain ⟨V, hV, hfd, hr⟩ := exists_neg_of_ind_ne_zero (by rw [h]; simp)
    have := hfd
    have hVne : V ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hr
      omega
    obtain ⟨u, huV, hune⟩ := (Submodule.ne_bot_iff V).mp hVne
    have hmem : MemDom u := hV.1 huV
    have hneg : Qform s u < 0 := hV.2 u huV hune
    by_contra hge
    push Not at hge
    have h1 := gam_mul_normSq_le hmem (s := s)
    have h2 : 0 ≤ gam s * normSq u := mul_nonneg hge (normSq_nonneg u)
    linarith
  · intro hneg
    obtain ⟨u, hmem, hn1, hQ⟩ := exists_minimizer hs
    have hune : u ≠ 0 := by
      intro h
      rw [h, normSq_zero] at hn1
      norm_num at hn1
    have hVneg : IsNegOn s (ℂ ∙ u) := by
      refine ⟨(Submodule.span_singleton_le_iff_mem u Dom).mpr hmem, ?_⟩
      intro w hw hwne
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have hcne : c ≠ 0 := by
        intro h
        rw [h, zero_smul] at hwne
        exact hwne rfl
      rw [Qform_smul, hQ]
      exact mul_neg_of_pos_of_neg (by positivity) hneg
    have hfd : FiniteDimensional ℂ ↥(ℂ ∙ u) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_singleton u)
    have h1 : (1 : ℕ∞) ≤ ind s := by
      have hfr : Module.finrank ℂ ↥(ℂ ∙ u) = 1 := finrank_span_singleton hune
      calc (1 : ℕ∞) = (Module.finrank ℂ ↥(ℂ ∙ u) : ℕ∞) := by simp [hfr]
        _ ≤ ind s :=
          le_iSup_of_le (ℂ ∙ u) (le_iSup_of_le hVneg (le_iSup_of_le hfd le_rfl))
    exact le_antisymm (ind_le_one s) h1

/-- Sign dictionary, null side: the nullity is `1` exactly at
`gam s = 0` (the minimizer is then a global minimum of `Q_s` on the
domain, hence lies in the radical by the variational argument). -/
theorem nul_eq_one_iff {s : ℝ} (hs : 0 < s) : nul s = 1 ↔ gam s = 0 := by
  constructor
  · intro h
    obtain ⟨V, hV, hfd, hr⟩ := exists_null_of_nul_ne_zero (by rw [h]; simp)
    have := hfd
    have hVne : V ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hr
      omega
    obtain ⟨u, huV, hune⟩ := (Submodule.ne_bot_iff V).mp hVne
    have hmem : MemDom u := hV.1 huV
    have hQ0 : Qform s u = 0 := by
      have h0 : Bform s u u = 0 := hV.2 u huV u hmem
      have : (Qform s u : ℂ) = 0 := by rw [← Bform_self, h0]
      exact Complex.ofReal_eq_zero.mp this
    have hle : gam s ≤ 0 := by
      by_contra hgt
      push Not at hgt
      have h1 := gam_mul_normSq_le hmem (s := s)
      have h2 : 0 < gam s * normSq u :=
        mul_pos hgt (normSq_pos hmem hune)
      linarith
    have hge : 0 ≤ gam s := by
      by_contra hlt
      push Not at hlt
      have hind : ind s = 1 := (ind_eq_one_iff hs).mpr hlt
      have hsum := ind_add_nul_le_one s
      rw [hind, h] at hsum
      norm_num at hsum
    linarith
  · intro hgam
    obtain ⟨u, hmem, hn1, hQ⟩ := exists_minimizer hs
    rw [hgam] at hQ
    have hune : u ≠ 0 := by
      intro h
      rw [h, normSq_zero] at hn1
      norm_num at hn1
    have hpos : ∀ w, MemDom w → 0 ≤ Qform s w := by
      intro w hw
      have := gam_mul_normSq_le hw (s := s)
      rw [hgam, zero_mul] at this
      exact this
    have hrad := bform_eq_zero_of_min hmem hQ hpos
    have hVnull : IsNullOn s (ℂ ∙ u) := by
      refine ⟨(Submodule.span_singleton_le_iff_mem u Dom).mpr hmem, ?_⟩
      intro w hw v hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [Bform_smul_left, hrad v hv, mul_zero]
    have hfd : FiniteDimensional ℂ ↥(ℂ ∙ u) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_singleton u)
    have h1 : (1 : ℕ∞) ≤ nul s := by
      have hfr : Module.finrank ℂ ↥(ℂ ∙ u) = 1 := finrank_span_singleton hune
      calc (1 : ℕ∞) = (Module.finrank ℂ ↥(ℂ ∙ u) : ℕ∞) := by simp [hfr]
        _ ≤ nul s :=
          le_iSup_of_le (ℂ ∙ u) (le_iSup_of_le hVnull (le_iSup_of_le hfd le_rfl))
    exact le_antisymm (nul_le_one s) h1

/-- The single-crossing package: a threshold `s* ∈ (1, √3)` where `γ`
vanishes, with `γ < 0` for positive parameters strictly below it and
`γ > 0` strictly above it.
Combines the intermediate value theorem with `gam_continuousOn` (CircleQ),
`gam_strictMonoOn` and `gam_sqrt_three_pos` (Threshold), and `gam_one_neg`
(GammaOne). -/
theorem exists_threshold :
    ∃ sstar : ℝ, sstar ∈ Ioo 1 (Real.sqrt 3) ∧ gam sstar = 0 ∧
      (∀ s : ℝ, 0 < s → s < sstar → gam s < 0) ∧
      (∀ s : ℝ, sstar < s → 0 < gam s) := by
  have h13 : (1 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hsub : Icc (1 : ℝ) (Real.sqrt 3) ⊆ Ioi 0 :=
    fun x hx => lt_of_lt_of_le one_pos hx.1
  have hcont : ContinuousOn gam (Icc (1 : ℝ) (Real.sqrt 3)) :=
    gam_continuousOn.mono hsub
  have hivt := intermediate_value_Ioo (le_of_lt h13) hcont
  have h0mem : (0 : ℝ) ∈ Ioo (gam 1) (gam (Real.sqrt 3)) :=
    ⟨gam_one_neg, gam_sqrt_three_pos⟩
  obtain ⟨sstar, hmem, hval⟩ := hivt h0mem
  refine ⟨sstar, hmem, hval, ?_, ?_⟩
  · intro s hs hlt
    have h := gam_strictMonoOn (mem_Ioi.mpr hs)
      (mem_Ioi.mpr (lt_trans one_pos hmem.1)) hlt
    rwa [hval] at h
  · intro s hlt
    have hsstar_pos : (0 : ℝ) < sstar := lt_trans one_pos hmem.1
    have h := gam_strictMonoOn (mem_Ioi.mpr hsstar_pos)
      (mem_Ioi.mpr (lt_trans hsstar_pos hlt)) hlt
    rwa [hval] at h

/-- Circle-level classification ([ksindexi] Section 4, `k = 3`): there is a
single threshold `s* ∈ (1, √3)` such that for every `s > 0` the form
`Q_s` has index `1` below the threshold and `0` at and above it, and
nullity `1` exactly at the threshold.  Reduces to `exists_threshold`
plus the sign dictionary plus `ind_add_nul_le_one`. -/
theorem circle_main :
    ∃ sstar : ℝ, sstar ∈ Ioo 1 (Real.sqrt 3) ∧ ∀ s : ℝ, 0 < s →
      ind s = (if s < sstar then 1 else 0) ∧
      nul s = (if s = sstar then 1 else 0) := by
  obtain ⟨sstar, hmem, hval, hbelow, habove⟩ := exists_threshold
  refine ⟨sstar, hmem, fun s hs => ⟨?_, ?_⟩⟩
  · by_cases hlt : s < sstar
    · rw [if_pos hlt]
      exact (ind_eq_one_iff hs).mpr (hbelow s hs hlt)
    · rw [if_neg hlt]
      push Not at hlt
      have hnneg : ¬ gam s < 0 := by
        rcases eq_or_lt_of_le hlt with heq | hgt
        · rw [← heq, hval]
          exact lt_irrefl 0
        · exact asymm (habove s hgt)
      have hne1 : ind s ≠ 1 := fun h => hnneg ((ind_eq_one_iff hs).mp h)
      exact Order.lt_one_iff.mp (lt_of_le_of_ne (ind_le_one s) hne1)
  · by_cases heq : s = sstar
    · rw [if_pos heq, heq]
      exact (nul_eq_one_iff (lt_trans one_pos hmem.1)).mpr hval
    · rw [if_neg heq]
      have hne0 : gam s ≠ 0 := by
        rcases lt_trichotomy s sstar with hlt | heq' | hgt
        · exact ne_of_lt (hbelow s hs hlt)
        · exact absurd heq' heq
        · exact ne_of_gt (habove s hgt)
      have hne1 : nul s ≠ 1 := fun h => hne0 ((nul_eq_one_iff hs).mp h)
      exact Order.lt_one_iff.mp (lt_of_le_of_ne (nul_le_one s) hne1)

end KsIndex.Statements
