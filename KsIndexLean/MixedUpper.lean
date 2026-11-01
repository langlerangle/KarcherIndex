module

/-
# Boundary-trace estimates for the mixed upper bound

This file constructs the complex-linear map `traceFull` from a natural
class-`r` disk domain to sequences indexed by `ℤ`, using boundary modes
`kn + (k-r)`. For `k ≥ 3` and `r < k`, zero full trace implies nonnegative
disk energy. For `1 ≤ r ≤ k-1`, negative mixed disk energy implies negative
transported circle energy, and the transported trace has finite
`H^{1/2}` coefficient weight.

The domination proof compares each radial mode integral with its DtN
boundary term, proves summability, and reindexes the surviving class
lattice. These estimates supply inputs to `FormIndex.formIndex_le_of_negMap`.
The arc-support condition and final mixed-count assembly are supplied in
`TraceArc.lean`; this file does not itself prove the final count.
-/
public import KsIndexLean.SeamUpper
public import KsIndexLean.SymbolReindex
public import KsIndexLean.ArcMain

@[expose] public section


noncomputable section

namespace KsIndex.MixedUpper

open Complex Real MeasureTheory intervalIntegral Set Filter Topology
open KsIndex.Parseval KsIndex.FourierMode KsIndex.Radial KsIndex.Surface KsIndex.SurfaceForm
  KsIndex.SingleDiskBridge KsIndex.SingleDisk KsIndex.FormIndex KsIndex.PiAssembly
  KsIndex.SeamUpper KsIndex.PolarAssembly KsIndex.ArcForm KsIndex.ArcLower KsIndex.ArcSpace
  KsIndex.Reindex KsIndex.ArcMain KsIndex.ArcEstimate
open scoped ContDiff

variable {k : ℕ}

/-! ### The full ℤ-indexed class-`r` boundary-trace map -/

/-- **The full class-`r` boundary-trace map**, `ℤ`-indexed: `u ↦ (n ↦ Fm (ext u) (kn+(k−r)) 1)`.
For `1 ≤ r ≤ k-1`, nonzero boundary modes of a class-`r` function can occur only
when `ℓ ≡ −r (mod k)`
(`Fm_eq_zero_of_class`: `k ∣ r + ℓ`), i.e. `ℓ = kn + (k−r)` with residue `k−r ∈ {1,…,k−1}` — this
lattice matches `SymbolReindex.sigma_natAbs_eq` (with its residue argument `k−r`), giving the
circle problem `j = r`.  This is `SeamUpper.traceMap`'s mechanism (boundary trace = interior limit
of the linear modes, so `ℂ`-linear via `Fm_tendsto_ext` + `tendsto_nhds_unique`) with the finite
head set replaced by the full class lattice — the codomain the circle model `ArcDom` lives in. -/
def traceFull {b₁ b₀ : Bool} (hk : 1 ≤ k) (r : ℕ) :
    ↥(NatCc k b₁ b₀ ⊓ Erot1 k r) →ₗ[ℂ] (ℤ → ℂ) where
  toFun u := fun n => Fm (extChoice hk u) ((k : ℤ) * n + ((k - r : ℕ) : ℤ)) 1
  map_add' u v := by
    funext n
    have : (𝓝[<] (1 : ℝ)).NeBot := inferInstance
    simp only [Pi.add_apply]
    refine tendsto_nhds_unique (Fm_tendsto_ext hk (u + v) ((k : ℤ) * n + ((k - r : ℕ) : ℤ))) ?_
    have hu : (u : ℂ → ℂ) ∈ NatCc k b₁ b₀ := (Submodule.mem_inf.mp u.2).1
    have hv : (v : ℂ → ℂ) ∈ NatCc k b₁ b₀ := (Submodule.mem_inf.mp v.2).1
    have hev : Fm ((u + v : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) : ℂ → ℂ) ((k : ℤ) * n + ((k - r : ℕ) : ℤ))
        =ᶠ[𝓝[<] (1 : ℝ)] (fun s => Fm (u : ℂ → ℂ) ((k : ℤ) * n + ((k - r : ℕ) : ℤ)) s
          + Fm (v : ℂ → ℂ) ((k : ℤ) * n + ((k - r : ℕ) : ℤ)) s) := by
      filter_upwards [Ioo_mem_nhds_lt] with s hs
      rw [Submodule.coe_add]
      exact Fm_add_of ((k : ℤ) * n + ((k - r : ℕ) : ℤ))
        (slice_continuous (mem_NatCc.mp hu).1.continuousOn hs.1.le hs.2)
        (slice_continuous (mem_NatCc.mp hv).1.continuousOn hs.1.le hs.2)
    exact (Tendsto.add (Fm_tendsto_ext hk u ((k : ℤ) * n + ((k - r : ℕ) : ℤ)))
      (Fm_tendsto_ext hk v ((k : ℤ) * n + ((k - r : ℕ) : ℤ)))).congr' hev.symm
  map_smul' c u := by
    funext n
    have : (𝓝[<] (1 : ℝ)).NeBot := inferInstance
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    refine tendsto_nhds_unique (Fm_tendsto_ext hk (c • u) ((k : ℤ) * n + ((k - r : ℕ) : ℤ))) ?_
    set d : ℤ := (k : ℤ) * n + ((k - r : ℕ) : ℤ) with hd
    have hfun : Fm ((c • u : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) : ℂ → ℂ) d
        = fun s => c * Fm (u : ℂ → ℂ) d s := by
      funext s; rw [Submodule.coe_smul]
      exact Fm_smul_of c (u : ℂ → ℂ) ((k : ℤ) * n + ((k - r : ℕ) : ℤ)) s
    rw [hfun]
    exact (Fm_tendsto_ext hk u ((k : ℤ) * n + ((k - r : ℕ) : ℤ))).const_mul c

/-- The value of `traceFull` at index `n` is the boundary trace at mode `kn + (k−r)`. -/
@[simp] lemma traceFull_apply {b₁ b₀ : Bool} (hk : 1 ≤ k) (r : ℕ)
    (u : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) (n : ℤ) :
    traceFull hk r u n = Fm (extChoice hk u) ((k : ℤ) * n + ((k - r : ℕ) : ℤ)) 1 := rfl

/-! ### Nonnegative energy for zero trace -/

/-- **Zero-trace ⟹ nonnegative energy** (`k ≥ 3`, `r < k`).  If a class-`r` natural test function
has vanishing full boundary trace, then in particular every head-set trace vanishes, so every
angular-mode radial form is nonnegative (`modeTerm_nonneg`; off-class modes vanish by class
selection), and its disk energy is `≥ 0`.  This is the `hker` input to `formIndex_le_of_negMap`. -/
lemma qd_nonneg_of_traceFull_zero {b₁ b₀ : Bool} (hk : 3 ≤ k) (hk1 : 1 ≤ k) {r : ℕ} (hr : r < k)
    (u : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) (hT0 : traceFull hk1 r u = 0) :
    0 ≤ Qd k (u : ℂ → ℂ) := by
  have hk2 : 2 ≤ k := by omega
  set f := (u : ℂ → ℂ) with hfdef
  have hfE : f ∈ Erot1 k r := (Submodule.mem_inf.mp u.2).2
  have hG : ContDiff ℝ 1 (extChoice hk1 u) := extChoice_contDiff hk1 u
  have hGeq : ∀ w ∈ disk, f w = extChoice hk1 u w := extChoice_eqOn hk1 u
  -- the full trace vanishing kills every head-set trace: each `ℓ ≡ k−r (mod k)` is `k(m−1)+(k−r)`
  have htrace : ∀ ℓ : ℤ, ℓ ∈ headSet k r → Fm (extChoice hk1 u) ℓ 1 = 0 := by
    intro ℓ hℓ
    obtain ⟨_, hdvd, _⟩ := mem_headSet.mp hℓ
    obtain ⟨m, hm⟩ := hdvd
    have hℓeq : ℓ = (k : ℤ) * (m - 1) + ((k - r : ℕ) : ℤ) := by
      rw [Nat.cast_sub hr.le]
      have hkm : (k : ℤ) * (m - 1) = (k : ℤ) * m - (k : ℤ) := by ring
      rw [hkm]; linarith [hm]
    have hval := congrFun hT0 (m - 1)
    rw [traceFull_apply] at hval
    rw [hℓeq]; exact hval
  have hQ : Qd k f = 2 * π * ∑' ℓ : ℤ,
      ∫ s in (0 : ℝ)..1,
        lhsC k ℓ.natAbs (Fm (extChoice hk1 u) ℓ) (FmD (extChoice hk1 u) ℓ) s := by
    rw [Qd_congr_disk hGeq, Qd_eq_tsum hG hk2]
  rw [hfdef, hQ]
  refine mul_nonneg (by positivity) (tsum_nonneg fun ℓ => ?_)
  exact modeTerm_nonneg hk hG hGeq hfE htrace ℓ

/-! ### DtN domination -/

/-- **Termwise DtN domination.**  Each mode integral dominates the DtN symbol times the boundary
trace squared.  For `ℓ ≠ 0` this is `qMode_ge_complex`; for `ℓ = 0` the trace vanishes off-class
(`r0 ≠ 0`) so the left side is `0` and `qMode_zero_nonneg_complex` closes it. -/
lemma sigma_trace_sq_le_modeTerm (hk : 2 ≤ k) {G f : ℂ → ℂ} (hG : ContDiff ℝ 1 G)
    (hGeq : ∀ w ∈ disk, f w = G w) {r0 : ℕ} (hf : f ∈ Erot1 k r0)
    (hr0pos : 0 < r0) (hr0lt : r0 < k) (ℓ : ℤ) :
    sigma k ℓ.natAbs * ‖Fm G ℓ 1‖ ^ 2
      ≤ ∫ s in (0 : ℝ)..1, lhsC k ℓ.natAbs (Fm G ℓ) (FmD G ℓ) s := by
  have hk0 : 0 < k := by omega
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (Fm G ℓ) (FmD G ℓ s) s :=
    fun s _ => Fm_hasDerivAt hG ℓ s
  have hcont' : ContinuousOn (FmD G ℓ) (Set.Icc 0 1) := (FmD_continuous hG ℓ).continuousOn
  rcases eq_or_ne ℓ 0 with hℓ0 | hℓ0
  · subst hℓ0
    have htr0 : Fm G 0 1 = 0 := Fm_ext_boundary_zero hG hGeq hf hk0 (by
      rw [add_zero]; intro hd; rw [Int.natCast_dvd_natCast] at hd
      exact absurd hd (Nat.not_dvd_of_pos_of_lt hr0pos hr0lt))
    have hz : sigma k (0 : ℤ).natAbs * ‖Fm G 0 1‖ ^ 2 = 0 := by rw [htr0]; simp
    rw [hz]; simpa using qMode_zero_nonneg_complex hk hderiv hcont' htr0
  · exact qMode_ge_complex hk (Int.natAbs_pos.mpr hℓ0) hderiv hcont' (Fm_zero_of_ne G hℓ0)

/-- **The DtN-weighted trace sequence is summable.**  Split at the symbol sign change `κ = k−1`:
the tail (`|ℓ| ≥ k−1`, `σ ≥ 0`, `0 ≤ σ‖t‖² ≤ modeTerm`) is dominated by the summable mode sum, and
the head (`|ℓ| < k−1`) is a finite set. -/
lemma sigma_trace_sq_summable (hk : 2 ≤ k) {G f : ℂ → ℂ} (hG : ContDiff ℝ 1 G)
    (hGeq : ∀ w ∈ disk, f w = G w) {r0 : ℕ} (hf : f ∈ Erot1 k r0)
    (hr0pos : 0 < r0) (hr0lt : r0 < k) :
    Summable (fun ℓ : ℤ => sigma k ℓ.natAbs * ‖Fm G ℓ 1‖ ^ 2) := by
  have hk1 : 1 ≤ k := by omega
  have hMsum := modeTerm_summable hG hk
  set M : ℤ → ℝ := fun ℓ => ∫ s in (0 : ℝ)..1, lhsC k ℓ.natAbs (Fm G ℓ) (FmD G ℓ) s with hMdef
  set g : ℤ → ℝ := fun ℓ => sigma k ℓ.natAbs * ‖Fm G ℓ 1‖ ^ 2 with hgdef
  have hMpos : Summable (fun ℓ => M ℓ ⊔ 0) := by
    have hMabs : Summable (fun ℓ => |M ℓ|) := summable_abs_iff.mpr hMsum
    exact hMabs.of_nonneg_of_le (fun ℓ => le_max_right _ _)
      (fun ℓ => max_le (le_abs_self _) (abs_nonneg _))
  have hg2 : Summable (fun ℓ => if k - 1 ≤ ℓ.natAbs then g ℓ else 0) := by
    refine hMpos.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_)
    · split_ifs with h
      · exact mul_nonneg (sigma_nonneg hk1 h) (sq_nonneg _)
      · exact le_refl 0
    · split_ifs with h
      · exact le_trans (sigma_trace_sq_le_modeTerm hk hG hGeq hf hr0pos hr0lt ℓ) (le_max_left _ _)
      · exact le_max_right _ _
  have hg1 : Summable (fun ℓ => if k - 1 ≤ ℓ.natAbs then (0 : ℝ) else g ℓ) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc (-(k : ℤ)) (k : ℤ)) (fun ℓ hℓ => ?_)
    have hcond : k - 1 ≤ ℓ.natAbs := by rw [Finset.mem_Icc] at hℓ; omega
    rw [if_pos hcond]
  exact (hg1.add hg2).congr (fun ℓ => by split_ifs <;> simp)

/-- **The DtN domination as `hneg`.**  On a class-`r` (`1 ≤ r ≤ k−1`) mixed test function with
negative disk energy, the transported circle form is negative: `Qd u = 2π ∑ modeTerm ≥
2π ∑ σ‖t‖² = 2πk·NQformArc(aOf r k)(bOf k)(traceFull u)`.  The `∑ σ‖t‖²` reindexes onto the class
lattice `ℓ = kn+(k−r)` (off-class traces vanish; `sigma_natAbs_eq` at residue `k−r`). -/
lemma NQformArc_neg_of_Qd_neg (hk : 3 ≤ k) (hk1 : 1 ≤ k) {r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k - 1)
    (u : ↥(NatCc k true false ⊓ Erot1 k r)) (hQ : Qd k (u : ℂ → ℂ) < 0) :
    NQformArc (aOf r k) (bOf k) (traceFull hk1 r u) < 0 := by
  have hk2 : 2 ≤ k := by omega
  have hr0pos : 0 < r := by omega
  have hr0lt : r < k := by omega
  have hfE : (u : ℂ → ℂ) ∈ Erot1 k r := (Submodule.mem_inf.mp u.2).2
  have hG : ContDiff ℝ 1 (extChoice hk1 u) := extChoice_contDiff hk1 u
  have hGeq : ∀ w ∈ disk, (u : ℂ → ℂ) w = extChoice hk1 u w := extChoice_eqOn hk1 u
  set G := extChoice hk1 u with hGdef
  -- Qd u = 2π ∑ modeTerm
  have hQdeq : Qd k (u : ℂ → ℂ) = 2 * π * ∑' ℓ : ℤ,
      ∫ s in (0 : ℝ)..1, lhsC k ℓ.natAbs (Fm G ℓ) (FmD G ℓ) s := by
    rw [Qd_congr_disk hGeq, Qd_eq_tsum hG hk2]
  -- ∑ σ‖t‖² ≤ ∑ modeTerm
  have hle : (∑' ℓ : ℤ, sigma k ℓ.natAbs * ‖Fm G ℓ 1‖ ^ 2)
      ≤ ∑' ℓ : ℤ, ∫ s in (0 : ℝ)..1, lhsC k ℓ.natAbs (Fm G ℓ) (FmD G ℓ) s :=
    (sigma_trace_sq_summable hk2 hG hGeq hfE hr0pos hr0lt).tsum_le_tsum
      (fun ℓ => sigma_trace_sq_le_modeTerm hk2 hG hGeq hfE hr0pos hr0lt ℓ)
      (modeTerm_summable hG hk2)
  -- reindex ∑ σ‖t‖² = k · NQformArc
  have hφinj : Function.Injective (fun n : ℤ => (k : ℤ) * n + ((k - r : ℕ) : ℤ)) := by
    intro a b h
    have hkab : (k : ℤ) * a = (k : ℤ) * b := by simp only at h; exact add_right_cancel h
    exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr (by omega)) hkab
  have hoff : ∀ ℓ ∉ Set.range (fun n : ℤ => (k : ℤ) * n + ((k - r : ℕ) : ℤ)),
      sigma k ℓ.natAbs * ‖Fm G ℓ 1‖ ^ 2 = 0 := by
    intro ℓ hℓ
    have hnd : ¬ (k : ℤ) ∣ ((r : ℤ) + ℓ) := by
      intro hd; obtain ⟨m, hm⟩ := hd; apply hℓ
      refine ⟨m - 1, ?_⟩
      simp only
      rw [Nat.cast_sub (by omega : r ≤ k)]
      have hkm1 : (k : ℤ) * (m - 1) = (k : ℤ) * m - (k : ℤ) := by ring
      omega
    rw [Fm_ext_boundary_zero hG hGeq hfE (by omega) hnd]; simp
  have hreindex : (∑' ℓ : ℤ, sigma k ℓ.natAbs * ‖Fm G ℓ 1‖ ^ 2)
      = (k : ℝ) * NQformArc (aOf r k) (bOf k) (traceFull hk1 r u) := by
    rw [← Function.Injective.tsum_eq hφinj (Function.support_subset_iff'.mpr hoff), NQformArc,
      ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    have hσ : sigma k ((k : ℤ) * n + ((k - r : ℕ) : ℤ)).natAbs
        = (k : ℝ) * sigmaArc (aOf r k) (bOf k) n := by
      have h := sigma_natAbs_eq (r := k - r) hk1 (by omega) (by omega) n
      rwa [show k - (k - r) = r from by omega] at h
    rw [hσ, show Fm G ((k : ℤ) * n + ((k - r : ℕ) : ℤ)) 1 = traceFull hk1 r u n from by
      rw [traceFull_apply, hGdef]]
    ring
  -- combine
  have hchain : 2 * π * ((k : ℝ) * NQformArc (aOf r k) (bOf k) (traceFull hk1 r u))
      ≤ Qd k (u : ℂ → ℂ) := by
    rw [hQdeq, ← hreindex]; exact mul_le_mul_of_nonneg_left hle (by positivity)
  by_contra hcon
  rw [not_lt] at hcon
  have hnn : 0 ≤ 2 * π * ((k : ℝ) * NQformArc (aOf r k) (bOf k) (traceFull hk1 r u)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) hcon)
  linarith [hchain, hQ]

/-! ### The `H^{1/2}` weight summability of the trace -/

/-- **The transported trace has finite `H^{1/2}` weight.**  The first half of `MemArc`: the class
lattice carries the DtN-weighted energy `∑ σ_{(a;k)}(n)‖t_n‖² < ∞` (reindex of `sigma_trace_sq_summable`
at residue `k−r`), and the arc symbol grows linearly (`sigmaArc_ge_inf`: `σ ≥ |n+a| − 1/|n+a|`), so
`(1+|n|) ≤ 4·σ` off the finite head `{−2,−1,0,1}`.  Comparing against `4|σ|‖t_n‖²` plus a
finitely-supported head correction gives `∑ (1+|n|)‖t_n‖² < ∞` — the reverse of
`summable_sigmaArc_mul_sq`. -/
lemma traceFull_weight_summable (hk : 3 ≤ k) (hk1 : 1 ≤ k) {r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k - 1)
    (u : ↥(NatCc k true false ⊓ Erot1 k r)) :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) * ‖traceFull hk1 r u n‖ ^ 2) := by
  have hk2 : 2 ≤ k := by omega
  have hr0pos : 0 < r := by omega
  have hr0lt : r < k := by omega
  have ha : aOf r k ∈ Set.Ioo (0 : ℝ) 1 := aOf_mem hk hr1 hrk
  have hbabs : |bOf k| ≤ 1 := (bOf_abs_lt hk).le
  have hfE : (u : ℂ → ℂ) ∈ Erot1 k r := (Submodule.mem_inf.mp u.2).2
  have hG : ContDiff ℝ 1 (extChoice hk1 u) := extChoice_contDiff hk1 u
  have hGeq : ∀ w ∈ disk, (u : ℂ → ℂ) w = extChoice hk1 u w := extChoice_eqOn hk1 u
  have hφinj : Function.Injective (fun n : ℤ => (k : ℤ) * n + ((k - r : ℕ) : ℤ)) := by
    intro p q h
    have hkab : (k : ℤ) * p = (k : ℤ) * q := by simp only at h; exact add_right_cancel h
    exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr (by omega)) hkab
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  -- `∑ σ‖t‖²` summable, in the `traceFull` coordinate (reindex of the DtN-weighted energy)
  have hσt : Summable (fun n : ℤ => sigmaArc (aOf r k) (bOf k) n * ‖traceFull hk1 r u n‖ ^ 2) := by
    have hcomp := (sigma_trace_sq_summable hk2 hG hGeq hfE hr0pos hr0lt).comp_injective hφinj
    have hkstep : Summable
        (fun n : ℤ => (k : ℝ) * (sigmaArc (aOf r k) (bOf k) n * ‖traceFull hk1 r u n‖ ^ 2)) := by
      refine hcomp.congr (fun n => ?_)
      simp only [Function.comp_apply]
      have hσ : sigma k ((k : ℤ) * n + ((k - r : ℕ) : ℤ)).natAbs
          = (k : ℝ) * sigmaArc (aOf r k) (bOf k) n := by
        have h := sigma_natAbs_eq (r := k - r) hk1 (by omega) (by omega) n
        rwa [show k - (k - r) = r from by omega] at h
      rw [hσ, ← traceFull_apply hk1 r u n]
      ring
    exact (hkstep.mul_left ((k : ℝ)⁻¹)).congr
      (fun n => by rw [← mul_assoc, inv_mul_cancel₀ hk0.ne', one_mul])
  -- dominate `(1+|n|)‖t‖²` by `4|σ|‖t‖²` plus a finite head correction
  have hσabs : Summable
      (fun n : ℤ => 4 * |sigmaArc (aOf r k) (bOf k) n| * ‖traceFull hk1 r u n‖ ^ 2) := by
    have h1 : Summable (fun n : ℤ => |sigmaArc (aOf r k) (bOf k) n * ‖traceFull hk1 r u n‖ ^ 2|) :=
      summable_abs_iff.mpr hσt
    refine (h1.mul_left 4).congr (fun n => ?_)
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖traceFull hk1 r u n‖)]; ring
  have hheadsum : Summable (fun n : ℤ =>
      Set.indicator (↑({-2, -1, 0, 1} : Finset ℤ)) (fun n => 3 * ‖traceFull hk1 r u n‖ ^ 2) n) :=
    summable_of_ne_finset_zero (s := ({-2, -1, 0, 1} : Finset ℤ))
      (fun n hn => Set.indicator_of_notMem (by simpa using hn) _)
  refine (hσabs.add hheadsum).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  have hT : (0 : ℝ) ≤ ‖traceFull hk1 r u n‖ ^ 2 := sq_nonneg _
  by_cases hn : n ∈ ({-2, -1, 0, 1} : Finset ℤ)
  · rw [Set.indicator_of_mem (by simpa using hn)]
    obtain ⟨hlo, hhi⟩ : (-2 : ℤ) ≤ n ∧ n ≤ 1 := by
      have hn' := hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn'
      omega
    have hlo' : (-2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
    have hhi' : (n : ℝ) ≤ 1 := by exact_mod_cast hhi
    have hn3 : 1 + |(n : ℝ)| ≤ 3 := by
      have : |(n : ℝ)| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have h4 : (0 : ℝ) ≤ 4 * |sigmaArc (aOf r k) (bOf k) n| * ‖traceFull hk1 r u n‖ ^ 2 := by
      positivity
    linarith [mul_le_mul_of_nonneg_right hn3 hT, h4]
  · rw [Set.indicator_of_notMem (by simpa using hn), add_zero]
    obtain ⟨hnm2, hnm1, hn0, hn1⟩ : n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0 ∧ n ≠ 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      exact hn
    have hσpos : 0 ≤ sigmaArc (aOf r k) (bOf k) n :=
      le_trans (by norm_num) (sigmaArc_ge_three_halves ha hbabs ⟨hnm2, hnm1, hn0, hn1⟩)
    have htail : 1 + |(n : ℝ)| ≤ 4 * sigmaArc (aOf r k) (bOf k) n := by
      have hinf := sigmaArc_ge_inf ha hbabs n
      rcases le_or_gt 0 n with hl | hl
      · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (2 : ℤ) ≤ n by omega)
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ))]
        rw [abs_of_pos (by linarith [ha.1] : (0 : ℝ) < (n : ℝ) + aOf r k)] at hinf
        have hinv : 1 / ((n : ℝ) + aOf r k) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith [ha.1])
        nlinarith [hinf, hinv, hn2, ha.1]
      · have hn3 : (n : ℝ) ≤ -3 := by exact_mod_cast (show n ≤ (-3 : ℤ) by omega)
        rw [abs_of_neg (by linarith : (n : ℝ) < 0)]
        rw [abs_of_neg (by linarith [ha.2] : (n : ℝ) + aOf r k < 0)] at hinf
        have hinv : 1 / (-((n : ℝ) + aOf r k)) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith [ha.2])
        nlinarith [hinf, hinv, hn3, ha.2]
    rw [abs_of_nonneg hσpos]
    nlinarith [mul_le_mul_of_nonneg_right htail hT]

end KsIndex.MixedUpper
