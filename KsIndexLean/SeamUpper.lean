module

/-
# A seam index upper bound from boundary Fourier traces

For `k ≥ 3`, `r < k` and either choice of the two boundary-condition
flags, `seamNat_le_neumannCount` proves

`formIndex (Qd k) (NatCc k b₁ b₀ ⊓ Erot1 k r)
  ≤ neumannCount k (r : ZMod k) + (if (r : ZMod k) = 0 then 1 else 0)`.

A natural test function has a global `C¹` extension agreeing with it on
the open disk. The Fourier decomposition of this extension expresses
`Qd` as `2 * π` times a sum of radial mode energies. If its boundary
Fourier coefficients vanish on `headSet k r`, the radial estimates make
every mode energy nonnegative: the low on-class modes are controlled by
these vanishing traces, off-class traces vanish by the rotation condition,
and the symbol is nonnegative above the frequency threshold.

The trace-coefficient map is linear, so nonnegativity on its kernel bounds
the index by the cardinality of `headSet k r`. The final calculation
identifies this cardinality with the displayed count.

Boundary coefficients are obtained from the interior radial limit, using
a smooth extension. In particular, the one-sided arc extension condition
does not identify the original function's assigned boundary values with
its trace. The limit proves linearity and makes the trace independent of
the chosen extension.
-/
public import KsIndexLean.PiAssembly
public import KsIndexLean.NeumannCount
public import KsIndexLean.ClosedDiskExt
public import KsIndexLean.SeamLowerNat

@[expose] public section


noncomputable section

open Complex Real MeasureTheory intervalIntegral Set Filter Topology
open KsIndex.Parseval KsIndex.FourierMode KsIndex.Radial KsIndex.Surface KsIndex.SurfaceForm
  KsIndex.SingleDiskBridge KsIndex.SingleDisk KsIndex.FormIndex KsIndex.PiAssembly
open scoped ContDiff

namespace KsIndex.SeamUpper

variable {k : ℕ}

/-! ### `slice` and `Fm` are additive / homogeneous where the slices are integrable -/

lemma slice_add (f g : ℂ → ℂ) (r : ℝ) : slice (f + g) r = slice f r + slice g r := by
  funext θ; simp [slice, Pi.add_apply]

lemma slice_smul (c : ℂ) (f : ℂ → ℂ) (r : ℝ) : slice (c • f) r = c • slice f r := by
  funext θ; simp [slice, Pi.smul_apply]

lemma sliceIntegrand_intervalIntegrable {f : ℂ → ℂ} {r : ℝ} (hf : Continuous (slice f r))
    (ℓ : ℤ) :
    IntervalIntegrable (fun θ => slice f r θ * Complex.exp (-(ℓ : ℂ) * I * θ)) volume 0 (2 * π) :=
  (hf.mul (by fun_prop)).intervalIntegrable _ _

lemma fc_add {a b : ℝ → ℂ} (ℓ : ℤ)
    (ha : IntervalIntegrable (fun θ => a θ * Complex.exp (-(ℓ : ℂ) * I * θ)) volume 0 (2 * π))
    (hb : IntervalIntegrable (fun θ => b θ * Complex.exp (-(ℓ : ℂ) * I * θ)) volume 0 (2 * π)) :
    fc (a + b) ℓ = fc a ℓ + fc b ℓ := by
  unfold fc
  rw [← mul_add, ← intervalIntegral.integral_add ha hb]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [Pi.add_apply]; ring

lemma fc_smul (c : ℂ) (a : ℝ → ℂ) (ℓ : ℤ) : fc (c • a) ℓ = c * fc a ℓ := by
  unfold fc
  rw [show (∫ θ in (0 : ℝ)..2 * π, (c • a) θ * Complex.exp (-(ℓ : ℂ) * I * θ))
        = ∫ θ in (0 : ℝ)..2 * π, c * (a θ * Complex.exp (-(ℓ : ℂ) * I * θ)) from by
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring,
    intervalIntegral.integral_const_mul]
  ring

lemma Fm_add_of {f g : ℂ → ℂ} {r : ℝ} (ℓ : ℤ)
    (hf : Continuous (slice f r)) (hg : Continuous (slice g r)) :
    Fm (f + g) ℓ r = Fm f ℓ r + Fm g ℓ r := by
  unfold Fm
  rw [slice_add, fc_add ℓ (sliceIntegrand_intervalIntegrable hf ℓ)
    (sliceIntegrand_intervalIntegrable hg ℓ)]

lemma Fm_smul_of (c : ℂ) (f : ℂ → ℂ) (ℓ : ℤ) (r : ℝ) : Fm (c • f) ℓ r = c * Fm f ℓ r := by
  unfold Fm; rw [slice_smul, fc_smul]

/-! ### `slice` continuity and `Fm` congruence on the open disk -/

lemma slice_continuous {f : ℂ → ℂ} (hf : ContinuousOn f disk) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (slice f r) := by
  have hmap : Continuous fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * I) := by fun_prop
  have hmem : ∀ θ : ℝ, (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ disk := by
    intro θ
    rw [mem_disk_iff, norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    exact hr1
  exact hf.comp_continuous hmap hmem

lemma Fm_congr_of_eqOn {f g : ℂ → ℂ} (hfg : ∀ w ∈ disk, f w = g w) (ℓ : ℤ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) : Fm f ℓ r = Fm g ℓ r := by
  have hs : slice f r = slice g r := by
    funext θ
    refine hfg _ ?_
    rw [mem_disk_iff, norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    exact hr1
  unfold Fm; rw [hs]

/-! ### The DtN symbol is nonnegative above the momentum threshold -/

lemma sigma_nonneg (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : k - 1 ≤ ℓ) : 0 ≤ sigma k ℓ := by
  rw [sigma, kap]
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
  have hℓ' : (k : ℝ) - 1 ≤ (ℓ : ℝ) := by rw [← hcast]; exact_mod_cast hℓ
  have hk0 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  apply div_nonneg _ (Nat.cast_nonneg ℓ)
  nlinarith [hℓ', hk0]

/-! ### Boundary points of `NatCc k b₁ b₀` carry a local smooth extension -/

/-- A norm-one point with `(x^k).re = 0` is a puncture (`x^{2k} = −1`). -/
lemma puncture_of_reZero {x : ℂ} (hx : ‖x‖ = 1) (h0 : (x ^ k).re = 0) : x ∈ punctures k := by
  have him : (x ^ k).im ^ 2 = 1 := by
    have h1 : ‖x ^ k‖ = 1 := by rw [norm_pow, hx, one_pow]
    have h2 : (1 : ℝ) ^ 2 = (x ^ k).re ^ 2 + (x ^ k).im ^ 2 := by rw [← h1]; exact norm_sq_eq _
    rw [h0] at h2; nlinarith [h2]
  show x ^ (2 * k) = -1
  have hpow : x ^ (2 * k) = (x ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hpow]
  apply Complex.ext
  · rw [pow_two, Complex.mul_re, h0]; simp only [Complex.neg_re, Complex.one_re]; nlinarith [him]
  · rw [pow_two, Complex.mul_im, h0]; simp

/-- The natural arc condition provides a local smooth extension at every arc point: for `true`
(Neumann) the one-sided extension, for `false` (Dirichlet) the zero function, since `f` vanishes
near the arc's closure. -/
lemma arcCond_local_ext {A S : Set ℂ} {b : Bool} {f : ℂ → ℂ} (h : ArcCond A S b f)
    (hAS : A ⊆ S) {x : ℂ} (hx : x ∈ A) :
    ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F x ∧ ∀ᶠ y in nhds x, y ∈ Metric.ball (0 : ℂ) 1 → f y = F y := by
  cases b
  · obtain ⟨ε, hε, hz⟩ := h
    refine ⟨0, contDiffAt_const, ?_⟩
    filter_upwards [Metric.ball_mem_nhds x hε] with y hy _
    refine hz y ⟨x, hAS hx, ?_⟩
    rw [← dist_eq_norm]; exact Metric.mem_ball.mp hy
  · obtain ⟨F, hF, hFe⟩ := h x hx
    exact ⟨F, hF, hFe⟩

/-- **Closed-disk extension of a natural test function, every encoding pair.**  Every
`f ∈ NatCc k b₁ b₀` has a global `C¹` function agreeing with it on the open disk. -/
lemma natCc_extension {f : ℂ → ℂ} {b₁ b₀ : Bool} (hk : 1 ≤ k) (hf : f ∈ NatCc k b₁ b₀) :
    ∃ G : ℂ → ℂ, ContDiff ℝ 1 G ∧ ∀ w ∈ disk, f w = G w := by
  obtain ⟨hsm, harc1, harc0, _hout, hsupp⟩ := mem_NatCc.mp hf
  have h : ∀ x ∈ Metric.closedBall (0 : ℂ) 1, ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F x ∧
      ∀ᶠ y in nhds x, y ∈ Metric.ball (0 : ℂ) 1 → f y = F y := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    rcases hx.lt_or_eq with hlt | hx1
    · -- interior point
      refine ⟨f, hsm.contDiffAt (Metric.isOpen_ball.mem_nhds (mem_disk_iff.mpr hlt)),
        Eventually.of_forall fun y _ => rfl⟩
    · -- boundary point
      rcases lt_trichotomy ((x ^ k).re) 0 with hneg | hzero | hpos
      · -- arc_0
        exact arcCond_local_ext harc0 KsIndex.Bracket.arc_zero_subset_slit
          ⟨hx1, by simpa [arc] using hneg⟩
      · -- puncture
        have hxp : x ∈ punctures k := puncture_of_reZero hx1 hzero
        obtain ⟨ε, hε, hz⟩ := hsupp
        refine ⟨0, contDiffAt_const, ?_⟩
        filter_upwards [Metric.ball_mem_nhds x hε] with y hy _
        refine hz y ⟨x, hxp, ?_⟩
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hy
      · -- arc_1
        exact arcCond_local_ext harc1 arc_one_subset_slitC ⟨hx1, by
          simp only [arc, Set.mem_setOf_eq, pow_one, neg_one_mul, neg_lt_zero]; exact hpos⟩
  obtain ⟨G, hG, _, hGeq⟩ := ClosedDiskExt.exists_finite_order_extension f h 1
  exact ⟨G, hG, fun w hw => hGeq w hw⟩

/-! ### The head index set and its cardinality -/

/-- The finite set of "bad" angular modes for class `r`: the negative-σ on-class modes
`1 ≤ |ℓ| ≤ k−2`, `ℓ ≡ −r (mod k)`, together with the `ℓ = 0` mode when `k ∣ r`. -/
def headSet (k r : ℕ) : Finset ℤ :=
  (Finset.Icc (-(k : ℤ) + 2) ((k : ℤ) - 2)).filter
    (fun ℓ => (k : ℤ) ∣ ((r : ℤ) + ℓ) ∧ (ℓ ≠ 0 ∨ (k : ℤ) ∣ (r : ℤ)))

lemma mem_headSet {k r : ℕ} {ℓ : ℤ} :
    ℓ ∈ headSet k r ↔ |ℓ| ≤ (k : ℤ) - 2 ∧ (k : ℤ) ∣ ((r : ℤ) + ℓ) ∧ (ℓ ≠ 0 ∨ (k : ℤ) ∣ (r : ℤ)) := by
  rw [headSet, Finset.mem_filter, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨by omega, h3⟩

/-! ### The closed-disk extension chosen for each domain vector -/

variable {b₁ b₀ : Bool} {r : ℕ}

/-- A chosen global `C¹` extension of a domain vector, agreeing with it on the open disk. -/
def extChoice (hk : 1 ≤ k) (u : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) : ℂ → ℂ :=
  Classical.choose (natCc_extension hk (Submodule.mem_inf.mp u.2).1)

lemma extChoice_contDiff (hk : 1 ≤ k) (u : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) :
    ContDiff ℝ 1 (extChoice hk u) :=
  (Classical.choose_spec (natCc_extension hk (Submodule.mem_inf.mp u.2).1)).1

lemma extChoice_eqOn (hk : 1 ≤ k) (u : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) :
    ∀ w ∈ disk, (u : ℂ → ℂ) w = extChoice hk u w :=
  (Classical.choose_spec (natCc_extension hk (Submodule.mem_inf.mp u.2).1)).2

/-- `Ioo 0 1` is a neighbourhood of `1` from the left. -/
lemma Ioo_mem_nhds_lt : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := by
  rw [mem_nhdsWithin]
  exact ⟨Set.Ioi 0, isOpen_Ioi, by norm_num, by rw [Set.Ioi_inter_Iio]⟩

/-- The boundary trace of the extension is the interior limit of the modes of the vector. -/
lemma Fm_tendsto_ext (hk : 1 ≤ k) (u : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) (ℓ : ℤ) :
    Tendsto (Fm (u : ℂ → ℂ) ℓ) (𝓝[<] (1 : ℝ)) (𝓝 (Fm (extChoice hk u) ℓ 1)) := by
  have hcont : Continuous (Fm (extChoice hk u) ℓ) :=
    Fm_continuous (extChoice_contDiff hk u).continuous ℓ
  have hev : Fm (u : ℂ → ℂ) ℓ =ᶠ[𝓝[<] (1 : ℝ)] Fm (extChoice hk u) ℓ := by
    filter_upwards [Ioo_mem_nhds_lt] with s hs
    exact Fm_congr_of_eqOn (extChoice_eqOn hk u) ℓ hs.1.le hs.2
  exact ((hcont.tendsto 1).mono_left nhdsWithin_le_nhds).congr' hev.symm

/-! ### The trace-coefficient map -/

/-- **The trace-coefficient map**: a domain vector to its boundary-trace Fourier coefficients on
the head set.  `ℂ`-linear because the boundary trace is the interior limit of the (linear) modes. -/
def traceMap (hk : 1 ≤ k) (r : ℕ) :
    ↥(NatCc k b₁ b₀ ⊓ Erot1 k r) →ₗ[ℂ] (↥(headSet k r) → ℂ) where
  toFun u := fun ℓ => Fm (extChoice hk u) ℓ.val 1
  map_add' u v := by
    funext ℓ
    haveI : (𝓝[<] (1 : ℝ)).NeBot := inferInstance
    simp only [Pi.add_apply]
    refine tendsto_nhds_unique (Fm_tendsto_ext hk (u + v) ℓ.val) ?_
    have hu : (u : ℂ → ℂ) ∈ NatCc k b₁ b₀ := (Submodule.mem_inf.mp u.2).1
    have hv : (v : ℂ → ℂ) ∈ NatCc k b₁ b₀ := (Submodule.mem_inf.mp v.2).1
    have hev : Fm ((u + v : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) : ℂ → ℂ) ℓ.val
        =ᶠ[𝓝[<] (1 : ℝ)] (fun s => Fm (u : ℂ → ℂ) ℓ.val s + Fm (v : ℂ → ℂ) ℓ.val s) := by
      filter_upwards [Ioo_mem_nhds_lt] with s hs
      rw [Submodule.coe_add]
      exact Fm_add_of ℓ.val (slice_continuous (mem_NatCc.mp hu).1.continuousOn hs.1.le hs.2)
        (slice_continuous (mem_NatCc.mp hv).1.continuousOn hs.1.le hs.2)
    exact (Tendsto.add (Fm_tendsto_ext hk u ℓ.val) (Fm_tendsto_ext hk v ℓ.val)).congr' hev.symm
  map_smul' c u := by
    funext ℓ
    haveI : (𝓝[<] (1 : ℝ)).NeBot := inferInstance
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    refine tendsto_nhds_unique (Fm_tendsto_ext hk (c • u) ℓ.val) ?_
    have hfun : Fm ((c • u : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) : ℂ → ℂ) ℓ.val
        = fun s => c * Fm (u : ℂ → ℂ) ℓ.val s := by
      funext s; rw [Submodule.coe_smul]; exact Fm_smul_of c (u : ℂ → ℂ) ℓ.val s
    rw [hfun]
    exact (Fm_tendsto_ext hk u ℓ.val).const_mul c

/-! ### Off-class boundary traces vanish -/

lemma Fm_ext_boundary_zero {G f : ℂ → ℂ} (hG : ContDiff ℝ 1 G) (hGeq : ∀ w ∈ disk, f w = G w)
    {r0 : ℕ} (hf : f ∈ Erot1 k r0) (hk : 0 < k) {ℓ : ℤ} (hcl : ¬ (k : ℤ) ∣ ((r0 : ℤ) + ℓ)) :
    Fm G ℓ 1 = 0 := by
  haveI : (𝓝[<] (1 : ℝ)).NeBot := inferInstance
  have hlt : ∀ s ∈ Set.Ico (0 : ℝ) 1, Fm G ℓ s = 0 := fun s hs => by
    rw [← Fm_congr_of_eqOn hGeq ℓ hs.1 hs.2]; exact Fm_eq_zero_of_class hf hk hcl s
  have hev : Fm G ℓ =ᶠ[𝓝[<] (1 : ℝ)] 0 := by
    filter_upwards [Ioo_mem_nhds_lt] with s hs
    exact hlt s ⟨hs.1.le, hs.2⟩
  have h1 : Tendsto (Fm G ℓ) (𝓝[<] (1 : ℝ)) (𝓝 0) := tendsto_const_nhds.congr' hev.symm
  have h2 : Tendsto (Fm G ℓ) (𝓝[<] (1 : ℝ)) (𝓝 (Fm G ℓ 1)) :=
    ((Fm_continuous hG.continuous ℓ).tendsto 1).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique h2 h1

/-! ### Per-mode nonnegativity on the kernel -/

/-- Each angular-mode radial form is nonnegative once the head-set boundary traces vanish. -/
lemma modeTerm_nonneg (hk : 3 ≤ k) {G f : ℂ → ℂ} (hG : ContDiff ℝ 1 G)
    (hGeq : ∀ w ∈ disk, f w = G w) {r0 : ℕ} (hf : f ∈ Erot1 k r0)
    (htrace : ∀ ℓ : ℤ, ℓ ∈ headSet k r0 → Fm G ℓ 1 = 0) (ℓ : ℤ) :
    0 ≤ ∫ s in (0 : ℝ)..1, lhsC k ℓ.natAbs (Fm G ℓ) (FmD G ℓ) s := by
  have hk2 : 2 ≤ k := by omega
  have hk0 : 0 < k := by omega
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (Fm G ℓ) (FmD G ℓ s) s :=
    fun s _ => Fm_hasDerivAt hG ℓ s
  have hcont' : ContinuousOn (FmD G ℓ) (Set.Icc 0 1) := (FmD_continuous hG ℓ).continuousOn
  rcases eq_or_ne ℓ 0 with hℓ0 | hℓ0
  · subst hℓ0
    have htr0 : Fm G 0 1 = 0 := by
      by_cases hdvd : (k : ℤ) ∣ (r0 : ℤ)
      · exact htrace 0 (mem_headSet.mpr ⟨by simp; omega, by simpa using hdvd, Or.inr (by simpa using hdvd)⟩)
      · exact Fm_ext_boundary_zero hG hGeq hf hk0 (by simpa using hdvd)
    simpa using qMode_zero_nonneg_complex hk2 hderiv hcont' htr0
  · have hnat : 1 ≤ ℓ.natAbs := Int.natAbs_pos.mpr hℓ0
    have hkey : sigma k ℓ.natAbs * ‖Fm G ℓ 1‖ ^ 2 ≤
        ∫ s in (0 : ℝ)..1, lhsC k ℓ.natAbs (Fm G ℓ) (FmD G ℓ) s :=
      qMode_ge_complex hk2 hnat hderiv hcont' (Fm_zero_of_ne G hℓ0)
    refine le_trans ?_ hkey
    by_cases hsmall : |ℓ| ≤ (k : ℤ) - 2
    · have htr : Fm G ℓ 1 = 0 := by
        by_cases hdvd : (k : ℤ) ∣ ((r0 : ℤ) + ℓ)
        · exact htrace ℓ (mem_headSet.mpr ⟨hsmall, hdvd, Or.inl hℓ0⟩)
        · exact Fm_ext_boundary_zero hG hGeq hf hk0 hdvd
      rw [htr]; simp
    · have hge : k - 1 ≤ ℓ.natAbs := by
        have h : (k : ℤ) - 2 < |ℓ| := not_le.mp hsmall
        rw [Int.abs_eq_natAbs] at h
        omega
      exact mul_nonneg (sigma_nonneg (by omega) hge) (sq_nonneg _)

/-! ### The head-set cardinality -/

/-- `headSet` is the pair `{−r, k−r}` cut down to the window `|ℓ| ≤ k−2`. -/
lemma headSet_eq_pair (hk : 3 ≤ k) {r : ℕ} (hr : r < k) :
    headSet k r = ({(-(r : ℤ)), (k : ℤ) - r} : Finset ℤ).filter (fun ℓ => |ℓ| ≤ (k : ℤ) - 2) := by
  have hk' : (3 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  have hr' : (r : ℤ) < (k : ℤ) := by exact_mod_cast hr
  ext ℓ
  rw [mem_headSet, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨habs, ⟨t, ht⟩, _⟩
    rw [abs_le] at habs
    have hk0 : (0 : ℤ) < k := by omega
    have hb1 : -(k : ℤ) < (r : ℤ) + ℓ := by omega
    have hb2 : (r : ℤ) + ℓ < 2 * k := by omega
    rw [ht] at hb1 hb2
    have ht0 : 0 ≤ t := by
      by_contra h; push_neg at h
      have hle : (k : ℤ) * t ≤ (k : ℤ) * (-1) := Int.mul_le_mul_of_nonneg_left (by omega) hk0.le
      rw [mul_neg_one] at hle; omega
    have ht1 : t ≤ 1 := by
      by_contra h; push_neg at h
      have hge : (k : ℤ) * 2 ≤ (k : ℤ) * t := Int.mul_le_mul_of_nonneg_left (by omega) hk0.le
      omega
    refine ⟨?_, by rw [abs_le]; omega⟩
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
    · left; omega
    · right; omega
  · rintro ⟨hor, habs⟩
    rw [abs_le] at habs
    rcases hor with rfl | rfl
    · exact ⟨by rw [abs_le]; omega, ⟨0, by ring⟩,
        by rcases eq_or_ne (r : ℤ) 0 with h0 | h0
           · exact Or.inr (by rw [h0]; exact dvd_zero _)
           · exact Or.inl (by simpa using h0)⟩
    · exact ⟨by rw [abs_le]; omega, ⟨1, by ring⟩, Or.inl (by omega)⟩

lemma headSet_card_nat (hk : 3 ≤ k) {r : ℕ} (hr : r < k) :
    (headSet k r).card = (if 1 ≤ r ∧ r ≤ k - 2 then 1 else 0) + (if 2 ≤ r then 1 else 0)
      + (if r = 0 then 1 else 0) := by
  have hpair := headSet_eq_pair hk hr
  have eA : (|(-(r : ℤ))| ≤ (k : ℤ) - 2) ↔ r ≤ k - 2 := by rw [abs_le]; omega
  have eB : (|((k : ℤ) - r)| ≤ (k : ℤ) - 2) ↔ 2 ≤ r := by rw [abs_le]; omega
  have hne : (-(r : ℤ)) ≠ (k : ℤ) - r := by omega
  by_cases cA : r ≤ k - 2 <;> by_cases cB : 2 ≤ r
  · have hset : headSet k r = {(-(r : ℤ)), (k : ℤ) - r} := by
      rw [hpair, Finset.filter_true_of_mem]
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact eA.mpr cA
      · exact eB.mpr cB
    rw [hset, Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hne),
      Finset.card_singleton, if_pos ⟨by omega, cA⟩, if_pos cB, if_neg (by omega)]
  · have hset : headSet k r = {(-(r : ℤ))} := by
      rw [hpair]; ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · rfl
        · exact absurd (eB.mp hx) cB
      · rintro rfl; exact ⟨Or.inl rfl, eA.mpr cA⟩
    rw [hset, Finset.card_singleton]
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · rw [if_neg (by omega), if_neg (by omega), if_pos hr0]
    · rw [if_pos ⟨hr0, cA⟩, if_neg cB, if_neg (by omega)]
  · have hset : headSet k r = {(k : ℤ) - r} := by
      rw [hpair]; ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · exact absurd (eA.mp hx) cA
        · rfl
      · rintro rfl; exact ⟨Or.inr rfl, eB.mpr cB⟩
    rw [hset, Finset.card_singleton, if_neg (by omega), if_pos cB, if_neg (by omega)]
  · exfalso; omega

/-! ### The upper bound -/

/-- An index upper bound for class `r` in every natural boundary encoding,
assuming `k ≥ 3` and `r < k`. In particular it applies to the pure-Neumann domain. -/
theorem seamNat_le_neumannCount (hk : 3 ≤ k) {r : ℕ} (hr : r < k) :
    formIndex (Qd k) (NatCc k b₁ b₀ ⊓ Erot1 k r)
      ≤ neumannCount k (r : ZMod k) + (if (r : ZMod k) = 0 then 1 else 0) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  haveI : NeZero k := ⟨by omega⟩
  have hvr : (r : ZMod k).val = r := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hr]
  have hz0 : ((r : ZMod k) = 0) ↔ r = 0 := by
    constructor
    · intro h; rw [← hvr, h]; exact ZMod.val_zero
    · rintro rfl; exact Nat.cast_zero
  have hcard : (Fintype.card ↥(headSet k r) : ℕ∞)
      = neumannCount k (r : ZMod k) + (if (r : ZMod k) = 0 then 1 else 0) := by
    rw [Fintype.card_coe, headSet_card_nat hk hr, neumannCount_eq hk]
    simp only [hvr]
    rw [show (if (r : ZMod k) = 0 then (1 : ℕ∞) else 0) = ((if r = 0 then 1 else 0 : ℕ) : ℕ∞) by
        by_cases h : r = 0 <;> simp [hz0, h]]
    push_cast
    ring
  rw [← hcard]
  refine formIndex_le_of_domMap (traceMap hk1 r) (fun u hT0 => ?_)
  set f := (u : ℂ → ℂ) with hfdef
  have hf : f ∈ NatCc k b₁ b₀ := (Submodule.mem_inf.mp u.2).1
  have hfE : f ∈ Erot1 k r := (Submodule.mem_inf.mp u.2).2
  have hG : ContDiff ℝ 1 (extChoice hk1 u) := extChoice_contDiff hk1 u
  have hGeq : ∀ w ∈ disk, f w = extChoice hk1 u w := extChoice_eqOn hk1 u
  have htrace : ∀ ℓ : ℤ, ℓ ∈ headSet k r → Fm (extChoice hk1 u) ℓ 1 = 0 := by
    intro ℓ hℓ
    have := congrFun hT0 ⟨ℓ, hℓ⟩
    simpa [traceMap] using this
  have hQ : Qd k f = 2 * π * ∑' ℓ : ℤ,
      ∫ s in (0 : ℝ)..1, lhsC k ℓ.natAbs (Fm (extChoice hk1 u) ℓ) (FmD (extChoice hk1 u) ℓ) s := by
    rw [Qd_congr_disk hGeq, Qd_eq_tsum hG hk2]
  rw [hfdef, hQ]
  refine mul_nonneg (by positivity) (tsum_nonneg fun ℓ => ?_)
  exact modeTerm_nonneg hk hG hGeq hfE htrace ℓ

end KsIndex.SeamUpper
