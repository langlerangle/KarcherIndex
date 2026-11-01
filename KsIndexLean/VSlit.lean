module

/-
# A mixed test function with positive mean boundary trace

`cutSlitC` is the globally smooth complex-valued slit cutoff. The function
`vSlitC` agrees with it on the closed disk and is zero outside; it has no
radial ground-state factor. For `k ≥ 1`, `δ > 0` and `c > 0`, `vSlit_mem`
places it in `NatCc k true false ⊓ Erot1 k 0`.

The real quantity `nuSlit` is its mean boundary value,
`(2π)⁻¹ ∫₀^{2π} cutSlit k δ c (exp(iθ)) dθ`. The lemma
`Fm_cutSlitC_zero_one` identifies this with the zeroth Fourier mode of the
smooth extension on the unit circle. For `k ≥ 2`, `δ > 0` and `0 < c ≤ 1/2`,
`nuSlit_pos` proves strict positivity: the nonnegative continuous integrand
equals one at the interior angle `2π/k`.

The positive trace supplies data for later mixed-form pairing arguments;
the pairing identity itself is not proved in this module.
-/
public import KsIndexLean.SlitCutoffGrad

@[expose] public section


noncomputable section

open Complex MeasureTheory Set Filter
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SingleDiskBridge KsIndex.Parseval
  KsIndex.FourierMode KsIndex.Radial KsIndex.Bracket KsIndex.SurfaceSym
open scoped ContDiff

namespace KsIndex.SingleDisk

variable {k : ℕ}

/-! ### The global smooth cut-off and its truncation -/

/-- The slit cut-off as a globally smooth `ℂ`-valued function. -/
def cutSlitC (k : ℕ) (δ c : ℝ) (w : ℂ) : ℂ := ((cutSlit k δ c w : ℝ) : ℂ)

lemma contDiff_cutSlitC (k : ℕ) (δ c : ℝ) : ContDiff ℝ ∞ (cutSlitC k δ c) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_cutSlit k δ c)

/-- **The trace-carrying test function**: the slit cut-off truncated to the closed disk. -/
def vSlitC (k : ℕ) (δ c : ℝ) (w : ℂ) : ℂ := if ‖w‖ ≤ 1 then cutSlitC k δ c w else 0

lemma vSlitC_eq_of_mem {δ c : ℝ} {w : ℂ} (hw : w ∈ disk) :
    vSlitC k δ c w = cutSlitC k δ c w := by
  have h1 : ‖w‖ < 1 := mem_disk_iff.mp hw
  simp [vSlitC, h1.le]

/-! ### Membership in the class-0 mixed natural space -/

theorem vSlit_mem_NatCc (hk : 1 ≤ k) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    vSlitC k δ c ∈ NatCc k true false := by
  have hF := contDiff_cutSlitC k δ c
  have hone : ∀ w₀, OneSided (vSlitC k δ c) w₀ := fun w₀ =>
    ⟨_, hF.contDiffAt, Eventually.of_forall fun w hw => vSlitC_eq_of_mem hw⟩
  obtain ⟨ε, hε, hnb⟩ := slit_nbhd hk hδ hc
  have hvan : ∀ w : ℂ, (∃ p ∈ KsIndex.Bracket.slit k, ‖w - p‖ < ε) → vSlitC k δ c w = 0 := by
    intro w hw
    obtain ⟨h1, h2⟩ := hnb w hw
    unfold vSlitC cutSlitC
    split_ifs
    · rw [cutSlit_zero hδ hc h1 h2, Complex.ofReal_zero]
    · rfl
  rw [mem_NatCc]
  refine ⟨hF.contDiffOn.congr fun w hw => vSlitC_eq_of_mem hw,
    fun w _ => hone w,
    ⟨ε, hε, hvan⟩,
    fun w hw => by simp [vSlitC, not_le.mpr hw],
    ⟨ε, hε, fun w ⟨p, hp, hwp⟩ =>
      hvan w ⟨p, KsIndex.Bracket.punctures_subset_slit hk hp, hwp⟩⟩⟩

lemma vSlitC_rot (hk : 1 ≤ k) (δ c : ℝ) :
    rot1 (rotUnit k : ℂ) (vSlitC k δ c) = vSlitC k δ c := by
  funext w
  have ha : ‖(rotUnit k : ℂ)‖ = 1 := Circle.norm_coe _
  have hak : (rotUnit k : ℂ) ^ k = 1 := rotUnit_pow (by omega)
  simp only [rot1_apply, vSlitC, cutSlitC, norm_mul, ha, one_mul]
  rw [cutSlit_rot ha hak]

theorem vSlit_mem_Erot1 (hk : 1 ≤ k) (δ c : ℝ) : vSlitC k δ c ∈ Erot1 k 0 := by
  rw [Erot1, Module.End.mem_eigenspace_iff, vSlitC_rot hk]
  simp

/-- For `k ≥ 1` and positive cutoff parameters, the trace-carrying function
belongs to the class-0 mixed natural space. -/
theorem vSlit_mem (hk : 1 ≤ k) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    vSlitC k δ c ∈ NatCc k true false ⊓ Erot1 k 0 :=
  Submodule.mem_inf.mpr ⟨vSlit_mem_NatCc hk hδ hc, vSlit_mem_Erot1 hk δ c⟩

/-! ### The boundary trace and its positivity -/

/-- The `ℓ = 0` boundary trace of the cut-off (real form). -/
def nuSlit (k : ℕ) (δ c : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, cutSlit k δ c (Complex.exp (θ * I))

/-- The complex `ℓ = 0` mode of the global extension is the real trace. -/
lemma Fm_cutSlitC_zero_one (k : ℕ) (δ c : ℝ) :
    Fm (cutSlitC k δ c) 0 1 = ((nuSlit k δ c : ℝ) : ℂ) := by
  unfold Fm fc nuSlit
  simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
  have hs : (fun θ : ℝ => slice (cutSlitC k δ c) 1 θ)
      = fun θ : ℝ => ((cutSlit k δ c (Complex.exp (θ * I)) : ℝ) : ℂ) := by
    funext θ
    simp only [slice, cutSlitC, Complex.ofReal_one, one_mul]
  rw [hs, intervalIntegral.integral_ofReal]
  push_cast
  ring

/-- A continuous nonnegative function positive at an interior point has positive integral. -/
lemma integral_pos_of_nonneg_of_pos_at {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x)
    {a b x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo a b) (hpos : 0 < f x₀) :
    0 < ∫ x in a..b, f x := by
  have hab : a ≤ b := le_of_lt (hx₀.1.trans hx₀.2)
  rw [intervalIntegral.integral_of_le hab]
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ ?_).2 ?_
  · exact Eventually.of_forall hnn
  · exact hf.integrableOn_Ioc
  · set U : Set ℝ := {x | f x₀ / 2 < f x} ∩ Set.Ioo a b with hU
    have hUopen : IsOpen U := (isOpen_lt continuous_const hf).inter isOpen_Ioo
    have hx₀U : x₀ ∈ U := ⟨by simp only [Set.mem_ofPred_eq]; linarith, hx₀⟩
    have hUpos : 0 < volume U := hUopen.measure_pos volume ⟨x₀, hx₀U⟩
    refine lt_of_lt_of_le hUpos (measure_mono fun x hx => ?_)
    refine ⟨?_, Set.Ioo_subset_Ioc_self hx.2⟩
    have : 0 < f x := lt_of_le_of_lt (by linarith) hx.1
    exact fun h0 => this.ne' h0

/-- **Positivity of the trace** for `k ≥ 2`, `δ > 0` and `0 < c ≤ ½`: the cut-off equals `1` at the interior angle
`θ = 2π/k`, where `w^k = e^{2πi} = 1`. -/
theorem nuSlit_pos (hk2 : 2 ≤ k) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    0 < nuSlit k δ c := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  refine mul_pos (by positivity) ?_
  set f : ℝ → ℝ := fun θ => cutSlit k δ c (Complex.exp (θ * I)) with hf
  have hfc : Continuous f :=
    (contDiff_cutSlit k δ c).continuous.comp (by fun_prop)
  have hnn : ∀ θ, 0 ≤ f θ := fun θ => (cutSlit_mem_Icc k δ c _).1
  set θ₀ : ℝ := 2 * Real.pi / k with hθ₀
  have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk2' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hθ₀mem : θ₀ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
    constructor
    · rw [hθ₀]
      exact div_pos h2π hk'
    · rw [hθ₀, div_lt_iff₀ hk']
      nlinarith
  have hkne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hval : f θ₀ = 1 := by
    have hwk : Complex.exp ((θ₀ : ℝ) * I) ^ k = 1 := by
      rw [← Complex.exp_nat_mul]
      have harg : (k : ℂ) * ((θ₀ : ℝ) * I) = 2 * (Real.pi : ℂ) * I := by
        rw [hθ₀]
        push_cast
        field_simp
      rw [harg]
      have := Complex.exp_two_pi_mul_I
      rw [show 2 * (Real.pi : ℂ) * I = 2 * Real.pi * I by ring]
      simpa [mul_comm, mul_assoc] using this
    have hre : ((Complex.exp ((θ₀ : ℝ) * I)) ^ k).re = 1 := by rw [hwk]; simp
    rw [hf]
    apply cutSlit_one hδ hc
    right
    rw [hre]
    linarith
  exact integral_pos_of_nonneg_of_pos_at hfc hnn hθ₀mem (by rw [hval]; norm_num)

end KsIndex.SingleDisk
