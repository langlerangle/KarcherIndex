module

/-
KsIndexLean — ZeroMeanExtension: the Jacobi extension maps mean-zero boundary
data into the zero-angular-mean block ([ksindexi] tex 2250–2267: in the j = 0
zero-mean half of Lemma `nop-sphop` the Dirichlet decomposition
`u = jext(trace u) + (zero-trace remainder)` stays inside `H¹_{(0;k),⊥}`).

Main results:
* `angularAverage_jacobiExtension` — `P₀ (jext f) = 0` for mean-zero `f`,
  via the normalized-uniqueness theorem applied to `P₀ (jext f)`: its trace
  vanishes coefficientwise (ZeroMeanTrace), and it satisfies the normalized
  weak equations because the test families (zero-trace, constant-trace) are
  rotation-stable and the weak form is rotation-invariant.
* `jacobiExtensionCLM_mem_zeroMeanDomain` — the extension of class-zero
  mean-zero data lies in `zeroMeanDomain k`.
* `zeroMeanTraceData` + `sub_jacobiExtension_mem_zeroMeanDomain` /
  `sub_jacobiExtension_mem_fullZeroTrace` — the paper's decomposition data
  and the membership of both components, feeding the block transport.
-/
public import KsIndexLean.ZeroMeanTrace
public import KsIndexLean.JacobiExtensionUnique
public import KsIndexLean.JacobiExtensionCharacter
public import KsIndexLean.DiskRotationForms
public import KsIndexLean.CircleSobolevRotation

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.DtNCircle KsIndex.CircleSobolev

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-! ### Rotation stability of the two normalized test families -/

/-- Boundary rotation fixes the constant function. -/
lemma boundaryRotation_circleOneL2 (θ : ℝ) :
    boundaryRotation θ circleOneL2 = circleOneL2 := by
  apply Lp.ext
  have h1 : (circleOneL2 : Circle₁ → ℂ) =ᵐ[circleMeasure] fun _ => (1 : ℂ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℂ))
  have h2 : ((circleOneL2 : Circle₁ → ℂ) ∘ circleRotate θ) =ᵐ[circleMeasure]
      (fun _ => (1 : ℂ)) ∘ circleRotate θ :=
    (measurePreserving_circleRotate θ).quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [boundaryRotation_coe_ae θ circleOneL2, h2, h1] with w hw hw2 hw1
  rw [hw]
  exact hw2.trans hw1.symm

/-- Rotation preserves constant boundary traces. The corresponding zero-trace
statement is `diskRotation_mem_fullZeroTrace`. -/
lemma diskRotation_constantTrace (θ : ℝ) {v : ComplexH1} {c : ℂ}
    (hv : diskTraceCLM v = c • circleOneL2) :
    diskTraceCLM (diskRotation θ v) = c • circleOneL2 := by
  rw [diskTrace_rotation, hv, (boundaryRotation θ).map_smul,
    boundaryRotation_circleOneL2]

/-! ### The weak pairing against the angular average -/

/-- The weak Jacobi pairing with a fixed left argument, bundled as a
continuous linear functional in the test slot. -/
def weakJacobiRightCLM (V : BoundedRealPotential) (u : ComplexH1) :
    ComplexH1 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := weakJacobi V u
      map_add' := weakJacobi_add_right V u
      map_smul' := fun a v => weakJacobi_smul_right V a u v }
    ((2 + V.C) * ‖u‖) (fun v => norm_weakJacobi_le V u v)

@[simp] lemma weakJacobiRightCLM_apply (V : BoundedRealPotential)
    (u v : ComplexH1) : weakJacobiRightCLM V u v = weakJacobi V u v := rfl

/-- Averaging in the test slot averages the pairing. -/
lemma weakJacobi_angularAverage_right (V : BoundedRealPotential)
    (w u : ComplexH1) :
    weakJacobi V w (angularAverage u) =
      (2 * Real.pi)⁻¹ • ∫ θ in (0:ℝ)..(2 * Real.pi),
        weakJacobi V w (diskRotation θ u) := by
  change weakJacobiRightCLM V w (angularAverage u) = _
  unfold angularAverage
  rw [ContinuousLinearMap.map_smul_of_tower]
  congr 1
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _
    (intervalIntegrable_diskRotation u 0 (2 * Real.pi))]
  rfl

/-- Rotation moves from the test slot onto the left argument inverted. -/
lemma surfaceJacobi_rotation_right (k : ℕ) (θ : ℝ) (w u : ComplexH1) :
    weakJacobi (surfacePotential k) w (diskRotation θ u) =
      weakJacobi (surfacePotential k) (diskRotation (-θ) w) u := by
  have he : diskRotation θ (diskRotation (-θ) w) = w := by
    rw [← diskRotation_add, add_neg_cancel, diskRotation_zero]
  have h := surfaceJacobi_diskRotation k θ (diskRotation (-θ) w) u
  rw [he] at h
  exact h

/-! ### `P₀ ∘ jext = 0` -/

/-- A boundary L² function with vanishing Fourier coefficients vanishes. -/
lemma circleL2_eq_zero_of_coefficients {g : Lp ℂ 2 circleMeasure}
    (h : ∀ m : ℤ, circleFourierCoeff g m = 0) : g = 0 := by
  apply circleFourierCLE.injective
  rw [map_zero]
  apply lp.ext
  funext m
  rw [lp.coeFn_zero, Pi.zero_apply, circleFourierCLE_apply]
  exact h m

/-- For `k ≥ 2`, the normalized Jacobi extension of mean-zero half-order
boundary data has zero angular average ([ksindexi] tex 2250–2267). -/
theorem angularAverage_jacobiExtension {k : ℕ} (hk : 2 ≤ k)
    (f : dotted (1 / 2 : ℝ)) :
    angularAverage (jacobiExtensionCLM hk f) = 0 := by
  have hc0 : circleCoefficientCLM 0 (diskTraceCLM (jacobiExtensionCLM hk f)) = 0 := by
    have ht : toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        (halfDiskTraceCLM (jacobiExtensionCLM hk f)) =
          diskTraceCLM (jacobiExtensionCLM hk f) :=
      DFunLike.congr_fun toL2_comp_halfDiskTraceCLM _
    rw [jacobiExtensionCLM_halfTrace] at ht
    rw [circleCoefficientCLM_apply, ← ht, fourierCoeff_toL2]
    exact (mem_dotted _ f.val).mp f.property
  have hz : ∀ v : ComplexH1,
      (v ∈ zeroTraceDomain Set.univ ∨ ∃ c : ℂ, diskTraceCLM v = c • circleOneL2) →
      weakJacobi (surfacePotential k)
        (angularAverage (jacobiExtensionCLM hk f)) v = 0 := by
    intro v hv
    rw [← weakJacobi_conj, weakJacobi_angularAverage_right]
    have hzero : ∀ θ : ℝ, weakJacobi (surfacePotential k) v
        (diskRotation θ (jacobiExtensionCLM hk f)) = 0 := by
      intro θ
      rw [surfaceJacobi_rotation_right, ← weakJacobi_conj]
      rcases hv with hv | ⟨c, hc⟩
      · rw [jacobiExtensionCLM_weak_zeroTrace hk f _
          (diskRotation_mem_fullZeroTrace (-θ) v hv), map_zero]
      · rw [jacobiExtensionCLM_constantTrace hk f _
          ⟨c, diskRotation_constantTrace (-θ) hc⟩, map_zero]
    simp only [hzero]
    rw [intervalIntegral.integral_zero, smul_zero, map_zero]
  apply normalizedJacobi_zero_of_trace_zero hk
  · apply circleL2_eq_zero_of_coefficients
    intro m
    have h := circleCoefficient_trace_angularAverage m (jacobiExtensionCLM hk f)
    rw [hc0] at h
    rw [← circleCoefficientCLM_apply, h, ite_self]
  · intro v hv
    exact hz v (Or.inl hv)
  · intro v hv
    exact hz v (Or.inr hv)

/-! ### Membership in the zero-mean domain -/

/-- Class-zero elements have class-zero half-order traces. -/
lemma halfDiskTrace_mem_character_zero {k : ℕ} (hk : 0 < k) {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) 1) :
    halfDiskTraceCLM u ∈ character (1 / 2 : ℝ) ((0 : ℕ) : ℤ) (k : ℤ) := by
  rw [mem_character_iff_rotationCLM (1 / 2 : ℝ) k hk,
    show KsIndex.FormIndex.zeta k ^ ((0 : ℕ) : ℤ) = 1 by simp, one_smul]
  apply toL2_injective (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [toL2_rotationCLM]
  have ht : toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (halfDiskTraceCLM u) =
      diskTraceCLM u := DFunLike.congr_fun toL2_comp_halfDiskTraceCLM u
  rw [ht, trace_character hu, one_smul]

/-- The Jacobi extension of class-zero mean-zero data lies in the zero-mean
pure-Neumann class-zero domain. -/
theorem jacobiExtensionCLM_mem_zeroMeanDomain {k : ℕ} (hk : 2 ≤ k)
    (f : dotted (1 / 2 : ℝ))
    (hf : f.val ∈ character (1 / 2 : ℝ) ((0 : ℕ) : ℤ) (k : ℤ)) :
    jacobiExtensionCLM hk f ∈ zeroMeanDomain k := by
  rw [mem_zeroMeanDomain]
  refine ⟨angularAverage_jacobiExtension hk f, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩
  · exact Submodule.mem_inf.mpr
      ⟨(mem_naturalArcDomain k 1 true _).mpr (fun h => nomatch h),
        (mem_naturalArcDomain k 0 true _).mpr (fun h => nomatch h)⟩
  · exact jacobiExtensionH1_mem_character hk 0 f hf

/-! ### The Dirichlet decomposition of a zero-mean-domain element -/

/-- The decomposition boundary data of a zero-mean-domain element: its
half-order trace, bundled as mean-zero data (ZeroMeanTrace). -/
def zeroMeanTraceData {k : ℕ} (u : ComplexH1) (hu : u ∈ zeroMeanDomain k) :
    dotted (1 / 2 : ℝ) :=
  ⟨halfDiskTraceCLM u,
    halfDiskTrace_mem_dotted_of_angularAverage_eq_zero
      ((mem_zeroMeanDomain u).mp hu).1⟩

lemma zeroMeanTraceData_mem_character {k : ℕ} (hk : 2 ≤ k) (u : ComplexH1)
    (hu : u ∈ zeroMeanDomain k) :
    (zeroMeanTraceData u hu).val ∈
      character (1 / 2 : ℝ) ((0 : ℕ) : ℤ) (k : ℤ) := by
  apply halfDiskTrace_mem_character_zero (show 0 < k by omega)
  have hchar := (Submodule.mem_inf.mp ((mem_zeroMeanDomain u).mp hu).2).2
  rwa [pow_zero] at hchar

/-- The extension component of the decomposition stays in the domain. -/
theorem jacobiExtension_zeroMeanTraceData_mem {k : ℕ} (hk : 2 ≤ k)
    (u : ComplexH1) (hu : u ∈ zeroMeanDomain k) :
    jacobiExtensionCLM hk (zeroMeanTraceData u hu) ∈ zeroMeanDomain k :=
  jacobiExtensionCLM_mem_zeroMeanDomain hk _
    (zeroMeanTraceData_mem_character hk u hu)

/-- The remainder component of the decomposition stays in the domain. -/
theorem sub_jacobiExtension_mem_zeroMeanDomain {k : ℕ} (hk : 2 ≤ k)
    (u : ComplexH1) (hu : u ∈ zeroMeanDomain k) :
    u - jacobiExtensionCLM hk (zeroMeanTraceData u hu) ∈ zeroMeanDomain k :=
  Submodule.sub_mem _ hu (jacobiExtension_zeroMeanTraceData_mem hk u hu)

/-- The remainder has zero boundary trace (the paper's `H¹₀` component). -/
theorem diskTrace_sub_jacobiExtension {k : ℕ} (hk : 2 ≤ k) (u : ComplexH1)
    (hu : u ∈ zeroMeanDomain k) :
    diskTraceCLM (u - jacobiExtensionCLM hk (zeroMeanTraceData u hu)) = 0 := by
  rw [map_sub]
  have ht : toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (halfDiskTraceCLM (jacobiExtensionCLM hk (zeroMeanTraceData u hu))) =
        diskTraceCLM (jacobiExtensionCLM hk (zeroMeanTraceData u hu)) :=
    DFunLike.congr_fun toL2_comp_halfDiskTraceCLM _
  rw [jacobiExtensionCLM_halfTrace] at ht
  have hu' : toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (halfDiskTraceCLM u) =
      diskTraceCLM u := DFunLike.congr_fun toL2_comp_halfDiskTraceCLM u
  rw [show (zeroMeanTraceData u hu).val = halfDiskTraceCLM u from rfl, hu'] at ht
  rw [ht, sub_self]

/-- The remainder belongs to the full zero-boundary-trace test domain. -/
theorem sub_jacobiExtension_mem_fullZeroTrace {k : ℕ} (hk : 2 ≤ k)
    (u : ComplexH1) (hu : u ∈ zeroMeanDomain k) :
    u - jacobiExtensionCLM hk (zeroMeanTraceData u hu) ∈
      zeroTraceDomain Set.univ :=
  (mem_fullZeroTrace_iff _).mpr (diskTrace_sub_jacobiExtension hk u hu)

end KsIndex.Trace
