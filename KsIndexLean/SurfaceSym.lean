module

/-
# Rotation and copy-shift sectors of the disk-chain Jacobi form

On families `U : ZMod (2m) × ℂ → ℂ`, the two actions are precomposition by
`(n,w) ↦ (n,a*w)` with `a = exp(-2πi/k)`, and by `(n,w) ↦ (n+2,w)`.
The rotation preserves the smooth compactly supported disk-chain domain when
`a^k = 1`; the copy shift preserves it because the seam arcs have period two.
Both actions preserve the polarized Jacobi form, and they commute.

For `k ≥ 2` and `m ≠ 0`, `indSurface_eq_sum_sectors` decomposes the disk-chain
index into the sum over joint eigenspaces with eigenvalues `ζ_k^r` and `ζ_m^s`.
The proof applies the finite-order index decomposition twice, first to rotation
and then to the shift on each rotation eigenspace. The translation phases here
are the finite-quotient phases `α = s/m`; geometric and circle-form
identifications are supplied by separate interfaces.
-/
public import KsIndexLean.SurfaceForm
public import KsIndexLean.CharDecomp

@[expose] public section


noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped ContDiff

namespace KsIndex.SurfaceSym

open KsIndex.Surface KsIndex.GradOrtho KsIndex.ThetaOrtho KsIndex.SurfaceForm KsIndex.FormIndex

variable {k m : ℕ}

/-! ### The rotation -/

/-- Rotation of a family: `rotF a u n w = u n (a·w)`. -/
def rotF (a : ℂ) (u : ZMod (2 * m) → ℂ → ℂ) : ZMod (2 * m) → ℂ → ℂ := fun n w => u n (a * w)

/-- Rotation on uncurried test functions, as a linear endomorphism. -/
def rotE (m : ℕ) (a : ℂ) : Module.End ℂ (ZMod (2 * m) × ℂ → ℂ) where
  toFun U := fun p => U (p.1, a * p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma rotE_apply (a : ℂ) (U : ZMod (2 * m) × ℂ → ℂ) (p : ZMod (2 * m) × ℂ) :
    rotE m a U p = U (p.1, a * p.2) := rfl

lemma rotE_pow_apply (a : ℂ) (j : ℕ) (U : ZMod (2 * m) × ℂ → ℂ) (p : ZMod (2 * m) × ℂ) :
    ((rotE m a) ^ j) U p = U (p.1, a ^ j * p.2) := by
  induction j generalizing U p with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, rotE_apply, ih]
    simp only
    rw [pow_succ, mul_assoc]

lemma uncurry_symm_rotE (a : ℂ) (U : ZMod (2 * m) × ℂ → ℂ) :
    (uncurryE m).symm (rotE m a U) = rotF a ((uncurryE m).symm U) := rfl

/-- Rotation by a unit `a` with `a^k = 1` preserves `C_c^∞(Ξ_{k,m})`: it fixes the disk, the arc
families (`(a w)^k = w^k`), the punctures, and commutes with the seam gluing. -/
lemma rotF_mem_CcSmooth {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = 1)
    {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ CcSmooth k m) : rotF a u ∈ CcSmooth k m := by
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, ⟨ε, hε, hz⟩⟩ := hu
  have hmul : ContDiff ℝ ∞ (fun w : ℂ => a * w) := contDiff_const.mul contDiff_id
  have hnorm : ∀ w : ℂ, ‖a * w‖ = ‖w‖ := fun w => by rw [norm_mul, ha, one_mul]
  have hconj : ∀ w : ℂ, a * (1 / (starRingEnd ℂ) w) = 1 / (starRingEnd ℂ) (a * w) := by
    intro w
    have h1 : ((starRingEnd ℂ) a)⁻¹ = a :=
      inv_eq_of_mul_eq_one_right (by rw [Complex.conj_mul', ha]; norm_num)
    rw [map_mul, one_div, one_div, mul_inv, h1]
  refine ⟨⟨fun n => ?_, fun n w hw => ?_, fun n w hw => ?_⟩, ⟨ε, hε, fun n w hw => ?_⟩⟩
  · exact (hsm1 n).comp hmul.contDiffOn
      (fun w hw => by rw [mem_disk_iff, hnorm]; exact mem_disk_iff.mp hw)
  · have hglue : glue (rotF a u) n = fun w => glue u n (a * w) := by
      funext w
      simp only [glue, rotF, hnorm, hconj]
    rw [hglue]
    have hmem : a * w ∈ seamArc k m n := by
      obtain ⟨hw1, hw2⟩ := hw
      refine ⟨by rw [hnorm]; exact hw1, ?_⟩
      rw [mul_pow, hak, one_mul]; exact hw2
    exact (hsm2 n (a * w) hmem).comp w hmul.contDiffAt
  · exact hsm3 n (a * w) (by rw [hnorm]; exact hw)
  · obtain ⟨p, hp, hwp⟩ := hw
    refine hz n (a * w) ⟨a * p, ?_, ?_⟩
    · change (a * p) ^ (2 * k) = -1
      rw [mul_pow, pow_mul', hak, one_pow, one_mul]; exact hp
    · rw [← mul_sub, norm_mul, ha, one_mul]; exact hwp

/-! ### Rotation invariance of the polarized form -/

/-- The disk integral is invariant under rotation by a circle element. -/
lemma setIntegral_disk_comp_mul (a : Circle) (F : ℂ → ℂ) :
    ∫ w in disk, F ((a : ℂ) * w) = ∫ w in disk, F w := by
  have hmp : MeasurePreserving (rotation a) volume volume := (rotation a).measurePreserving
  have hemb : MeasurableEmbedding (rotation a) := (rotation a).toHomeomorph.measurableEmbedding
  have hpre : (rotation a) ⁻¹' disk = disk := by
    ext w
    simp only [Set.mem_preimage, rotation_apply, disk, Metric.mem_ball, dist_zero_right,
      norm_mul, Circle.norm_coe, one_mul]
  have h := hmp.setIntegral_preimage_emb hemb F disk
  rw [hpre] at h
  simpa only [rotation_apply] using h

lemma fderiv_comp_mul {f : ℂ → ℂ} {a w : ℂ} (hf : DifferentiableAt ℝ f (a * w)) (v : ℂ) :
    fderiv ℝ (fun z => f (a * z)) w v = fderiv ℝ f (a * w) (a * v) := by
  have hL : HasFDerivAt (fun z : ℂ => a * z) (a • ContinuousLinearMap.id ℝ ℂ) w := by
    have hfun : (fun z : ℂ => a * z) = ⇑(a • ContinuousLinearMap.id ℝ ℂ) := by
      funext z; simp [smul_eq_mul]
    rw [hfun]; exact (a • ContinuousLinearMap.id ℝ ℂ).hasFDerivAt
  have hcomp : HasFDerivAt (fun z => f (a * z))
      ((fderiv ℝ f (a * w)).comp (a • ContinuousLinearMap.id ℝ ℂ)) w :=
    hf.hasFDerivAt.comp w hL
  rw [hcomp.fderiv]
  simp [smul_eq_mul]

/-- The gradient cross density is rotation-equivariant (`basis_rot` from `GradOrtho`). -/
lemma gradInner_comp_mul {f g : ℂ → ℂ} {a : ℂ} (ha : ‖a‖ = 1) {w : ℂ}
    (hf : DifferentiableAt ℝ f (a * w)) (hg : DifferentiableAt ℝ g (a * w)) :
    gradInner (fun z => f (a * z)) (fun z => g (a * z)) w = gradInner f g (a * w) := by
  simp only [gradInner, fderiv_comp_mul hf, fderiv_comp_mul hg]
  exact (basis_rot (fderiv ℝ f (a * w)) (fderiv ℝ g (a * w)) ha).symm

/-- **Rotation invariance of the polarized Jacobi form on `C_c^∞`.** -/
lemma jacobiB_rotF [NeZero m] (a : Circle) {u v : ZMod (2 * m) → ℂ → ℂ}
    (hu : u ∈ CcSmooth k m) (hv : v ∈ CcSmooth k m) :
    jacobiB k m (rotF (a : ℂ) u) (rotF (a : ℂ) v) = jacobiB k m u v := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  unfold jacobiB
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 : ∫ w in disk, gradInner (rotF (a : ℂ) u n) (rotF (a : ℂ) v n) w
      = ∫ w in disk, gradInner (u n) (v n) w := by
    rw [← setIntegral_disk_comp_mul a (gradInner (u n) (v n))]
    refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    have haw : (a : ℂ) * w ∈ disk := by
      rw [mem_disk_iff, norm_mul, Circle.norm_coe, one_mul]; exact mem_disk_iff.mp hw
    exact gradInner_comp_mul (Circle.norm_coe a) (differentiableAt_of_mem hu n haw)
      (differentiableAt_of_mem hv n haw)
  have h2 : ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (rotF (a : ℂ) u n w) * rotF (a : ℂ) v n w
      = ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * v n w := by
    rw [← setIntegral_disk_comp_mul a
      (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * v n w)]
    refine setIntegral_congr_fun measurableSet_disk fun w _ => ?_
    simp only [rotF, potV_rotation k (Circle.norm_coe a)]
  rw [h1, h2]

/-! ### The shift -/

/-- Shift of a family by two copies: `shiftF u n = u (n + 2)`. -/
def shiftF (u : ZMod (2 * m) → ℂ → ℂ) : ZMod (2 * m) → ℂ → ℂ := fun n w => u (n + 2) w

/-- The shift on uncurried test functions, as a linear endomorphism. -/
def shiftE (m : ℕ) : Module.End ℂ (ZMod (2 * m) × ℂ → ℂ) where
  toFun U := fun p => U (p.1 + 2, p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma shiftE_apply (U : ZMod (2 * m) × ℂ → ℂ) (p : ZMod (2 * m) × ℂ) :
    shiftE m U p = U (p.1 + 2, p.2) := rfl

lemma shiftE_pow_apply (j : ℕ) (U : ZMod (2 * m) × ℂ → ℂ) (p : ZMod (2 * m) × ℂ) :
    ((shiftE m) ^ j) U p = U (p.1 + ((2 * j : ℕ) : ZMod (2 * m)), p.2) := by
  induction j generalizing U p with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, shiftE_apply, ih]
    simp only
    congr 1
    refine Prod.ext ?_ rfl
    simp only
    push_cast
    ring

lemma uncurry_symm_shiftE (U : ZMod (2 * m) × ℂ → ℂ) :
    (uncurryE m).symm (shiftE m U) = shiftF ((uncurryE m).symm U) := rfl

lemma parity_two (m : ℕ) : parity m 2 = 0 := by
  rw [map_ofNat]; decide

lemma seamArc_add_two (k m : ℕ) (n : ZMod (2 * m)) : seamArc k m (n + 2) = seamArc k m n := by
  unfold seamArc
  rw [add_right_comm, map_add, parity_two, add_zero]

/-- The shift preserves `C_c^∞(Ξ_{k,m})` (the seam arcs have period two in the copy index). -/
lemma shiftF_mem_CcSmooth {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ CcSmooth k m) :
    shiftF u ∈ CcSmooth k m := by
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, ⟨ε, hε, hz⟩⟩ := hu
  refine ⟨⟨fun n => hsm1 (n + 2), fun n w hw => ?_, fun n w hw => hsm3 (n + 2) w hw⟩,
    ⟨ε, hε, fun n w hw => hz (n + 2) w hw⟩⟩
  have hglue : glue (shiftF u) n = glue u (n + 2) := by
    funext w
    simp only [glue, shiftF, add_right_comm n 1 2]
  rw [hglue]
  exact hsm2 (n + 2) w (by rwa [seamArc_add_two])

/-- **Shift invariance of the polarized Jacobi form** (reindex the sum over copies). -/
lemma jacobiB_shiftF [NeZero m] (u v : ZMod (2 * m) → ℂ → ℂ) :
    jacobiB k m (shiftF u) (shiftF v) = jacobiB k m u v := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  unfold jacobiB
  exact Fintype.sum_equiv (Equiv.addRight (2 : ZMod (2 * m))) _ _ (fun n => rfl)

/-- The rotation and the shift commute. -/
lemma rotE_mul_shiftE (a : ℂ) : rotE m a * shiftE m = shiftE m * rotE m a :=
  LinearMap.ext fun _ => rfl

/-! ### Finite order, domain preservation, and form invariance -/

/-- `e^{−2πi/k}` as a circle element. -/
def rotUnit (k : ℕ) : Circle := Circle.exp (-(2 * π) / k)

lemma rotUnit_pow (hk : 0 < k) : ((rotUnit k : Circle) : ℂ) ^ k = 1 := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [rotUnit, Circle.coe_exp, ← Complex.exp_nat_mul]
  have : (k : ℂ) * (((-(2 * π) / k : ℝ) : ℂ) * I) = ((-1 : ℤ) : ℂ) * (2 * π * I) := by
    push_cast; field_simp
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

section receipts

lemma rot_pow_id (hk : 0 < k) (U : ZMod (2 * m) × ℂ → ℂ) :
    ((rotE m (rotUnit k : ℂ)) ^ k) U = U := by
  funext p
  rw [rotE_pow_apply, rotUnit_pow hk, one_mul]

lemma rot_mem_Dom (hk : 0 < k) {U : ZMod (2 * m) × ℂ → ℂ} (hU : U ∈ Dom k m) :
    rotE m (rotUnit k : ℂ) U ∈ Dom k m := by
  rw [mem_Dom] at hU ⊢
  rw [uncurry_symm_rotE]
  exact rotF_mem_CcSmooth (Circle.norm_coe _) (rotUnit_pow hk) hU

lemma rot_inv [NeZero m] {U V : ZMod (2 * m) × ℂ → ℂ} (hU : U ∈ Dom k m) (hV : V ∈ Dom k m) :
    Bs k m (rotE m (rotUnit k : ℂ) U) (rotE m (rotUnit k : ℂ) V) = Bs k m U V := by
  rw [mem_Dom] at hU hV
  simp only [Bs, uncurry_symm_rotE]
  exact jacobiB_rotF (rotUnit k) hU hV

lemma shift_pow_id (U : ZMod (2 * m) × ℂ → ℂ) : ((shiftE m) ^ m) U = U := by
  funext p
  rw [shiftE_pow_apply, ZMod.natCast_self, add_zero]

lemma shift_mem_Dom {U : ZMod (2 * m) × ℂ → ℂ} (hU : U ∈ Dom k m) : shiftE m U ∈ Dom k m := by
  rw [mem_Dom] at hU ⊢
  rw [uncurry_symm_shiftE]
  exact shiftF_mem_CcSmooth hU

lemma shift_inv [NeZero m] (U V : ZMod (2 * m) × ℂ → ℂ) :
    Bs k m (shiftE m U) (shiftE m V) = Bs k m U V := by
  simp only [Bs, uncurry_symm_shiftE]
  exact jacobiB_shiftF _ _

/-- The shift preserves every rotation eigenspace (the two actions commute). -/
lemma shift_mem_rotBlock {μ : ℂ} {U : ZMod (2 * m) × ℂ → ℂ}
    (hU : U ∈ Dom k m ⊓ Module.End.eigenspace (rotE m (rotUnit k : ℂ)) μ) :
    shiftE m U ∈ Dom k m ⊓ Module.End.eigenspace (rotE m (rotUnit k : ℂ)) μ := by
  obtain ⟨hD, hE⟩ := Submodule.mem_inf.mp hU
  rw [Module.End.mem_eigenspace_iff] at hE
  refine Submodule.mem_inf.mpr ⟨shift_mem_Dom hD, ?_⟩
  rw [Module.End.mem_eigenspace_iff, ← Module.End.mul_apply, rotE_mul_shiftE,
    Module.End.mul_apply, hE, map_smul]

end receipts

/-! ### The sector decomposition of the index -/

/-- For `k ≥ 2` and `m ≠ 0`, the disk-chain index splits over the joint rotation
and copy-shift eigenspaces. The shift eigenvalue `ζ_m^s` corresponds to the
finite-quotient phase `α = s/m`. -/
theorem indSurface_eq_sum_sectors [NeZero m] (hk : 2 ≤ k) :
    indSurface k m = ∑ r : Fin k, ∑ s : Fin m,
      formIndex (Qs k m)
        ((Dom k m ⊓ Module.End.eigenspace (rotE m (rotUnit k : ℂ)) (zeta k ^ (r : ℕ)))
          ⊓ Module.End.eigenspace (shiftE m) (zeta m ^ (s : ℕ))) := by
  have hS := sesq_surface (m := m) hk
  have hk0 : 0 < k := by omega
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [indSurface_eq,
    formIndex_eq_sum_eigen (rotE m (rotUnit k : ℂ)) hS hk0 (fun U _ => rot_pow_id hk0 U)
      (fun U hU => rot_mem_Dom hk0 hU) (fun U hU V hV => rot_inv hU hV)]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact formIndex_eq_sum_eigen (shiftE m) (hS.mono inf_le_left) hm0
    (fun U _ => shift_pow_id U) (fun U hU => shift_mem_rotBlock hU)
    (fun U hU V hV => shift_inv U V)

end KsIndex.SurfaceSym
