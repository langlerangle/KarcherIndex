module

public import KsIndexLean.KarcherNeumannCoreCharacter
public import KsIndexLean.KarcherHalfPeriodIntegralForm
public import KsIndexLean.OpenSetCompactSupport

@[expose] public section


/-! Linear spaces of actual compact Neumann test fields and their geometric
rotation characters. Open-disk restriction forgets only boundary data. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SingleDisk KsIndex.FormIndex
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The canonical coordinate extension is linear on actual fields. -/
def halfPeriodCoordinateLM (R : PaperHalfPeriodRealization k) :
    (PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun := R.halfPeriodCoordinate
  map_add' f g := funext (R.halfPeriodCoordinate_add f g)
  map_smul' a f := funext (R.halfPeriodCoordinate_smul a f)

lemma isNeumannTest_zero (R : PaperHalfPeriodRealization k) :
    R.IsNeumannTest 0 := by
  have hz : R.halfPeriodCoordinate 0 = 0 := (R.halfPeriodCoordinateLM).map_zero
  refine ⟨continuous_const,by simp [HasCompactSupport],?_,?_⟩
  · rw [hz]
    exact contDiffOn_const
  · intro w hw
    refine ⟨0,contDiffAt_const,Filter.Eventually.of_forall (fun z hn => ?_)⟩
    rw [hz]

lemma IsNeumannTest.add {R : PaperHalfPeriodRealization k}
    {f g : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    (hf : R.IsNeumannTest f) (hg : R.IsNeumannTest g) : R.IsNeumannTest (f+g) := by
  have he : R.halfPeriodCoordinate (f+g) = R.halfPeriodCoordinate f + R.halfPeriodCoordinate g :=
    (R.halfPeriodCoordinateLM).map_add f g
  refine ⟨hf.1.add hg.1,hf.2.1.add hg.2.1,?_,?_⟩
  · rw [he]
    exact hf.2.2.1.add hg.2.2.1
  · intro w hw
    obtain ⟨F,hF,hfe⟩ := hf.2.2.2 w hw
    obtain ⟨G,hG,hge⟩ := hg.2.2.2 w hw
    refine ⟨F+G,hF.add hG,?_⟩
    filter_upwards [hfe,hge] with z hz hz' hn
    rw [he,Pi.add_apply,hz hn,hz' hn]
    rfl

lemma IsNeumannTest.smul {R : PaperHalfPeriodRealization k}
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    (hf : R.IsNeumannTest f) (a : ℂ) : R.IsNeumannTest (a • f) := by
  have he : R.halfPeriodCoordinate (a • f) = a • R.halfPeriodCoordinate f :=
    (R.halfPeriodCoordinateLM).map_smul a f
  refine ⟨continuous_const.smul hf.1,hf.2.1.smul_left,?_,?_⟩
  · rw [he]
    exact contDiffOn_const.smul hf.2.2.1
  · intro w hw
    obtain ⟨F,hF,hfe⟩ := hf.2.2.2 w hw
    refine ⟨a • F,contDiffAt_const.smul hF,?_⟩
    filter_upwards [hfe] with z hz hn
    rw [he,Pi.smul_apply,hz hn]
    rfl

/-- Actual compact smooth Neumann test fields; no PDE or normal derivative
condition is part of this domain. -/
def neumannTests (R : PaperHalfPeriodRealization k) :
    Submodule ℂ (PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) where
  carrier := {f | R.IsNeumannTest f}
  zero_mem' := R.isNeumannTest_zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun a _ hf => hf.smul a

/-- Pointwise character under the actual geometric rotation. -/
def halfPeriodTestCharacter (R : PaperHalfPeriodRealization k) (j : ℕ) :
    Submodule ℂ (PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) where
  carrier := {f | ∀ q, f (R.halfPeriodRotation q) = zeta k ^ j * f q}
  zero_mem' := by intro q; simp
  add_mem' := by
    intro f g hf hg q
    change f (R.halfPeriodRotation q) + g (R.halfPeriodRotation q) =
      zeta k ^ j * (f q + g q)
    rw [hf,hg,mul_add]
  smul_mem' := by
    intro a f hf q
    change a * f (R.halfPeriodRotation q) = zeta k ^ j * (a * f q)
    rw [hf]
    ring

def neumannCharacterTests (R : PaperHalfPeriodRealization k) (j : ℕ) :=
  R.neumannTests ⊓ R.halfPeriodTestCharacter j

/-- Coordinate restriction to the open disk is a linear map on actual fields. -/
def halfPeriodInteriorLM (R : PaperHalfPeriodRealization k) :
    (PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) →ₗ[ℂ] (disk → ℂ) where
  toFun f z := R.halfPeriodCoordinate f z.val
  map_add' f g := funext (fun z => R.halfPeriodCoordinate_add f g z.val)
  map_smul' a f := funext (fun z => R.halfPeriodCoordinate_smul a f z.val)

lemma halfPeriodCoordinate_mem_Erot1 (R : PaperHalfPeriodRealization k) (j : ℕ)
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    (hf : f ∈ R.halfPeriodTestCharacter j) : R.halfPeriodCoordinate f ∈ Erot1 k j := by
  let a : ℂ := (SurfaceSym.rotUnit k : Circle)
  have ha : ‖a‖ = 1 := Circle.norm_coe _
  have ha2 : a ^ (2*k) = 1 := by
    rw [Nat.mul_comm 2 k,pow_mul,SurfaceSym.rotUnit_pow (by have := h.out; omega),one_pow]
  have hp (z : ℂ) : a*z ∈ punctures k ↔ z ∈ punctures k := by
    change (a*z)^(2*k) = -1 ↔ z^(2*k) = -1
    rw [mul_pow,ha2,one_mul]
  apply Module.End.mem_eigenspace_iff.mpr
  funext z
  change R.halfPeriodCoordinate f (a*z) = zeta k ^ j * R.halfPeriodCoordinate f z
  by_cases hz : ‖z‖ ≤ 1 ∧ z ∉ punctures k
  · have hr : a*z = Trace.planeRotation (-(2*Real.pi)/k) z := by
      simp only [a,SurfaceSym.rotUnit,Circle.coe_exp,Trace.planeRotation_apply]
    rw [hr]
    have he := R.halfPeriodCoordinate_rotation f (⟨⟨z,hz.2⟩,hz.1⟩ : PuncturedClosedDisk k)
    exact he.trans ((hf _).trans (congrArg (fun v => zeta k ^ j * v)
      (R.halfPeriodCoordinate_apply f ⟨⟨z,hz.2⟩,hz.1⟩).symm))
  · have haz : ¬ (‖a*z‖ ≤ 1 ∧ a*z ∉ punctures k) := by
      simpa only [norm_mul,ha,one_mul,hp] using hz
    simp only [halfPeriodCoordinate,dite_eq_right hz,dite_eq_right haz,mul_zero]

lemma neumannCharacter_coordinate_mem (R : PaperHalfPeriodRealization k) (j : ℕ)
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    (hf : f ∈ R.neumannCharacterTests j) :
    R.halfPeriodCoordinate f ∈ NatCc k true true ⊓ Erot1 k j :=
  ⟨R.neumannTest_to_nat hf.1,R.halfPeriodCoordinate_mem_Erot1 j hf.2⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
