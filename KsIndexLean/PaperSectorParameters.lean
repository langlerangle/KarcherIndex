module

public import KsIndexLean.ChainSphereCharacterForms
public import KsIndexLean.SphericalPaperPhase

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

def paperPhase (α : ℝ) : ℂ := Complex.exp ((2 * Real.pi * α) * Complex.I)

/-- The repository root-of-unity convention equals the paper's Fourier character. -/
lemma paperCharacter_exp (k j : ℕ) :
    KsIndex.FormIndex.zeta k ^ j =
      Complex.exp (((2 * Real.pi * j / k : ℝ) : ℂ) * Complex.I) := by
  rw [KsIndex.FormIndex.zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma paperRationalPhase_root (m n : ℕ) [NeZero m] :
    (paperPhase ((n : ℝ) / m)) ^ m = 1 := by
  have he : paperPhase ((n : ℝ) / m) =
      KsIndex.FormIndex.zeta m ^ n := by
    rw [paperCharacter_exp]
    unfold paperPhase
    congr 1
    push_cast
    ring
  rw [he, ← pow_mul, Nat.mul_comm n m, pow_mul,
    KsIndex.FormIndex.zeta_pow_N (Nat.pos_of_ne_zero (NeZero.ne m)), one_pow]

abbrev PaperChainSector (m n j : ℕ) [NeZero m] :=
  chainPhaseCharacterDomain 3 m
    (paperPhase ((n : ℝ) / m))
    (-(2 * Real.pi) / 3) (paperRotation_root 3 (by omega)) (KsIndex.FormIndex.zeta 3 ^ j)

abbrev PaperSphereSector (α : ℝ) (j : ℕ) :=
  sphericalPhaseCharacterDomain 3 (paperPhase α)⁻¹
    (-(2 * Real.pi) / 3) (paperRotation_root 3 (by omega)) (KsIndex.FormIndex.zeta 3 ^ j)

/-- Explicit rational phase and Fourier sector specialization, in lower/upper chart order. -/
def paperRationalSectorEquiv (m n j : ℕ) [NeZero m] :
    PaperChainSector m n j ≃ₗᵢ[ℂ] PaperSphereSector ((n : ℝ) / m) j :=
  chainPhaseCharacterSphereLinearIsometryEquiv 3 m _ (paperRationalPhase_root m n)
    (-(2 * Real.pi) / 3) (paperRotation_root 3 (by omega)) (KsIndex.FormIndex.zeta 3 ^ j)

lemma paperRationalSector_jacobi (m n j : ℕ) [NeZero m] (V : BoundedRealPotential)
    (q r : PaperChainSector m n j) :
    chainChartJacobi 3 m V q.val.val r.val.val = (m : ℂ) *
      sphereChartJacobi (isOpen_boundaryArc 3 1) V
        (paperRationalSectorEquiv m n j q).val (paperRationalSectorEquiv m n j r).val :=
  chainPhaseCharacterSphere_jacobi 3 m _ (paperRationalPhase_root m n)
    (-(2 * Real.pi) / 3) (paperRotation_root 3 (by omega)) (KsIndex.FormIndex.zeta 3 ^ j) V q r

lemma paperSphereSector_upper (α : ℝ) (j : ℕ) (q : PaperSphereSector α j) :
    secondChartTrace (isOpen_boundaryArc 3 1) (boundaryArc 3 0) q.val =
      Complex.exp ((2 * Real.pi * α) * Complex.I) •
        firstChartTrace (isOpen_boundaryArc 3 1) (boundaryArc 3 0) q.val :=
  paperSphericalPhase_upper α ⟨q.val, q.property.1⟩

end KsIndex.Spherical
