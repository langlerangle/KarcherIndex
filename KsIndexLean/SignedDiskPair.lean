module

public import KsIndexLean.SphericalReflectionDomains
public import KsIndexLean.SingleDisk

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

lemma trace_eq_signed_iff (A : Set Circle₁) (b : Bool) (u : ComplexH1) :
    arcTrace A u = sgn b • arcTrace A u ↔
      u ∈ (if b then ⊤ else zeroTraceDomain A) := by
  cases b
  · change arcTrace A u = (-1 : ℂ) • arcTrace A u ↔ arcTrace A u = 0
    rw [neg_one_smul]
    constructor
    · intro h
      have hz : (2 : ℂ) • arcTrace A u = 0 := by
        calc
          _ = arcTrace A u + arcTrace A u := two_smul ℂ (arcTrace A u)
          _ = -arcTrace A u + arcTrace A u := congrArg (fun x => x + arcTrace A u) h
          _ = 0 := neg_add_cancel _
      exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
    · intro h
      rw [h, neg_zero]
  · simp

def signedDiskPair (b : Bool) (u : ComplexH1) : DiskPairH1 := (u, sgn b • u)

lemma signedDiskPair_mem_slit_iff (k : ℕ) (b1 b0 : Bool) (u : ComplexH1) :
    signedDiskPair b1 u ∈ slitTraceDomain k (sgn b1 * sgn b0) ↔
      u ∈ mixedTraceDomain k b1 b0 := by
  rw [mem_slitTraceDomain]
  change (arcTrace (boundaryArc k 1) u = arcTrace (boundaryArc k 1) (sgn b1 • u) ∧
    arcTrace (boundaryArc k 0) u = (sgn b1 * sgn b0) •
      arcTrace (boundaryArc k 0) (sgn b1 • u)) ↔ _
  rw [map_smul, map_smul, smul_smul]
  have hs : (sgn b1 * sgn b0) * sgn b1 = sgn b0 := by
    calc
      _ = (sgn b1 * sgn b1) * sgn b0 := by ring
      _ = sgn b0 := by rw [sgn_mul_sgn, one_mul]
  rw [hs]
  exact and_congr (trace_eq_signed_iff _ b1 u) (trace_eq_signed_iff _ b0 u)

lemma signedDiskPair_norm (b : Bool) (u : ComplexH1) : ‖signedDiskPair b u‖ = ‖u‖ := by
  change max ‖u‖ ‖sgn b • u‖ = ‖u‖
  rw [norm_smul, norm_sgn, one_mul, max_self]

lemma signedDiskPair_add (b : Bool) (u v : ComplexH1) :
    signedDiskPair b (u + v) = signedDiskPair b u + signedDiskPair b v := by
  ext <;> simp [signedDiskPair, smul_add]

lemma signedDiskPair_smul (b : Bool) (a : ℂ) (u : ComplexH1) :
    signedDiskPair b (a • u) = a • signedDiskPair b u := by
  ext <;> simp [signedDiskPair, smul_comm (sgn b) a]

end KsIndex.Trace
