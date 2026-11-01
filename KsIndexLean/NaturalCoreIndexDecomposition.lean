module

public import KsIndexLean.NaturalCoreSesq
public import KsIndexLean.D5DensityAssembly
public import KsIndexLean.SeamLowerConj
public import KsIndexLean.CapstoneM2

@[expose] public section


/-! The unrestricted natural-core index is the sum of its rotation-character indices. -/
noncomputable section
namespace KsIndex.Trace
open KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.FormIndex
  KsIndex.Surface KsIndex.SurfaceSym

theorem natCc_index_eq_sum {k : ℕ} (hk : 2 ≤ k) (b1 b0 : Bool) :
    formIndex (Qd k) (NatCc k b1 b0) = ∑ r : Fin k, seamNat k b1 b0 r := by
  exact formIndex_eq_sum_eigen (rot1 (rotUnit k : ℂ)) (natCc_sesq hk b1 b0)
    (by omega) (fun u _ => rot1_pow_k_eq_id (by omega) u)
    (fun u hu => rot1_mem_natCc_same (rotUnit_norm_one k) (rotUnit_pow (by omega)) hu)
    (fun u hu v hv => Bd_rot1 (rotUnit_norm_one k) hu.1 hv.1)

theorem natCc_dirichlet_index {k : ℕ} (hk : 3 ≤ k) :
    formIndex (Qd k) (NatCc k false false) = 0 := by
  rw [natCc_index_eq_sum (by omega)]
  simp only [Capstone.seamNat_FF hk, Finset.sum_const_zero]

theorem natCc_neumann_index {k : ℕ} (hk : 3 ≤ k) :
    formIndex (Qd k) (NatCc k true true) = (2 * k - 3 : ℕ) := by
  rw [natCc_index_eq_sum (by omega)]
  simp_rw [Capstone.seamNat_TT_eq hk (r := _) (Fin.isLt _)]
  rw [← Nat.cast_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (Capstone.ttVal k) k, Capstone.sum_ttVal hk]

end KsIndex.Trace
