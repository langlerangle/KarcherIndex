module

public import KsIndexLean.AlphaEnergy8192Samples
public import KsIndexLean.AlphaQTailEnclosure

@[expose] public section


/-! Short rational endpoint enclosures for the four energy tails. -/
namespace KsIndex.AlphaRemarkTrial.Energy8192Tail
open PowerArc
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
lemma recenter {x a e c R : ℝ} (h : |x-a| ≤ e) (hb : e+|a-c| ≤ R) :
    |x-c| ≤ R := (abs_sub_le x a c).trans ((add_le_add h (le_refl _)).trans hb)

namespace Pplus
def point (i : Fin 25) : ℝ := (16386 : ℝ) + (1 : ℝ)*(shift i : ℝ)
noncomputable def center : Fin 25 → ℝ := ![(-2070637937/5000000000000000 : ℝ),
  (-5130485867/10000000000000000 : ℝ),
  (165679989/400000000000000 : ℝ),
  (1282845669/2500000000000000 : ℝ),
  (-258920237/625000000000000 : ℝ),
  (-5132279753/10000000000000000 : ℝ),
  (2566588547/5000000000000000 : ℝ),
  (-4144172569/10000000000000000 : ℝ),
  (-5134074703/10000000000000000 : ℝ),
  (3238201/7812500000000 : ℝ),
  (2567486289/5000000000000000 : ℝ),
  (-64775347/156250000000000 : ℝ),
  (-1470025403/10000000000000000 : ℝ),
  (-1186806707/10000000000000000 : ℝ),
  (183788327/1250000000000000 : ℝ),
  (237406751/2000000000000000 : ℝ),
  (-1470587919/10000000000000000 : ℝ),
  (-9498087/80000000000000 : ℝ),
  (367717327/2500000000000000 : ℝ),
  (237497613/2000000000000000 : ℝ),
  (-367787697/2500000000000000 : ℝ),
  (-4639513/39062500000000 : ℝ),
  (1471432353/10000000000000000 : ℝ),
  (59397133/500000000000000 : ℝ),
  (-1471714009/10000000000000000 : ℝ)]
noncomputable def radius (_ : Fin 25) : ℝ := (11/1000000000000000 : ℝ)
theorem radius_nonneg (i : Fin 25) : 0 ≤ radius i := by norm_num [radius]
theorem point_ge (i : Fin 25) : 1 ≤ point i := by fin_cases i <;> norm_num [point, shift]
theorem endpoint_interval (i : Fin 25) :
    |g (exponent i) (point i)/g (exponent i) 0-center i| ≤ radius i := by
  fin_cases i
  · have h := recenter (c := (-2070637937/5000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16392 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-5130485867/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16391 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (165679989/400000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16390 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (1282845669/2500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16389 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-258920237/625000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16388 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-5132279753/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16387 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (2566588547/5000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16385 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-4144172569/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16384 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-5134074703/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16383 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (3238201/7812500000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16382 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (2567486289/5000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16381 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-64775347/156250000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16380 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1470025403/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16392 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1186806707/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16391 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (183788327/1250000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16390 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (237406751/2000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16389 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1470587919/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16388 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-9498087/80000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16387 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (367717327/2500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16386 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (237497613/2000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16385 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-367787697/2500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16384 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-4639513/39062500000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16383 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (1471432353/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16382 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (59397133/500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16381 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1471714009/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16380 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
end Pplus
namespace Pminus
def point (i : Fin 25) : ℝ := (16386 : ℝ) + (-1 : ℝ)*(shift i : ℝ)
noncomputable def center : Fin 25 → ℝ := ![(-64775347/156250000000000 : ℝ),
  (2567486289/5000000000000000 : ℝ),
  (3238201/7812500000000 : ℝ),
  (-5134074703/10000000000000000 : ℝ),
  (-4144172569/10000000000000000 : ℝ),
  (2566588547/5000000000000000 : ℝ),
  (-5132279753/10000000000000000 : ℝ),
  (-258920237/625000000000000 : ℝ),
  (1282845669/2500000000000000 : ℝ),
  (165679989/400000000000000 : ℝ),
  (-5130485867/10000000000000000 : ℝ),
  (-2070637937/5000000000000000 : ℝ),
  (-1471714009/10000000000000000 : ℝ),
  (59397133/500000000000000 : ℝ),
  (1471432353/10000000000000000 : ℝ),
  (-4639513/39062500000000 : ℝ),
  (-367787697/2500000000000000 : ℝ),
  (237497613/2000000000000000 : ℝ),
  (367717327/2500000000000000 : ℝ),
  (-9498087/80000000000000 : ℝ),
  (-1470587919/10000000000000000 : ℝ),
  (237406751/2000000000000000 : ℝ),
  (183788327/1250000000000000 : ℝ),
  (-1186806707/10000000000000000 : ℝ),
  (-1470025403/10000000000000000 : ℝ)]
noncomputable def radius (_ : Fin 25) : ℝ := (11/1000000000000000 : ℝ)
theorem radius_nonneg (i : Fin 25) : 0 ≤ radius i := by norm_num [radius]
theorem point_ge (i : Fin 25) : 1 ≤ point i := by fin_cases i <;> norm_num [point, shift]
theorem endpoint_interval (i : Fin 25) :
    |g (exponent i) (point i)/g (exponent i) 0-center i| ≤ radius i := by
  fin_cases i
  · have h := recenter (c := (-64775347/156250000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16380 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (2567486289/5000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16381 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (3238201/7812500000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16382 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-5134074703/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16383 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-4144172569/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16384 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (2566588547/5000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16385 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-5132279753/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16387 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-258920237/625000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16388 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (1282845669/2500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16389 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (165679989/400000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16390 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-5130485867/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16391 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-2070637937/5000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16392 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1471714009/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16380 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (59397133/500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16381 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (1471432353/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16382 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-4639513/39062500000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16383 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-367787697/2500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16384 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (237497613/2000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16385 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (367717327/2500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16386 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-9498087/80000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16387 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1470587919/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16388 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (237406751/2000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16389 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (183788327/1250000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16390 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1186806707/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16391 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1470025403/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16392 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
end Pminus
namespace Mplus
def point (i : Fin 25) : ℝ := (16387 : ℝ) + (1 : ℝ)*(shift i : ℝ)
noncomputable def center : Fin 25 → ℝ := ![(5129589323/10000000000000000 : ℝ),
  (-2070637937/5000000000000000 : ℝ),
  (-5130485867/10000000000000000 : ℝ),
  (165679989/400000000000000 : ℝ),
  (1282845669/2500000000000000 : ℝ),
  (-258920237/625000000000000 : ℝ),
  (517931009/1250000000000000 : ℝ),
  (2566588547/5000000000000000 : ℝ),
  (-4144172569/10000000000000000 : ℝ),
  (-5134074703/10000000000000000 : ℝ),
  (3238201/7812500000000 : ℝ),
  (2567486289/5000000000000000 : ℝ),
  (1186579729/10000000000000000 : ℝ),
  (-1470025403/10000000000000000 : ℝ),
  (-1186806707/10000000000000000 : ℝ),
  (183788327/1250000000000000 : ℝ),
  (237406751/2000000000000000 : ℝ),
  (-1470587919/10000000000000000 : ℝ),
  (-9498087/80000000000000 : ℝ),
  (367717327/2500000000000000 : ℝ),
  (237497613/2000000000000000 : ℝ),
  (-367787697/2500000000000000 : ℝ),
  (-4639513/39062500000000 : ℝ),
  (1471432353/10000000000000000 : ℝ),
  (59397133/500000000000000 : ℝ)]
noncomputable def radius (_ : Fin 25) : ℝ := (11/1000000000000000 : ℝ)
theorem radius_nonneg (i : Fin 25) : 0 ≤ radius i := by norm_num [radius]
theorem point_ge (i : Fin 25) : 1 ≤ point i := by fin_cases i <;> norm_num [point, shift]
theorem endpoint_interval (i : Fin 25) :
    |g (exponent i) (point i)/g (exponent i) 0-center i| ≤ radius i := by
  fin_cases i
  · have h := recenter (c := (5129589323/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16393 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-2070637937/5000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16392 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-5130485867/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16391 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (165679989/400000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16390 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (1282845669/2500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16389 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-258920237/625000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16388 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (517931009/1250000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16386 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (2566588547/5000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16385 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-4144172569/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16384 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-5134074703/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16383 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (3238201/7812500000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16382 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (2567486289/5000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16381 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (1186579729/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16393 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1470025403/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16392 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1186806707/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16391 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (183788327/1250000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16390 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (237406751/2000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16389 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1470587919/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16388 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-9498087/80000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16387 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (367717327/2500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16386 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (237497613/2000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16385 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-367787697/2500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16384 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-4639513/39062500000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16383 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (1471432353/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16382 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (59397133/500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16381 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
end Mplus
namespace Mminus
def point (i : Fin 25) : ℝ := (16385 : ℝ) + (-1 : ℝ)*(shift i : ℝ)
noncomputable def center : Fin 25 → ℝ := ![(-4012399/7812500000000 : ℝ),
  (-64775347/156250000000000 : ℝ),
  (2567486289/5000000000000000 : ℝ),
  (3238201/7812500000000 : ℝ),
  (-5134074703/10000000000000000 : ℝ),
  (-4144172569/10000000000000000 : ℝ),
  (517931009/1250000000000000 : ℝ),
  (-5132279753/10000000000000000 : ℝ),
  (-258920237/625000000000000 : ℝ),
  (1282845669/2500000000000000 : ℝ),
  (165679989/400000000000000 : ℝ),
  (-5130485867/10000000000000000 : ℝ),
  (-237634013/2000000000000000 : ℝ),
  (-1471714009/10000000000000000 : ℝ),
  (59397133/500000000000000 : ℝ),
  (1471432353/10000000000000000 : ℝ),
  (-4639513/39062500000000 : ℝ),
  (-367787697/2500000000000000 : ℝ),
  (237497613/2000000000000000 : ℝ),
  (367717327/2500000000000000 : ℝ),
  (-9498087/80000000000000 : ℝ),
  (-1470587919/10000000000000000 : ℝ),
  (237406751/2000000000000000 : ℝ),
  (183788327/1250000000000000 : ℝ),
  (-1186806707/10000000000000000 : ℝ)]
noncomputable def radius (_ : Fin 25) : ℝ := (11/1000000000000000 : ℝ)
theorem radius_nonneg (i : Fin 25) : 0 ≤ radius i := by norm_num [radius]
theorem point_ge (i : Fin 25) : 1 ≤ point i := by fin_cases i <;> norm_num [point, shift]
theorem endpoint_interval (i : Fin 25) :
    |g (exponent i) (point i)/g (exponent i) 0-center i| ≤ radius i := by
  fin_cases i
  · have h := recenter (c := (-4012399/7812500000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16379 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-64775347/156250000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16380 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (2567486289/5000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16381 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (3238201/7812500000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16382 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-5134074703/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16383 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-4144172569/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16384 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (517931009/1250000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16386 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-5132279753/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16387 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-258920237/625000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16388 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (1282845669/2500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16389 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (165679989/400000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16390 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-5130485867/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_b_16391 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-237634013/2000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16379 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1471714009/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16380 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (59397133/500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16381 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (1471432353/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16382 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-4639513/39062500000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16383 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-367787697/2500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16384 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (237497613/2000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16385 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (367717327/2500000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16386 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-9498087/80000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16387 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1470587919/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16388 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (237406751/2000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16389 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (183788327/1250000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16390 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
  · have h := recenter (c := (-1186806707/10000000000000000 : ℝ)) (R := (11/1000000000000000 : ℝ))
      energy8192_sample_c_16391 (by norm_num)
    norm_num [exponent, point, shift, center, radius] at h ⊢
    exact h
end Mminus
end KsIndex.AlphaRemarkTrial.Energy8192Tail
