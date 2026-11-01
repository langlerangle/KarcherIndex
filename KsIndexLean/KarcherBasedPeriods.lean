module

public import KsIndexLean.KarcherLiftCovering

@[expose] public section


/-! Prescribed-basepoint periods and realization of every real integral lift.
The statements specify avoiding chains and their path integrals; continuity
of lifted paths is a separate assertion. -/
noncomputable section
namespace KsIndex.KarcherData
open Piecewise

/-- Every integral vertical period is realized by an actual avoiding loop at
 any prescribed finite parameter point. -/
theorem exists_based_integer_period {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) (n : ℤ) :
    ∃ L : Chain, L.start = b.val ∧ L.finish = b.val ∧
      (∀ z ∈ Surface.punctures k, L.Avoids z) ∧
      periodVector k L = (0, 0, (2 * Real.pi) * (n : ℝ)) := by
  obtain ⟨C, hc, hC, hp⟩ := exists_integer_period hk n
  have hb : C.start ∉ Surface.punctures k := fun hz => C.start_ne (hC _ hz) rfl
  obtain ⟨D, hs, ht, hD⟩ := exists_connecting_chain hk b.property hb
  let A := D.append C ht
  have hA : ∀ z ∈ Surface.punctures k, A.Avoids z :=
    fun z hz => D.append_avoids C ht (hD z hz) (hC z hz)
  have hj : A.finish = D.reverse.start := by
    simp only [A, Chain.append_finish, Chain.reverse_start]
    exact hc.trans ht.symm
  refine ⟨A.append D.reverse hj, ?_, ?_, ?_, ?_⟩
  · simpa only [Chain.append_start, A] using hs
  · simpa only [Chain.append_finish, Chain.reverse_finish] using hs
  · exact fun z hz => A.append_avoids D.reverse hj (hA z hz) (D.reverse_avoids (hD z hz))
  · rw [periodVector_append hk A D.reverse hj hA (fun z hz => D.reverse_avoids (hD z hz)),
      periodVector_reverse hk D hD]
    change periodVector k (D.append C ht) + -periodVector k D = _
    rw [periodVector_append hk D C ht hD hC, hp]
    abel

/-- Equality modulo the vertical period is exactly an integral vertical difference. -/
lemma projectPeriod_eq_iff_sub_lattice (p q : AmbientTriple) :
    projectPeriod p = projectPeriod q ↔
      ∃ n : ℤ, p - q = (0, 0, (2 * Real.pi) * (n : ℝ)) := by
  constructor
  · intro he
    have hx := congrArg Prod.fst he
    have hy := congrArg (fun t : PeriodTarget => t.2.1) he
    have hz := congrArg (fun t : PeriodTarget => t.2.2) he
    have hzero : ((p.2.2 - q.2.2 : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
      rw [AddCircle.coe_sub]
      exact sub_eq_zero.mpr hz
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).mp hzero
    rw [zsmul_eq_mul, mul_comm] at hn
    refine ⟨n, ?_⟩
    exact Prod.ext (sub_eq_zero.mpr hx) (Prod.ext (sub_eq_zero.mpr hy) hn.symm)
  · rintro ⟨n, hn⟩
    exact projectPeriod_eq_of_sub_lattice hn

/-- Any real lift of the descended integral is realized by an actual avoiding
 chain with the prescribed endpoints; adding a based period selects its sheet. -/
theorem exists_chain_with_real_integral {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (v : AmbientTriple)
    (hv : projectPeriod v = descendedIntegral hk b w) :
    ∃ D : Chain, D.start = b.val ∧ D.finish = w.val ∧
      (∀ z ∈ Surface.punctures k, D.Avoids z) ∧ periodVector k D = v := by
  obtain ⟨C, hs, ht, hC⟩ := exists_connecting_chain hk b.property w.property
  have he : projectPeriod v = projectPeriod (periodVector k C) :=
    hv.trans (descendedIntegral_eq hk b w C hs ht hC)
  obtain ⟨n, hn⟩ := (projectPeriod_eq_iff_sub_lattice v (periodVector k C)).mp he
  obtain ⟨L, hLs, hLt, hL, hLp⟩ := exists_based_integer_period hk b n
  have hj : L.finish = C.start := hLt.trans hs.symm
  refine ⟨L.append C hj, (Chain.append_start _ _ _).trans hLs,
    (Chain.append_finish _ _ _).trans ht,
    fun z hz => L.append_avoids C hj (hL z hz) (hC z hz), ?_⟩
  rw [periodVector_append hk L C hj hL hC, hLp, ← hn]
  abel

/-- Any two lifted points over the finite parameter chart admit a certified
 avoiding chain with exactly their real ambient displacement. Constructing a continuous
 path in the lift additionally requires continuity of partial integrals. -/
theorem exists_chain_between_finite_lifts {k : ℕ} (hk : 2 ≤ k)
    (base b w : PuncturedPlane k) (C : PeriodTarget)
    (q r : PeriodicEWCarrier hk base C)
    (hq : HeightLift.projection q = finiteParameter b)
    (hr : HeightLift.projection r = finiteParameter w) :
    ∃ D : Chain, D.start = b.val ∧ D.finish = w.val ∧
      (∀ z ∈ Surface.punctures k, D.Avoids z) ∧
      periodVector k D = HeightLift.ambient r - HeightLift.ambient q := by
  apply exists_chain_with_real_integral hk b w
  rw [projectPeriod_sub, HeightLift.project_ambient, HeightLift.project_ambient,
    hr, hq, extendedEWMap_finite, extendedEWMap_finite,
    descendedIntegral_basepoint hk base b w]
  abel

end KsIndex.KarcherData
