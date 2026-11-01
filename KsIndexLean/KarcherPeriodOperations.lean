module

public import KsIndexLean.ContourChainRepeat
public import KsIndexLean.KarcherPeriodIndex

@[expose] public section


/-! Real period laws for actual chain operations. Coefficient integrability is derived. -/
noncomputable section
namespace KsIndex.KarcherData
open Piecewise

lemma periodVector_identity (k : ℕ) (z : ℂ) :
    periodVector k (Chain.identity z) = 0 := by
  simp [periodVector]

lemma periodVector_append {k : ℕ} (hk : 2 ≤ k) (C D : Chain)
    (h : C.finish = D.start)
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z)
    (hD : ∀ z ∈ Surface.punctures k, D.Avoids z) :
    periodVector k (C.append D h) = periodVector k C + periodVector k D := by
  simp only [periodVector,
    Chain.append_contour _ _ _ (coeff1_chain_integrable hk C hC) (coeff1_chain_integrable hk D hD),
    Chain.append_contour _ _ _ (coeff2_chain_integrable hk C hC) (coeff2_chain_integrable hk D hD),
    Chain.append_contour _ _ _ (coeff3_chain_integrable hk C hC) (coeff3_chain_integrable hk D hD),
    Complex.add_re, Prod.mk_add_mk]

lemma periodVector_reverse {k : ℕ} (hk : 2 ≤ k) (C : Chain)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    periodVector k C.reverse = -periodVector k C := by
  simp only [periodVector,
    Chain.reverse_contour _ (coeff1_chain_integrable hk C hA),
    Chain.reverse_contour _ (coeff2_chain_integrable hk C hA),
    Chain.reverse_contour _ (coeff3_chain_integrable hk C hA), Complex.neg_re,
    Prod.neg_mk]

lemma periodVector_natRepeat {k : ℕ} (hk : 2 ≤ k) (C : Chain) (hc : C.IsClosed)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) (n : ℕ) :
    periodVector k (C.natRepeat hc n) = (n : ℝ) • periodVector k C := by
  simp only [periodVector,
    Chain.repeat_contour _ hc (coeff1_chain_integrable hk C hA),
    Chain.repeat_contour _ hc (coeff2_chain_integrable hk C hA),
    Chain.repeat_contour _ hc (coeff3_chain_integrable hk C hA)]
  simp [Complex.mul_re, Prod.smul_mk, smul_eq_mul]

end KsIndex.KarcherData
