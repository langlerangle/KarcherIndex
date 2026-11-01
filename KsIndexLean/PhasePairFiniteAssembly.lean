module

public import KsIndexLean.PhasePairLocalApproximation

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Value identities determine the finite H1 reconstruction; derivative
identities follow from the adopted weak-H1 carrier's injective value map. -/
lemma finite_carrier_reconstruction {ι : Type*} (t : Finset ι)
    (u u₀ : ComplexH1) (uB : ι → ComplexH1) (f₀ : ℂ → ℂ) (fB : ι → ℂ → ℂ)
    (h₀ : (valueCLM u₀ : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f₀)
    (hB : ∀ i ∈ t, (valueCLM (uB i) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] fB i)
    (hs : (fun z => f₀ z + ∑ i ∈ t, fB i z) =ᵐ[volume.restrict (disk : Set ℂ)]
      (valueCLM u : ℂ → ℂ)) : u₀ + ∑ i ∈ t, uB i = u := by
  apply valueCLM_injective
  apply Lp.ext
  rw [map_add, map_sum]
  have hall : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), ∀ i ∈ (↑t : Set ι),
      (valueCLM (uB i) : ℂ → ℂ) z = fB i z :=
    (ae_ball_iff t.countable_toSet).2 hB
  filter_upwards [Lp.coeFn_add (valueCLM u₀) (∑ i ∈ t, valueCLM (uB i)),
    Lp.coeFn_finsetSum t (fun i => valueCLM (uB i)), h₀, hall, hs]
    with z ha hb h0 hi hz
  simp only [ha, Pi.add_apply, hb, Finset.sum_apply, h0]
  rw [Finset.sum_congr rfl (fun i hit => hi i hit)]
  exact hz

/-- Finite local H1 approximations reconstruct the original disk function,
using the actual partition value identity, not an extra derivative partition. -/
theorem finite_carrier_tendsto {ι : Type*} (t : Finset ι)
    (u u₀ : ComplexH1) (uB : ι → ComplexH1) (f₀ : ℂ → ℂ) (fB : ι → ℂ → ℂ)
    (h₀ : (valueCLM u₀ : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f₀)
    (hB : ∀ i ∈ t, (valueCLM (uB i) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] fB i)
    (hs : (fun z => f₀ z + ∑ i ∈ t, fB i z) =ᵐ[volume.restrict (disk : Set ℂ)]
      (valueCLM u : ℂ → ℂ))
    (U₀ : ℕ → ComplexH1) (UB : ι → ℕ → ComplexH1)
    (ht₀ : Tendsto U₀ atTop (𝓝 u₀)) (htB : ∀ i ∈ t, Tendsto (UB i) atTop (𝓝 (uB i))) :
    Tendsto (fun n => U₀ n + ∑ i ∈ t, UB i n) atTop (𝓝 u) := by
  rw [← finite_carrier_reconstruction t u u₀ uB f₀ fB h₀ hB hs]
  exact ht₀.add (tendsto_finsetSum t htB)

/-- Smooth representatives add in the actual disk H1 carrier. -/
lemma RepresentsDiskJet.add {f g : ℂ → ℂ} {u v : ComplexH1}
    (hf : RepresentsDiskJet f u) (hg : RepresentsDiskJet g v)
    (hfd : Differentiable ℝ f) (hgd : Differentiable ℝ g) :
    RepresentsDiskJet (fun z => f z + g z) (u + v) := by
  have hd z d : fderiv ℝ (fun z => f z + g z) z d =
      fderiv ℝ f z d + fderiv ℝ g z d := by
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L d)
      (((hfd z).hasFDerivAt.add (hgd z).hasFDerivAt).fderiv)
  refine ⟨?_, ?_, ?_⟩
  · rw [map_add]
    filter_upwards [Lp.coeFn_add (valueCLM u) (valueCLM v), hf.1, hg.1] with z ha hb hc
    simp only [ha, Pi.add_apply, hb, hc]
  · rw [dxLp_add]
    filter_upwards [Lp.coeFn_add (dxLp u) (dxLp v), hf.2.1, hg.2.1] with z ha hb hc
    simpa only [ha, Pi.add_apply, hb, hc] using (hd z 1).symm
  · rw [dyLp_add]
    filter_upwards [Lp.coeFn_add (dyLp u) (dyLp v), hf.2.2, hg.2.2] with z ha hb hc
    simpa only [ha, Pi.add_apply, hb, hc] using (hd z Complex.I).symm

/-- Finite sums preserve the exact smooth value/derivative representatives. -/
lemma RepresentsDiskJet.sum {ι : Type*} (t : Finset ι) (f : ι → ℂ → ℂ) (u : ι → ComplexH1)
    (hr : ∀ i ∈ t, RepresentsDiskJet (f i) (u i))
    (hd : ∀ i ∈ t, Differentiable ℝ (f i)) :
    RepresentsDiskJet (fun z => ∑ i ∈ t, f i z) (∑ i ∈ t, u i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨?_, ?_, ?_⟩
    · rw [map_zero]
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (disk : Set ℂ))] with z hz
      exact hz
    · rw [show dxLp 0 = 0 from map_zero dxCLM]
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (disk : Set ℂ))] with z hz
      simpa using hz
    · rw [show dyLp 0 = 0 from map_zero dyCLM]
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict (disk : Set ℂ))] with z hz
      simpa using hz
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hr i (Finset.mem_insert_self i t)).add
      (ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
        (fun j hj => hd j (Finset.mem_insert_of_mem hj)))
      (hd i (Finset.mem_insert_self i t))
      (Differentiable.fun_sum (fun j hj => hd j (Finset.mem_insert_of_mem hj)))

/-- Once the finitely many local pieces are smooth and represented by their
H1 carriers, their actual summed function represents the summed carrier.
A single eventual threshold works for every piece. -/
theorem eventually_finite_smooth_representation {ι : Type*} (t : Finset ι)
    (f₀ : ℕ → ℂ → ℂ) (fB : ι → ℕ → ℂ → ℂ)
    (U₀ : ℕ → ComplexH1) (UB : ι → ℕ → ComplexH1)
    (h₀ : ∀ᶠ n in atTop, ContDiff ℝ ∞ (f₀ n) ∧ RepresentsDiskJet (f₀ n) (U₀ n))
    (hB : ∀ i ∈ t, ∀ᶠ n in atTop,
      ContDiff ℝ ∞ (fB i n) ∧ RepresentsDiskJet (fB i n) (UB i n)) :
    ∀ᶠ n in atTop,
      ContDiff ℝ ∞ (fun z => f₀ n z + ∑ i ∈ t, fB i n z) ∧
      RepresentsDiskJet (fun z => f₀ n z + ∑ i ∈ t, fB i n z)
        (U₀ n + ∑ i ∈ t, UB i n) := by
  have hall := (eventually_all_finset t).mpr hB
  filter_upwards [h₀, hall] with n hn hb
  have hsum : ContDiff ℝ ∞ (fun z => ∑ i ∈ t, fB i n z) :=
    ContDiff.sum (fun i hi => (hb i hi).1)
  exact ⟨hn.1.add hsum, hn.2.add
    (RepresentsDiskJet.sum t _ _ (fun i hi => (hb i hi).2)
      (fun i hi => (hb i hi).1.differentiable (by norm_num)))
    (hn.1.differentiable (by norm_num)) (hsum.differentiable (by norm_num))⟩

end KsIndex.Trace
