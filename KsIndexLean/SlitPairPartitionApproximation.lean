module

public import KsIndexLean.PhasePairInteriorApproximation

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

/-- The local data retained for later assembly of the original smooth seams. -/
def SmoothSeamPair (k a : ℕ) (c : ℂ) (f g : ℂ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧ HasCompactSupport f ∧ HasCompactSupport g ∧
  tsupport f ⊆ seamDomain (boundaryArc k a) (isOpen_boundaryArc k a) ∧
  tsupport g ⊆ seamDomain (boundaryArc k a) (isOpen_boundaryArc k a) ∧
  phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g) = f ∧
  phaseGerm c⁻¹ (closedDiskRestriction g) (closedDiskRestriction f) = g

/-- Assemble the actual punctured boundary partition and both interior
remainders. The smooth sums converge to the original pair in product H1.
Local seam identities and support are retained for the subsequent global
seam/puncture and cyclic-CcSmooth construction. -/
theorem slit_pair_partition_approximation (k : ℕ) (u v : ComplexH1) (c : ℕ → ℂ)
    (hc : ∀ a, a = 0 ∨ a = 1 → c a ≠ 0)
    (hm : ∀ a, a = 0 ∨ a = 1 → arcTrace (boundaryArc k a) u = c a • arcTrace (boundaryArc k a) v)
    {H : Set ℂ} (hH : IsOpen H) (hpH : KsIndex.Surface.punctures k ⊆ H)
    (hu : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), z ∈ H → valueCLM u z = 0)
    (hv : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), z ∈ H → valueCLM v z = 0) :
    ∃ (ι : Type) (t : Finset ι) (a : ι → ℕ)
      (F G : ι → ℕ → ℂ → ℂ) (F₀ G₀ : ℕ → ℂ → ℂ) (U V : ℕ → ComplexH1),
      Tendsto (fun n => (U n, V n)) atTop (𝓝 (u, v)) ∧
      (∀ i ∈ t, a i = 0 ∨ a i = 1) ∧
      (∀ i ∈ t, ∀ᶠ n in atTop, SmoothSeamPair k (a i) (c (a i)) (F i n) (G i n)) ∧
      (∀ᶠ n in atTop,
        ContDiff ℝ ∞ (F₀ n) ∧ HasCompactSupport (F₀ n) ∧ tsupport (F₀ n) ⊆ (disk : Set ℂ) ∧
        ContDiff ℝ ∞ (G₀ n) ∧ HasCompactSupport (G₀ n) ∧ tsupport (G₀ n) ⊆ (disk : Set ℂ)) ∧
      ∀ᶠ n in atTop,
        ContDiff ℝ ∞ (fun z => F₀ n z + ∑ i ∈ t, F i n z) ∧
        RepresentsDiskJet (fun z => F₀ n z + ∑ i ∈ t, F i n z) (U n) ∧
        ContDiff ℝ ∞ (fun z => G₀ n z + ∑ i ∈ t, G i n z) ∧
        RepresentsDiskJet (fun z => G₀ n z + ∑ i ∈ t, G i n z) (V n) := by
  classical
  obtain ⟨t, a, ha, ρ, hρ, hρc, hρs, hρi, hone⟩ := exists_punctured_boundary_partition k hH hpH
  let F := fun i n => compactMollify (shrinkingMollifier n)
    (fun z => ρ i z • joinedDiskValue u v (c (a i)) z)
  let G := fun i n z => (c (a i))⁻¹ * F i n (σ z)
  have hlocal i := localized_phase_pair_h1 (isOpen_boundaryArc k (a i)) u v (c (a i))
    (hc _ (ha i)) (hm _ (ha i)) (hρ i) (hρc i) (hρs i) (hρi i)
  choose ub vb UB VB htB huB hvB hgerm hspec using hlocal
  obtain ⟨u₀, f₀, F₀, U₀, huf, hsumu, htu₀, hsu₀⟩ :=
    partition_interior_approximation t ρ u hρ hH hu hone
  obtain ⟨v₀, g₀, G₀, V₀, hvg, hsumv, htv₀, hsv₀⟩ :=
    partition_interior_approximation t ρ v hρ hH hv hone
  have htu : Tendsto (fun n => U₀ n + ∑ i ∈ t, UB i n) atTop (𝓝 u) :=
    finite_carrier_tendsto t u u₀ ub f₀ (fun i z => ρ i z • valueCLM u z)
      huf (fun i _ => huB i) hsumu U₀ UB htu₀ (fun i _ => (continuous_fst.tendsto _).comp (htB i))
  have htv : Tendsto (fun n => V₀ n + ∑ i ∈ t, VB i n) atTop (𝓝 v) :=
    finite_carrier_tendsto t v v₀ vb g₀ (fun i z => ρ i z • valueCLM v z)
      hvg (fun i _ => hvB i) hsumv V₀ VB htv₀ (fun i _ => (continuous_snd.tendsto _).comp (htB i))
  refine ⟨↥(boundaryAway H), t, a, F, G, F₀, G₀,
    (fun n => U₀ n + ∑ i ∈ t, UB i n), (fun n => V₀ n + ∑ i ∈ t, VB i n),
    htu.prodMk_nhds htv, fun i _ => ha i, ?_, ?_, ?_⟩
  · intro i _
    filter_upwards [hspec i] with n hn
    exact ⟨hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1,
      hn.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2, hgerm i n,
      phaseGerm_restricted_pair_reverse (c (a i)) (hc _ (ha i)) (F i n)⟩
  · filter_upwards [hsu₀, hsv₀] with n hu hv
    exact ⟨hu.1, hu.2.1, hu.2.2.1, hv.1, hv.2.1, hv.2.2.1⟩
  · have hrepU := eventually_finite_smooth_representation t F₀ F U₀ UB
      (hsu₀.mono fun n h => ⟨h.1, h.2.2.2⟩)
      (fun i _ => (hspec i).mono fun n h => ⟨h.2.2.1, h.1⟩)
    have hrepV := eventually_finite_smooth_representation t G₀ G V₀ VB
      (hsv₀.mono fun n h => ⟨h.1, h.2.2.2⟩)
      (fun i _ => (hspec i).mono fun n h => ⟨h.2.2.2.1, h.2.1⟩)
    filter_upwards [hrepU, hrepV] with n hu hv
    exact ⟨hu.1, hu.2, hv.1, hv.2⟩

end KsIndex.Trace
