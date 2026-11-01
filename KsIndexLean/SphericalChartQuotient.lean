module

public import KsIndexLean.SphericalReconstruction

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Ordinary matching disk data for the sphere with the unmatched equator removed. -/
def MatchingDiskPair (A : Set Circle₁) :=
  {p : ComplexH1 × ComplexH1 // arcTrace A p.1 = arcTrace A p.2}

/-- Functions on the actual sphere with genuine weak H1 regularity in both bounded charts. -/
def SphereChartFunctions (A : Set Circle₁) (hA : IsOpen A) :=
  {F : Sphere → ℂ //
    ChartH1 (extendedSeamDomain A hA) (fun z => F (sphereChart z)) ∧
    ChartH1 (extendedSeamDomain A hA) (fun z => F (southChart z))}

def sphereChartSetoid (A : Set Circle₁) (hA : IsOpen A) :
    Setoid (SphereChartFunctions A hA) where
  r F G := ((fun z => F.val (sphereChart z)) =ᵐ[volume] (fun z => G.val (sphereChart z))) ∧
    ((fun z => F.val (southChart z)) =ᵐ[volume] (fun z => G.val (southChart z)))
  iseqv := ⟨fun _ => ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩,
    fun h => ⟨h.1.symm, h.2.symm⟩, fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩⟩

/-- The quotient by planar almost-everywhere equality in both stereographic charts. -/
def SphereChartSpace (A : Set Circle₁) (hA : IsOpen A) := Quotient (sphereChartSetoid A hA)

def matchingPairFunction {A : Set Circle₁} (hA : IsOpen A) (p : MatchingDiskPair A) :
    SphereChartFunctions A hA :=
  ⟨sphereJoinedValue p.val.1 p.val.2,
    (sphereJoinedValue_north_H1_iff hA _ _).mpr p.property,
    (sphereJoinedValue_south_H1_iff hA _ _).mpr p.property⟩

def matchingPairClass {A : Set Circle₁} (hA : IsOpen A) (p : MatchingDiskPair A) :
    SphereChartSpace A hA := Quotient.mk _ (matchingPairFunction hA p)

lemma matchingPairClass_injective {A : Set Circle₁} (hA : IsOpen A) :
    Function.Injective (matchingPairClass hA) := by
  intro p q he
  have hr := Quotient.exact he
  change ((fun z => sphereJoinedValue p.val.1 p.val.2 (sphereChart z)) =ᵐ[volume]
      (fun z => sphereJoinedValue q.val.1 q.val.2 (sphereChart z))) ∧
    ((fun z => sphereJoinedValue p.val.1 p.val.2 (southChart z)) =ᵐ[volume]
      (fun z => sphereJoinedValue q.val.1 q.val.2 (southChart z))) at hr
  have hn : joinedDiskValue p.val.1 p.val.2 1 =ᵐ[volume]
      joinedDiskValue q.val.1 q.val.2 1 := by
    simpa only [sphereJoinedValue_north] using hr.1
  have hs := (sphereJoinedValue_south_ae p.val.1 p.val.2).symm.trans
    (hr.2.trans (sphereJoinedValue_south_ae q.val.1 q.val.2))
  have hm := ae_mono (Measure.restrict_le_self : volume.restrict (disk : Set ℂ) ≤ volume)
  apply Subtype.ext
  apply Prod.ext
  · apply valueCLM_injective
    exact Lp.ext ((joinedDiskValue_disk_ae _ _ _).symm.trans
      ((hn.filter_mono hm).trans (joinedDiskValue_disk_ae _ _ _)))
  · apply valueCLM_injective
    exact Lp.ext ((joinedDiskValue_disk_ae _ _ _).symm.trans
      ((hs.filter_mono hm).trans (joinedDiskValue_disk_ae _ _ _)))

lemma matchingPairClass_surjective {A : Set Circle₁} (hA : IsOpen A) :
    Function.Surjective (matchingPairClass hA) := by
  intro Q
  induction Q using Quotient.inductionOn with
  | h F =>
    obtain ⟨u, v, ht, hn, hs⟩ := sphere_chart_reconstruction hA F.val F.property.1 F.property.2
    refine ⟨⟨(u, v), ht⟩, Quotient.sound ?_⟩
    exact ⟨hn, hs⟩

/-- The chartwise weak quotient is equivalent to the genuine matching disk carriers. -/
def matchingDiskPairEquiv (A : Set Circle₁) (hA : IsOpen A) :
    MatchingDiskPair A ≃ SphereChartSpace A hA :=
  Equiv.ofBijective (matchingPairClass hA)
    ⟨matchingPairClass_injective hA, matchingPairClass_surjective hA⟩

end KsIndex.Spherical
