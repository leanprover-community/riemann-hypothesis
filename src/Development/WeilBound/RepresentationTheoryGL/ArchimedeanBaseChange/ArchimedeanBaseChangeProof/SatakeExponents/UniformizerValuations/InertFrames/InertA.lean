module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameInert
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRSplit
public import GroundTheory.GlobalFields.TateThesis.Chebotarev

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.F.Inert

namespace InertPlacesInfinite

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end InertPlacesInfinite

theorem inertPlaceEx : InertPlaceEx := by
  intro E _ _ _ _ n π hπ Sec hSec X
  have hB : {w : HeightOneSpectrum (𝓞 E) | ¬ GlobalTheory.UnitaryBC.IsUnramU π w}.Finite :=
    Filter.eventually_cofinite.mp (PositivityTheory.Rg.BcB.F.Rig.eventually_isUnramU hπ)
  set T : Set (HeightOneSpectrum (𝓞 ↥(maximalRealSubfield E))) :=
    (fun w : HeightOneSpectrum (𝓞 E) => HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) w) ''
      ((X : Set (GlobalTheory.BCT.Pl E)) ∪ {w | ¬ GlobalTheory.UnitaryBC.IsUnramU π w}) with hT
  have hTf : T.Finite := (X.finite_toSet.union hB).image _
  obtain ⟨v, hv, hvT⟩ := (InertPlacesInfinite.inertSet_infinite (E := E)).exists_notMem_finite hTf
  obtain ⟨⟨Q, hQp, hQo⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 E) v.asIdeal
  have hQb : Q ≠ ⊥ := by
    intro h0
    apply v.ne_bot
    rw [hQo.over, h0]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  let w0 : HeightOneSpectrum (𝓞 E) := ⟨Q, hQp, hQb⟩
  have hw0 : HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) w0 = v :=
    HeightOneSpectrum.ext hQo.over.symm
  obtain ⟨u, ⟨huSec, huw⟩, -⟩ := hSec w0
  have huv : HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) u = v := huw.trans hw0
  refine ⟨u, huSec, ?_, ?_, ?_⟩
  · intro huX
    exact hvT ⟨u, Or.inl huX, huv⟩
  · rintro ⟨u', hne, hu'⟩
    apply hne
    have h1 : u.asIdeal.LiesOver v.asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal huv).symm⟩
    have h2 : u'.asIdeal.LiesOver v.asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal (hu'.trans huv)).symm⟩
    exact InertPlacesInfinite.eq_of_liesOver hv h1 h2
  · by_contra hun
    exact hvT ⟨u, Or.inr hun, huv⟩

end PositivityTheory.Rg.BcB.F.Inert

end
