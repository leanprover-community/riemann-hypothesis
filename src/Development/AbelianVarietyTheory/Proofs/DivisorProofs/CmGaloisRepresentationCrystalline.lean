module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotientsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockIsTheRun
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalTwistAbsDetPowGLStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsGaloisCompatStatement

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CsdTwistGal

theorem infChar_conj_of_isCsd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (P : CuspSub E a), P.IsCsd →
    ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), P.HasInfChar τ m →
      P.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m' → m' = m.map Neg.neg := by
  intro E _ _ _ a P hP τ m m' hm hm'
  have h1 : (GlobalTheory.ThetaPull.thetaSub P).Iso P := by
    obtain ⟨T, hT⟩ := hP
    refine ⟨((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V).symm.trans T, fun o φ => ?_⟩
    obtain ⟨φ, rfl⟩ := ((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V).surjective φ
    have e : (GlobalTheory.ThetaPull.thetaSub P).op o ((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V φ) =
        (GlobalTheory.ThetaPull.pull E a).submoduleMap P.V (P.op (thetaOp o) φ) :=
      Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1)
    rw [e]
    exact (congrArg T (((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V).symm_apply_apply _)).trans
      ((hT o φ).trans (congrArg (P.op o)
        (congrArg T (((GlobalTheory.ThetaPull.pull E a).submoduleMap P.V).symm_apply_apply φ)).symm))
  have h2 : (GlobalTheory.ThetaPull.thetaSub P).HasInfChar τ (m'.map Neg.neg) := by
    refine ⟨by rw [Multiset.card_map, hm'.1], ?_⟩
    rintro u _ ⟨φ, hφ, rfl⟩
    change cap τ u (GlobalTheory.ThetaPull.pull E a φ) = _ • GlobalTheory.ThetaPull.pull E a φ
    rw [GlobalTheory.ThetaPull.cap_pull, LinearMap.smul_apply, hm'.2 _ φ hφ, smul_smul, map_smul]
    congr 1
    have e : ((m'.map Neg.neg).map (u + ·)) = (m'.map (-u + ·)).map Neg.neg := by
      rw [Multiset.map_map, Multiset.map_map]
      refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply]; ring
    rw [e, Multiset.prod_map_neg, Multiset.card_map, hm'.1]
  have h4 := (h1.hasInfChar h2).unique hm
  rw [← h4, Multiset.map_map]
  simp

end GlobalTheory.CsdTwistGal

end
