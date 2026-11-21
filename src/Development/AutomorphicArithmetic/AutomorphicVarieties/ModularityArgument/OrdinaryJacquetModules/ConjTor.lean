import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNormalisedOfDualIsConj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCharacterSupportBaseChangeLiftDegreeOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLawsOfLawsLit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

namespace UpperTheory.V.Z.Ord

section Loc

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

private theorem hasSupport_contra {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL k)} (h : HasSupport π s) :
    HasSupport (contra π) (s.map Zc.dualCl) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨m, x, hs, hirr, hcusp, e, hsub⟩ := h
  have hπs : GlobalTheory.PRep.IsSmooth π := HasSupport.isSmooth ⟨m, x, hs, hirr, hcusp, e, hsub⟩
  have key : IsCuspSupport (contra π) (fun a => (x a).fst) (fun a => contra (x a).rep) := by
    refine ⟨GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k N)
      (hA k N V π hπs hirr) hirr, fun a => ?_, e, ?_⟩
    · have hc := (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA (x a) ⟨(hcusp a).1, (hcusp a).2.2⟩).1
      rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA, IrrGL.isCusp_of] at hc
      exact ⟨(hcusp a).1, GlobalTheory.CompanionTheory.ContraProd.contra_rep_isIrreducible hA (x a), hc.2⟩
    · have hρs : GlobalTheory.PRep.IsSmooth (piTensor fun a => (x a).rep) :=
        isSmooth_piTensor fun a => (x a).snd.rep.smooth
      have h1 := GlobalTheory.CompanionTheory.ContraSub.main k N V _ π (parInd e (piTensor fun a => (x a).rep)) hπs
        (isSmooth_parInd e _) hsub
      have h2 : Nonempty ((parInd e (piTensor fun a => contra (x a).rep)).Equiv
          (contra (parInd e (piTensor fun a => (x a).rep)))) :=
        GlobalTheory.CompanionTheory.ContraProd.parInd_equiv_contra (σ := piTensor fun a => contra (x a).rep)
          (ρ := piTensor fun a => (x a).rep) e hρs (GlobalTheory.CompanionTheory.ContraProd.contra_piTensor_rep hA x)
      obtain ⟨E⟩ := h2
      have h3 : IsSubquotient (contra (parInd e (piTensor fun a => (x a).rep)))
          (parInd e (piTensor fun a => contra (x a).rep)) :=
        IsSubquotient.of_surjective E.toIntertwiningMap fun w => ⟨E.invFun w, E.right_inv w⟩
      exact IsSubquotient.trans h1 h3
  have hsupp := hasSupport_of_isCuspSupport key
  have hmap : s.map Zc.dualCl = Multiset.map (fun a => Zc.dualCl (x a)) Finset.univ.val := by
    rw [← hs, Multiset.map_map]
    rfl
  rw [hmap]
  simp only [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA]
  exact hsupp








end Loc

end UpperTheory.V.Z.Ord
