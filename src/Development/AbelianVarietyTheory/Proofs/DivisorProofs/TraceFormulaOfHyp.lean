import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceOfInputs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceInputsImplyCuspidalTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalSpectrumFinitenessOfDecayHarishChandra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricExpansionOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicTermsVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealStableOfCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleRepHasTraceFiniteAdelicPureTensorFunctStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleIrreducibleTorusCharactersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffEqZeroOfSumTraceProjectionsInequivalentIrre
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestFamiliesProjectedTranslationOperators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleAdmissibleLocalComponentFiniteAStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorTraceEqConstMulLocalTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqualityOfGeomExpansion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientSeparationOfHarishChandra
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthFilterFinRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvalues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicAndConstantTermStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalOperatorsVanishingRadicalIntegralsUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EllipticPart

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_inputs_imply_cuspidal_trace : GlobalTheory.Published.PseudoCoefficientUpq → SpecFin → SpecTrace → Separation → TraceEq → TRCusp := by
  first | exact @GlobalTheory.TrMultEnd.trCusp_of_steps | exact GlobalTheory.TrMultEnd.trCusp_of_steps | (intros; apply GlobalTheory.TrMultEnd.trCusp_of_steps <;> assumption)
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_expansion_of_parts : EllTrace → EllipticPart → RealStable → GeomExpansion := by
  first | exact @GlobalTheory.TrMult.geomExpansion_of_parts | exact GlobalTheory.TrMult.geomExpansion_of_parts | (intros; apply GlobalTheory.TrMult.geomExpansion_of_parts <;> assumption)
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_stable_of_characters : GlobalTheory.Published.HarishChandraCharacters → RealStable := by
  first | exact @GlobalTheory.TrMult.realStable_of_harishChandra | exact GlobalTheory.TrMult.realStable_of_harishChandra | (intros; apply GlobalTheory.TrMult.realStable_of_harishChandra <;> assumption)
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical

noncomputable section

namespace GlobalTheory.TrMultSep

theorem separation_of_iwahoriTrace (hI : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace) (hE : GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate) :
    Separation := by
  intro D V T U hU μf hμ hK ν hν n Ws _ _ σs hσ a hyp
  haveI : ν.IsHaarMeasure := hν.1
  obtain ⟨e, he, hP, hfam⟩ := GlobalTheory.T.exists_testFamilies_projectedTranslationOperators D V T U hU μf hμ hK ν hν
  have hex : ∀ i, ∃ P : Ws i →ₗ[ℂ] Ws i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν (σs i) (finFn V e) P ∧
      FiniteDimensional ℂ (LinearMap.range P) := by
    intro i
    obtain ⟨c, A, hA, hAf⟩ := (GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V ν e he (Ws i) (σs i) (hσ.2.1 i)).1
    exact ⟨A, hA, hAf.1⟩
  choose P hPint using hex
  have hidem : ∀ i, P i ∘ₗ P i = P i := fun i => (hP (Ws i) (σs i) (hσ.2.1 i).1 (P i) (hPint i).1).1
  have hne : ∀ i, HasTypeVec T (σs i) → P i ≠ 0 := fun i h => (hP (Ws i) (σs i) (hσ.2.1 i).1 (P i) (hPint i).1).2 h
  intro i hi
  refine GlobalTheory.T.coeff_eq_zero_of_sum_trace_projections_inequivalent_irreps (GfC V) n Ws σs hσ.1 hσ.2.2 P hidem (fun i => (hPint i).2) a ?_ i (hne i hi)
  intro g c hc
  obtain ⟨ff, hff, hffI, hffT, hffOp⟩ := hfam g
  have htr : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i) := fun i =>
    ⟨_, hffOp (Ws i) (σs i) (hσ.2.1 i).1 (P i) (hPint i).1, hc i⟩
  have hloc := fun i => GlobalTheory.T.exists_irreducible_admissible_localComponent_finiteAdelic D V U.u (Ws i) (σs i) (hσ.1 i) (hσ.2.1 i)
  choose N instA instM π hπ using hloc
  letI : ∀ i, AddCommGroup (N i) := instA
  letI : ∀ i, Module ℂ (N i) := instM
  have hfac := fun i => GlobalTheory.T.pure_tensor_trace_eq_const_mul_local_trace D V U.u μf hμ hK ν hν (Ws i) (σs i) (hσ.2.1 i) (N i) (π i) (hπ i).1
    (hπ i).2.1 (hπ i).2.2 ff hff
  choose c' hc' using hfac
  have hd : ∀ t ∈ strictTorus V.rank U.ϖ, ∀ b : Fin n → ℂ,
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf U.u) (π i) (U.frame.cosetFn t) (b i)) →
      ∑ i, (a i * c' i) * b i = 0 := by
    intro t ht b hb
    have h := hyp (Function.update ff U.u (U.frame.cosetFn t)) (hffT t ht).1 (hffT t ht).2 (fun i => c' i * b i)
      (fun i => (hc' i _ (U.frame.cosetFn_mem t)).2 (b i) (hb i))
    simpa [mul_assoc] using h
  have hb := fun i => (hc' i (ff U.u) (hff.1 U.u)).1
  choose b hb using hb
  have key := GlobalTheory.T.admissible_irreducible_torus_characters hI hE D V U (μf U.u) (hμ U.u) n N π (fun i => (hπ i).1) (fun i => (hπ i).2.1)
    (fun i => a i * c' i) hd (ff U.u) (hff.1 U.u) hffI b hb
  have hceq : ∀ i, c i = c' i * b i := by
    intro i
    have h := (hc' i (ff U.u) (hff.1 U.u)).2 (b i) (hb i)
    rw [Function.update_eq_self] at h
    exact (htr i).unique h
  simp_rw [hceq, ← mul_assoc]
  exact key

end GlobalTheory.TrMultSep
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_separation_of_iwahori_trace : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace → GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate → Separation := by
  atlas_forward_decl GlobalTheory.TrMultSep.separation_of_iwahoriTrace
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_equality_of_geom_expansion : GeomExpansion → TraceEq := by
  first | exact @GlobalTheory.TraceEqTwo.traceEq_of_geomExpansion | exact GlobalTheory.TraceEqTwo.traceEq_of_geomExpansion | (intros; apply GlobalTheory.TraceEqTwo.traceEq_of_geomExpansion <;> assumption)
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EqualMultAssembly

theorem trCusp_of_classicalTheorems :
    GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification →
    GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspTraceClass →
    GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation →
    GlobalTheory.Published.PseudoCoefficientUpq → GlobalTheory.Published.HarishChandraCharacters →
    GlobalTheory.Published.LanglandsClassification → GlobalTheory.Published.LabesseWaldspurger →
    GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → TRCusp := by
  intro an ds rd hf tc dm fl ps hc lc lw ze gl
  have co := GlobalTheory.T.cuspidalOperators_vanishingRadicalIntegrals_unitaryGroup tc
  have asep := GlobalTheory.T.pseudocoefficient_separation_of_harish_chandra an ps hc lc
  have hyp := GlobalTheory.T.hyperbolic_terms_vanish lw GlobalTheory.T.parabolic_and_constant_term GlobalTheory.T.typeIdempotent_constantTerm_vanish GlobalTheory.T.regularSemisimple_unitaryGroup_concrete
  have ell := GlobalTheory.T.elliptic_trace_of_inputs lw co GlobalTheory.T.parabolic_and_constant_term GlobalTheory.IwahoriEigenObj.iwahoriEigenvalues
    GlobalTheory.T.regularSemisimple_unitaryGroup_concrete GlobalTheory.T.non_field_type_vanishing hyp
  exact GlobalTheory.T.trace_inputs_imply_cuspidal_trace ps (GlobalTheory.T.cuspidal_spectrum_finiteness_of_decay_harishChandra rd hf dm)
    (GlobalTheory.T.pseudo_coefficient_separation ds rd hf dm fl hc co GlobalTheory.T.parabolic_and_constant_term asep)
    (GlobalTheory.T.trace_separation_of_iwahori_trace GlobalTheory.IwahoriTraceProof.iwahoriTrace
      (GlobalTheory.SmGL.Exponents.exponentsSeparate gl ze))
    (GlobalTheory.T.trace_equality_of_geom_expansion (GlobalTheory.T.geometric_expansion_of_parts ell GlobalTheory.T.elliptic_part (GlobalTheory.T.real_stable_of_characters hc)))

end GlobalTheory.EqualMultAssembly
end
