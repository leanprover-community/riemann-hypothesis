module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ArchUnimod
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicAndConstantTerm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgreeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentUnipotentIntegralVanishSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentIntegralsPureTensorVanishOfLocalStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing GlobalTheory.Proof.parabolic_and_constant_term
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem MainStatements.WeightKernel.cuspAny : MainStatements.WeightKernel.CuspAny := by
  intro D V hodd T U hNoFixed μf hμf ff hff fa hA 𝔉 hP
  have := hμf
  have hH := (GlobalTheory.T.typeHypothesis_forms_agree D V T hNoFixed).1
  obtain ⟨a, ha0, ha2, hpar⟩ := parabolicAtSplitPlaces D V hodd T 𝔉 hP
  obtain ⟨v, hv⟩ := hH a ha0 (by omega)
  obtain ⟨h, hh, e⟩ := hff.2.1 v
  have hF := hff.isFinFamily
  have he := (T.frame v).idem_mem (μf v.1) (T.τ v)
  refine GlobalTheory.T.unipotentIntegrals_pureTensor_vanish_of_local D V 𝔉 fa ff hA hF v.1 fun ν _ x y => ?_
  exact (GlobalTheory.T.typeIdempotent_unipotentIntegral_vanish_splitPlace D V T v a ha0 (by omega) hv 𝔉 (hpar v).1 (μf v.1) _ (conv_mem_SB he hh) (ff v.1) (Or.inr e)
    ν x y).2

end
