module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HypA
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityCoverHypotheses
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDataExtendLargerFieldsOfPublishedStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsBareFormOfSaturation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset

@[expose] public section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
noncomputable section
namespace GlobalTheory.HeightCounting.Up
theorem weightOne_saturated_of_hypotheses : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState := fun hA hH =>
  _root_.GlobalTheory.T.exists_bare_form_of_saturation hA hH (GlobalTheory.T.adelicData_extend_largerFields_of_hypotheses hH.cover hA.a5 hA.a6 hA.a7 hA.a8 hA.a9 hA.a10)
end GlobalTheory.HeightCounting.Up
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.compatibleSystem_weightOne_saturated : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.weightOne_saturated_of_hypotheses | exact _root_.GlobalTheory.HeightCounting.Up.weightOne_saturated_of_hypotheses | (intros; apply _root_.GlobalTheory.HeightCounting.Up.weightOne_saturated_of_hypotheses <;> assumption)
end
