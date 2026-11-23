module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.VacAny

theorem eq_atPlace_of_at {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) a → a = GlobalTheory.EmbChart.atPlace v (GlobalTheory.AdelicU.evFin F v a) := by
  intro h
  refine Prod.ext ?_ ?_
  · have h1 := h ((1 : Ainf F), (0 : Af F)) (by
      change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (0 : Af F) = 0
      exact map_zero _)
    have h2 := congrArg Prod.fst h1
    change (1 : Ainf F) * a.1 = 0 at h2
    rw [one_mul] at h2
    rw [h2]
    rfl
  · refine GlobalTheory.AdelicU.af_ext fun w => ?_
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w a.2 =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.AdelicU.singleFin v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a.2))
    by_cases e : w = v
    · subst e
      rw [GlobalTheory.AdelicU.evalV_singleFin_self]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e]
      have h1 := h ((0 : Ainf F), GlobalTheory.AdelicU.singleFin w 1) (by
        change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (GlobalTheory.AdelicU.singleFin w 1) = 0
        exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm e) 1)
      have h2 := congrArg (fun x : AF F => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w x.2) h1
      change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.AdelicU.singleFin w 1 * a.2) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w 0 at h2
      rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul, map_zero] at h2
      exact h2

end GlobalTheory.VacAny
