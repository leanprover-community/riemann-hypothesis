module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacTransfer

variable {D : D7} {S X : HSp D} {n d : ℕ}

def archLine (cS : Matrix (Fin n) (Fin d) (AE D) ≃+ WO S X) (u : Matrix (Fin n) (Fin d) (AE D)) : ℝ →+ WO S X where
  toFun t := cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)
  map_zero' := by
    have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 0 = 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd
      simp only [map_zero]
    show cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 0 • u) = 0
    rw [h, zero_smul]
    exact map_zero cS
  map_add' s t := by
    have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F (s + t) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd
      simp only [map_add (f := _)]
    show cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F (s + t) • u) =
      cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u) + cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)
    rw [h, add_smul]
    exact map_add cS _ _

theorem archLine_apply (cS : Matrix (Fin n) (Fin d) (AE D) ≃+ WO S X) (u : Matrix (Fin n) (Fin d) (AE D)) (t : ℝ) :
    archLine cS u t = cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u) := rfl

end GlobalTheory.VacTransfer

end
