module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem iterD_const_mul_reindex : ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (e : I ≃ J) (u : List I) (h : (J → ℂ) → ℂ) (A : ℂ) (z : I → ℂ), iterD u (fun z ↦ A * h (fun j ↦ z (e.symm j))) z = A * iterD (u.map e) h (fun j ↦ z (e.symm j)) := by
  intro I J _ _ _ _ e u h A z
  have key : ∀ v : List I, iterD v (fun z ↦ A * h (fun j ↦ z (e.symm j))) =
      fun z ↦ A * iterD (v.map e) h (fun j ↦ z (e.symm j)) := by
    intro v
    induction v with
    | nil => rfl
    | cons i v ih =>
      funext z
      show partialD i (iterD v _) z = A * partialD (e i) (iterD (v.map e) h) _
      rw [ih]
      simp only [partialD, lineDeriv]
      have hpath : (fun t : ℂ ↦ A * iterD (v.map e) h (fun j ↦ (z + t • (Pi.single i 1 : I → ℂ)) (e.symm j))) =
          fun t ↦ A * iterD (v.map e) h ((fun j ↦ z (e.symm j)) + t • (Pi.single (e i) 1 : J → ℂ)) := by
        funext t
        congr 2
        funext j
        simp [Pi.single_apply, Equiv.symm_apply_eq]
      rw [hpath, deriv_const_mul_field]
  exact congrFun (key u) z

end GlobalTheory.HilbFam
