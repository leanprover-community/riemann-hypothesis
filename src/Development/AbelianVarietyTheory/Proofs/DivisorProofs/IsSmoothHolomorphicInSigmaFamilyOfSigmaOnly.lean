module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

theorem wirt_const_fun {Φ : Type} [Fintype Φ] (τ : Φ) (bar : Bool) (d : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirt τ bar (fun _ : Φ → ℂ => d) = fun _ => 0 := by
  funext z
  simp [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirt]

theorem wirtWord_const_fun {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (d : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord ws (fun _ : Φ → ℂ => d) = fun _ => if ws = [] then d else 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord_cons, ih]
    simp only [reduceCtorEq, if_false]
    exact wirt_const_fun w.1 w.2 _

theorem isGood_const (F : Type) [Field F] [NumberField F] (a : ℂ → ℂ)
    (ha : DifferentiableOn ℂ a GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane) :
    GlobalTheory.HeckeTwo.IsGood (fun σ (_ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) => a σ) := by
  refine ⟨fun σ _ => contDiffOn_const, fun w z _ => ?_⟩
  simp only [wirtWord_const_fun]
  split_ifs
  · exact ha
  · exact differentiableOn_const 0

theorem goodConst : ∀ (F : Type) [Field F] [NumberField F] (a : ℂ → ℂ), DifferentiableOn ℂ a GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane → GlobalTheory.HeckeTwo.IsGood (fun σ (_ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) => a σ) :=
  fun F _ _ a ha => isGood_const F a ha

end GlobalTheory.HeckeTwo
