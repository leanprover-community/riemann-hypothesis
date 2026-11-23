module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedMultiplicationPullbackFunction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.exists_normalised_multiplicationPullback_function : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → ∀ (m : ℕ) (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ), FnT u 1 th f → ∃ (α : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![(snd (baseOver (Sp ℂ)) x.P.A).left, (snd (baseOver (Sp ℂ)) x.P.A ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (s₁ : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp ℂ)))), α.IsGen ∧ LB.Gen.Corr x.P.L _ _ _ _ (LB.pullGen x.P.L _ _ α (ptSecT x.P.A 1).left) (rigT x.P.A x.P.L x.rig (baseOver (Sp ℂ)) (((m ^ 2 : ℕ) : ℤ) - 1)) ∧ IsTwistPull x.P.A x.P.L (mulT x.P.A (baseOver (Sp ℂ)) m) (snd (baseOver (Sp ℂ)) x.P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧ FnT u (m ^ 2) s₁ fun z => f ((m : ℂ) • z) := by
  first | exact @GlobalTheory.MBLow.Cl.exists_normalised_mulPull_fnT | exact GlobalTheory.MBLow.Cl.exists_normalised_mulPull_fnT | (intros; apply GlobalTheory.MBLow.Cl.exists_normalised_mulPull_fnT <;> assumption)
