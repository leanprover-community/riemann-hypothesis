module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverOrdEqSumAdaptedMonomial
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

theorem _root_.GlobalTheory.T.primeDivisorOver_ord_eq_sum_adaptedMonomial : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [GlobalTheory.IsNormalScheme Y] {q : Y ⟶ Sp k} (E : DivOver q) (y : Y), E.Through y →
    ∀ {ι : Type} [Fintype ι] (w : ι → Y) (u : ι → Y.functionFieldˣ), Function.Injective w →
    (∀ j, w j ⤳ y) → (∀ j, Order.coheight (w j) = 1) →
    (∀ j, Scheme.ord (u j : Y.functionField) (w j) = 1) →
    (∀ j v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0) →
    ∀ φ : Y.functionFieldˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j, v ≠ w j) → Scheme.ord (φ : Y.functionField) v = 0) →
      E.ord φ = ∑ j, Scheme.ord (φ : Y.functionField) (w j) * E.ord (u j) := by
  first | exact @GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial | exact GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial | (intros; apply GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial <;> assumption)
