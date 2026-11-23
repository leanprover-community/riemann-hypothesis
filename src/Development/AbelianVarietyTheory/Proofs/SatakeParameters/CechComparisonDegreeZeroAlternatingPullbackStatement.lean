module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechAbPullApp
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfAcyclic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechComparisonDegreeZeroAlternatingPullback
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

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite GlobalTheory SheafPull

theorem _root_.GlobalTheory.T.cechComparison_degreeZero_alternatingPullback : ∀ {T T' : TopCat.{0}} (f : T' ⟶ T) {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    [Finite ι] [Finite κ] {V : Opens T} {U : ι → Opens T} {V' : Opens T'} {U' : κ → Opens T'}
    (τ : κ → ι) (hτ : ∀ s : Finset κ, cechOpen V' U' s ≤ (Opens.map f).obj (cechOpen V U (s.image τ)))
    (hc : V ≤ ⨆ i, U i) (hc' : V' ≤ ⨆ k, U' k) (hV : V' ≤ (Opens.map f).obj V)
    {F : AbSheaf T} {G : AbSheaf T'} (φ : F ⟶ (push f).obj G) (hF : CechAcyclic V U F)
    (hG : CechAcyclic V' U' G) (x : LinearMap.ker (Cube.d (cechAbCube F.obj V U) (0 + 1)))
    (y : LinearMap.ker (Cube.d (cechAbCube G.obj V' U') (0 + 1))),
    y.1 = (cechAbPull f τ hτ φ).term (0 + 1) x.1 →
    cechAbHEquivH' hc' hG 0 (cechClass _ 0 y) =
      SheafPull.pull f φ 0 (homOfLE hV) (cechAbHEquivH' hc hF 0 (cechClass _ 0 x)) := by
  first | (exact @GlobalTheory.cechAbPull_degZero) | (exact GlobalTheory.cechAbPull_degZero) | (intros; apply GlobalTheory.cechAbPull_degZero  <;> assumption)
