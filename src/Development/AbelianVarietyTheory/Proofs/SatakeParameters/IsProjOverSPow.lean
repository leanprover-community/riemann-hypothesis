module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckePowOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompactBIffCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoordValuationBoundLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowerOfAbelianSchemeProjective
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.WeightTwoHeckePower

namespace GlobalTheory.WeightTwoHeckePower

theorem isProjOver_sPow : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.CompactB → ∀ (gb : GBase D.toG ℂ) (N : ℕ), 3 ≤ N →
    N.Coprime p → ∀ (X : GenModel gb N) (r : ℕ), IsProjOver (sPow X r) := by
  intro p _ D hC gb N hN hNp X r
  have hX : IsProjOver X.s := GlobalTheory.UPel.HT.GenProj.isProjOver_genModel p D hC gb N hN hNp X
  exact GlobalTheory.KS.isProjOver_pow ℂ X.X X.s hX X.univ.A X.univ.ab _
    (LB.isLB_pull X.univ.isLB _) X.univ.ample r

end GlobalTheory.WeightTwoHeckePower
