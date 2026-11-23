module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRosatiCoordinatesDivisibleOfPow
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_rosatiCoordinates_divisible_of_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (n : ℕ) (x : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G), 0 < n →
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ a, ∃ y : 𝓞 E, (n : 𝓞 E) * y = ∑ b, gP a b * H.bar (x b) := by
  first | exact @GlobalTheory.FlatCM.RosatiCoord.exists_mul_eq_gram_sum | exact GlobalTheory.FlatCM.RosatiCoord.exists_mul_eq_gram_sum | (intros; apply GlobalTheory.FlatCM.RosatiCoord.exists_mul_eq_gram_sum <;> assumption)
