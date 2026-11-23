module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem _root_.GlobalTheory.T.framedPointMove_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∃ ν : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X), ν.φ = 𝟙 _ ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FrMove (𝟙 Xo.X) ν y y) ∧ (∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ'), ∃ μ : SABMap Xo.univ.t Xo.univ.t (ρ ≫ ρ'), μ.φ = ν.φ ≫ ν'.φ ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S), FrMove ρ ν y y' → FrMove ρ' ν' y' y'' → FrMove (ρ ≫ ρ') μ y y'') ∧ ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), FrMap φ y z → FrMove ρ ν y y' → FrMove ρ ν z z' → FrMap φ y' z') ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' z z' : FrPt Xo c S), FrBor t y z → FrMove ρ ν y y' → FrMove ρ ν z z' → FrBor t y' z' := by
  first | exact @GlobalTheory.MoveCalc.frMove_calculus | exact GlobalTheory.MoveCalc.frMove_calculus | (intros; apply GlobalTheory.MoveCalc.frMove_calculus <;> assumption)
