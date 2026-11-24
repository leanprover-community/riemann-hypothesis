module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GGramPush
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_gram_invariant_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (n : ℕ) (v' : Fin n → (epsAt x' ⟶ t'.G)) (v : Fin n → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x = x' ≫ f → (∀ k, (v k).left = (v' k).left ≫ m.φ) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  first | exact @PositivityTheory.Xgf.hodge_gram_invariant_pullback | exact PositivityTheory.Xgf.hodge_gram_invariant_pullback
