module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FramedPointSpecialization
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem GlobalTheory.CompanionTheory.Ar.Flat.exists_framed_residue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (F : Type) [Field F] (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ β y v w → ∃ (k : Type) (_ : Field k) (β₀ : c.F →+* k) (y₀ : Sp k ⟶ Xo.XF c) (v₀ : Vecs y₀ D.p) (w₀ : Vecs y₀ D.q) (f : k →+* F) (j : k →+* ℂ), IsFramed U τ β₀ y₀ v₀ w₀ ∧ f.comp β₀ = β ∧ j.comp β₀ = algebraMap c.F ℂ ∧ y = spMap f ≫ y₀ ∧ ∀ (F' : Type) [Field F'] (f' : k →+* F'), ∃ (v' : Vecs (spMap f' ≫ y₀) D.p) (w' : Vecs (spMap f' ≫ y₀) D.q), IsFramed U τ (f'.comp β₀) (spMap f' ≫ y₀) v' w' ∧ (∀ a, (v' a).left = spMap (dualMap f') ≫ (v₀ a).left) ∧ ∀ b, (w' b).left = spMap (dualMap f') ≫ (w₀ b).left :=
  PositivityTheory.Xgn.framed_point_specialization
