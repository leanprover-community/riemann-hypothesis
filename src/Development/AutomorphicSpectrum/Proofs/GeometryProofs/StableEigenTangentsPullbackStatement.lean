module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenTangentsPullback
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLineGenOn

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

theorem _root_.GlobalTheory.T.stable_eigen_tangents_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : Type) [CommRing T] (y : Sp T ⟶ Xo.XF c) (A : Type) [CommRing A] (x₀ : Sp A ⟶ Y.X) (κ : c.F →+* A) (θ : A →+* T) (σ : E →+* ℂ) (r : ℕ) (e : Fin r → (epsAt x₀ ⟶ Y.t.G)), spMap θ ≫ x₀ = y ≫ Y.j → StableEig Y.t x₀ κ σ e → ∃ V : Fin r → (epsAt (under y) ⟶ Xo.univ.t.G), (∀ i, Tied Y y (V i).left (spMap (Formalism.L2.Pj.dualMap θ) ≫ (e i).left)) ∧ IsEigFrame Xo.univ.t.act (under y) ((θ.comp κ).comp (tauIn c σ)) V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.exists_eigFrame_univ | exact GlobalTheory.CompanionTheory.Ar.LocFn.exists_eigFrame_univ | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.exists_eigFrame_univ <;> assumption)
