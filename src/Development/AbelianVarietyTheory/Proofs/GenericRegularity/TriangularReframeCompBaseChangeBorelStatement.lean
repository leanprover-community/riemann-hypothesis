module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularReframeCompBaseChangeBorel
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.triangularReframe_comp_baseChange_borel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S], (∀ (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' y'' : FrPt Xo c S), Reframe g y y' → Reframe g' y' y'' → Reframe (fun τ => g τ * g' τ) y y'') ∧ (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), Reframe g y y' → FrMap φ y z → FrMap φ y' z' → Reframe (fun τ => (g τ).map φ) z z') ∧ ∀ y y' : FrPt Xo c S, (∃ t : Ix Dw → Sˣ, FrBor t y y') ↔ ∃ b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, IsUnit (b τ i i)) ∧ Reframe b y y' := by
  first | exact @GlobalTheory.Reg.reframe_calculus | exact GlobalTheory.Reg.reframe_calculus | (intros; apply GlobalTheory.Reg.reframe_calculus <;> assumption)
