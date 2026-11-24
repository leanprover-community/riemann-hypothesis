module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpFormEqZeroOfPullbackVanishing
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

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cmpForm_eq_zero_of_pullback_vanishing : ∀ (K : Type) [Field K] (X : Over (Sp K)), Smooth X.hom → ∀ f : Form (X.hom ≫ 𝟙 (Sp K)), (∀ (L : Type) [Field L] (σ : K →+* L), ∃ (X' : Over (Sp L)) (φ : X'.left ⟶ X.left) (m : IsMor (dp0 K) (X.hom ≫ 𝟙 (Sp K)) (dp0 L) (X'.hom ≫ 𝟙 (Sp L)) σ φ), IsPullback φ X'.hom X.hom (spMap σ) ∧ ∀ u : epsR L ⟶ X', tanVal u (m.pullForm f) = 0) → GlobalTheory.CechDR.cmpForm (X.hom ≫ 𝟙 (Sp K)) f = 0 := by
  first | exact @GlobalTheory.PtVanish.cmpForm_eq_zero_of_tanVal | exact GlobalTheory.PtVanish.cmpForm_eq_zero_of_tanVal | (intros; apply GlobalTheory.PtVanish.cmpForm_eq_zero_of_tanVal <;> assumption)
