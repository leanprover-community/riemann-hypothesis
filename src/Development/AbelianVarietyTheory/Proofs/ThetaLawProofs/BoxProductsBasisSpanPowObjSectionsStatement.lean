module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BoxProductsBasisSpanPowObjSections
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.boxProducts_basis_span_powObj_sections : ∀ (K : Type) [Field K] (x : KeyIn K) (m N : ℕ) (b : Fin N → RR x m), IsBasis x b → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))), ∃ q : (Fin n → Fin N) → K, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J, Good x.P.L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj x.P.A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  first | exact @GlobalTheory.BoxSpan.boxProducts_span | exact GlobalTheory.BoxSpan.boxProducts_span | (intros; apply GlobalTheory.BoxSpan.boxProducts_span <;> assumption)
