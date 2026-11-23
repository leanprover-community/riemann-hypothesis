module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsUnitKoszulInvariantOfFiniteClosedFibreZeros
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.isUnit_koszulInvariant_of_finite_closedFibre_zeros : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℚ O] (F : Type) [Field F] (f : O →+* F) (x : KeyIn O) (xF : KeyIn F) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (hg : xF.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sF : Fin xF.P.g → RR xF n) (κ : Fˣ) (a : O) (e : ℤ), Function.Injective f → admitted x.P.g n l l' al → KeyVia xF x f φ w → (∀ i, SecVia xF x φ w (sF i) (s (i.cast hg))) → {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → KaVal xF n l l' al sF κ → (κ : F) ^ e = f a → e ≠ 0 → IsUnit a := by
  first | exact @GlobalTheory.KaFiniteUnit.isUnit_of_finite_zeros | exact GlobalTheory.KaFiniteUnit.isUnit_of_finite_zeros | (intros; apply GlobalTheory.KaFiniteUnit.isUnit_of_finite_zeros <;> assumption)
