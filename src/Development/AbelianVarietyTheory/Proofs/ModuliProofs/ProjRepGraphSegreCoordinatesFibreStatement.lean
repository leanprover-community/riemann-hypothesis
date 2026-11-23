module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjRepGraphSegreCoordinatesFibre
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.projRep_graph_segre_coordinates_fibre : ∀ (R K σ₁ σ₂ : Type) [CommRing R] [CommRing K] [Finite σ₁] [Finite σ₂] (x : R →+* K) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (Z₁ Z₂ : Over (Sp R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (Y : Scheme.{0}) (s : Y ⟶ Sp K) (a₁ : Y ⟶ Z₁.left) (a₂ : Y ⟶ Z₂.left), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsPullback a₁ s Z₁.hom (spMap x) → a₂ ≫ Z₂.hom = s ≫ spMap x → ∃ (N : LB Y) (ty : σ₁ × σ₂ → N.Sec), ProjRep (graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂) s N ty ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v₁ : σ₁ → T) (v₂ : σ₂ → T), SecCoord M₁ th₁ (y ≫ a₁) v₁ → SecCoord M₂ th₂ (y ≫ a₂) v₂ → SecCoord N ty y (fun i => v₁ i.1 * v₂ i.2) := by
  first | exact @GlobalTheory.ZM.GraphSegre.projRep_graph | exact GlobalTheory.ZM.GraphSegre.projRep_graph | (intros; apply GlobalTheory.ZM.GraphSegre.projRep_graph <;> assumption)
