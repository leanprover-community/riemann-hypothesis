module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultipleOfHermitianFormSumOfNorms
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.cmHermitianForm_sum_of_squares : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ (N m : ℕ) (l : D.La →ₗ[OK H] (Fin m → OK H)) (r : (Fin m → OK H) →ₗ[OK H] D.La), 1 ≤ N ∧ r ∘ₗ l = LinearMap.id ∧ ∀ x y, (N : 𝓞 E) * (h x y : OK H) = ∑ k, ((l x k : OK H) : 𝓞 E) * H.bar (l y k : OK H) := by
  first | exact @GlobalTheory.CM.HermSq.kForm_sum_sq | exact GlobalTheory.CM.HermSq.kForm_sum_sq | (intros; apply GlobalTheory.CM.HermSq.kForm_sum_sq <;> assumption)
