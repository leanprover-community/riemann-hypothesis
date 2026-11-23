module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
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
theorem _root_.GlobalTheory.T.galoisCover_descent_and_cartesian_squares : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → (∀ (Z : Scheme.{0}) (f : X ⟶ Z), (∀ a, ρ a ≫ f = f) → ∃! f' : Y ⟶ Z, π ≫ f' = f) ∧ (∀ (T : Scheme.{0}) (x x' : T ⟶ X), x ≫ π = x' ≫ π → ∀ p : T, ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') ∧ ∀ (X' Y' : Scheme.{0}) (π' : X' ⟶ Y') (ρ' : Ga → (X' ⟶ X')) (u : X' ⟶ X) (v : Y' ⟶ Y), (∀ a, ρ' a ≫ u = u ≫ ρ a) → u ≫ π = π' ≫ v → (IsGaloisCover Ga ρ' π' → IsPullback u π' π v) ∧ (IsPullback u π' π v → (∀ a, ρ' a ≫ π' = π') → IsGaloisCover Ga ρ' π') := by
  first | exact @GlobalTheory.ZM.galoisCover_descent | exact GlobalTheory.ZM.galoisCover_descent | (intros; apply GlobalTheory.ZM.galoisCover_descent <;> assumption)
