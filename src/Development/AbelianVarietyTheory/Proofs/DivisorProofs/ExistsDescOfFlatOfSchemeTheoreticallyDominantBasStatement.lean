module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescOfFlatOfSchemeTheoreticallyDominantBas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open CategoryTheory Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.exists_desc_of_flat_of_schemeTheoreticallyDominant_base : ∀ {S S' U U' X Y Y' YU Y'' : Scheme.{0}} (f : S' ⟶ S) (j : U ⟶ S) (f' : U' ⟶ U) (j' : U' ⟶ S') [Flat f] [Surjective f] [QuasiCompact f] [QuasiCompact j] [IsSchemeTheoreticallyDominant j], IsPullback j' f' f j → ∀ (x : X ⟶ S) [IsSeparated x] (y : Y ⟶ S) [Flat y] (y' : Y' ⟶ S') (π : Y' ⟶ Y), IsPullback π y' y f → ∀ (yU : YU ⟶ U) (ιY : YU ⟶ Y), IsPullback ιY yU y j → ∀ (y'' : Y'' ⟶ U') (c : Y'' ⟶ Y') (cU : Y'' ⟶ YU), IsPullback c y'' y' j' → IsPullback cU y'' yU f' → cU ≫ ιY = c ≫ π → ∀ (h' : Y' ⟶ X) (hU : YU ⟶ X), h' ≫ x = y' ≫ f → c ≫ h' = cU ≫ hU → ∃ h : Y ⟶ X, π ≫ h = h' ∧ ιY ≫ h = hU ∧ h ≫ x = y := by
  first | exact @GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant | exact GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant | (intros; apply GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant <;> assumption)
