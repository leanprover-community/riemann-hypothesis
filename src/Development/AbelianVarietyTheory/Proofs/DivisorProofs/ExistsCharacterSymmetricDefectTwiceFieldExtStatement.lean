module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharacterSymmetricDefectTwiceFieldExt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_character_symmetricDefect_twice_fieldExt : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k → IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] [IsCommMonObj G'₀] (β₀ : G'₀.left ⟶ G₀.left) (hβ₀ : IsGrpPullback G'₀ G₀ (spMap ρ) β₀) (P₀ : GlobalTheory.UU.CP G₀) (P'₀ : GlobalTheory.UU.CP G'₀) (w₀ : LB.Iso P'₀.L.L (P₀.L.L.pull β₀)), GlobalTheory.UU.IsCPMap P'₀ P₀ (spMap ρ) β₀ hβ₀.1.w w₀ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G₀) (i₁ : splitTorus (Sp k') X ⟶ G'₀), IsMonHom i → IsMonHom i₁ → GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ i → ∀ (σ : GlobalTheory.UU.CubTriv P₀.c i) (σ₁ : GlobalTheory.UU.CubTriv P'₀.c i₁), GlobalTheory.UU.CubTriv.Even (P := P'₀) σ₁ → ∃ χ : X, GlobalTheory.UU.CubTriv.Even (P := P₀) (σ.twist χ) := by
  first | exact @GlobalTheory.TwistCompare.exists_twist_even | exact GlobalTheory.TwistCompare.exists_twist_even | (intros; apply GlobalTheory.TwistCompare.exists_twist_even <;> assumption)
