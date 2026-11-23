module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpL
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilComparisonGeneratorAdditiveSecondVariable
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
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

theorem _root_.GlobalTheory.T.weilComparisonGenerator_additive_second_variable : GlobalFnsSt → ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))) (hr₁ : r₁.IsGen) (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩) (r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))) (hr₂ : r₂.IsGen) (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩) (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1) → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → (join P₁.L P₂.L).ι), Good (join P₁.L P₂.L) z J → ∀ (x y y' : T ⟶ P₀.A), val u (lift x (y * y')).left z J * cubV c₁ z (rl J) (x ≫ f₁) (y ≫ g₁) (y' ≫ g₁) = cubV c₂ z (rr J) (x ≫ f₂) (y ≫ g₂) (y' ≫ g₂) * (val u (lift x y).left z J * val u (lift x y').left z J) := by
  first | exact @GlobalTheory.Mum.Two.WeilCmp.add_snd | exact GlobalTheory.Mum.Two.WeilCmp.add_snd | (intros; apply GlobalTheory.Mum.Two.WeilCmp.add_snd <;> assumption)
