module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MK
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMumfordGeneratorAdditiveCubicalStructures
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
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum


theorem _root_.GlobalTheory.T.homMumfordGenerator_additive_cubicalStructures : ∀ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {L₁ : RigLB H₁} {L₂ : RigLB H₂} (c₁ : CubicalStr H₁ L₁) (c₂ : CubicalStr H₂ L₂), (join L₁.L L₂.L).IsLB → Function.Surjective (H₁ ⊗ H₁ ⊗ H₁).hom.appTop.hom → ∀ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (u : LB.Gen (LB.LinComb (join L₁.L L₂.L) (mφ H₁ H₂ a b) mε)), IsNrm u → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ H₁.left ⨿ H₂.left) → (join L₁.L L₂.L).ι), Good (join L₁.L L₂.L) z J → ∀ x x' y : T ⟶ H₁, val u (lift (x * x') y).left z J * cubV c₁ z (rl J) x x' y = cubV c₂ z (rr J) (x ≫ a) (x' ≫ a) (y ≫ b) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV c₁ z (rl J) y x x' = cubV c₂ z (rr J) (y ≫ a) (x ≫ b) (x' ≫ b) * (val u (lift y x).left z J * val u (lift y x').left z J) := by
  first | exact @GlobalTheory.HomMumAdd.pair_add_of_surj | exact GlobalTheory.HomMumAdd.pair_add_of_surj | (intros; apply GlobalTheory.HomMumAdd.pair_add_of_surj <;> assumption)
