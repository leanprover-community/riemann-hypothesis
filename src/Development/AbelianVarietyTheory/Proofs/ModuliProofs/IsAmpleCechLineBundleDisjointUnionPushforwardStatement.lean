module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleCechLineBundleDisjointUnionPushforward
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

theorem _root_.GlobalTheory.T.isAmpleCechLineBundle_disjointUnion_pushforward : ∀ (Z Z₁ Z₂ : Scheme.{0}) (f₁ : Z₁ ⟶ Z) (f₂ : Z₂ ⟶ Z) [IsOpenImmersion f₁] [IsOpenImmersion f₂] (A₁ : LB Z₁) (A₂ : LB Z₂), IsCompl (Set.range f₁) (Set.range f₂) → A₁.IsLB → A₂.IsLB → AmpleFam A₁ → AmpleFam A₂ → (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)).IsLB ∧ AmpleFam (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)) := by
  first | exact @GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam | exact GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam | (intros; apply GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam <;> assumption)
