module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetricLiftNormalisedPullbackThetaSmul
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

theorem _root_.GlobalTheory.T.symmetricLift_normalisedPullback_theta_smul : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th th' : SecA A F 1) (c : F), (∀ j, th.f j = liftFun A.A _ (cF R c) * th'.f j) → ∀ (s₁ σ t : SecA A F (m ^ 2)) (x : TFK (R := R) F ⟶ A.A) (θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := R) F)) (c' : F), x ^ (m ^ 2) = 1 → IsNormPull A ρ m (m ^ 2) th s₁ → SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ → IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₁ σ → ThC A ρ m th' x t c' → ∀ j, σ.f j = liftFun A.A _ (cF R c) * t.f j := by
  first | exact @GlobalTheory.TestFibre.act_normPull_smul | exact GlobalTheory.TestFibre.act_normPull_smul | (intros; apply GlobalTheory.TestFibre.act_normPull_smul <;> assumption)
