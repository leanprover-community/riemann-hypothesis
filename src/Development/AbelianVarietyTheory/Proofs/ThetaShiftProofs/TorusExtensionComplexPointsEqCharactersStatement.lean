module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtensionComplexPointsEqCharacters
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.torusExtension_complexPoints_eq_characters : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g : ℕ) (u : HolUnif D.P.A D.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (ct : D.X →+ (Fin g → ℂ)), u.IsAH Hm χ → u.IsRig D.rig → (∀ x, u.ex (ct x) = D.c x) → ∀ z : Fin g → ℂ, (∀ lam : D.X →+ ℂ, ∃! p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left ∧ ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x)) ∧ ∀ p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left → ∃ lam : D.X →+ ℂ, ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x) := by
  first | exact @GlobalTheory.TorusExtChar.points_eq_characters | exact GlobalTheory.TorusExtChar.points_eq_characters | (intros; apply GlobalTheory.TorusExtChar.points_eq_characters <;> assumption)
