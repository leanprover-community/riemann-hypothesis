module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackOfCoprodJoin
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.exists_lineBundleIso_pullback_of_coprodJoin : ∀ {X₁ X₂ : Scheme.{0}} (M : LB X₁) (M' : LB X₂), M.IsLB → M'.IsLB → Nonempty X₁ → Nonempty X₂ → ∀ (F : X₂ ⟶ X₁) (t : LB.Gen (LB.LinComb (join M' M) (Sum.elim (fun _ : PUnit => F ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (-1 : ℤ))))), t.IsGen → ∃ w : LB.Iso M' (M.pull F), w.IsGen ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ X₂) (z : Z) (J : (Z ⟶ X₂ ⨿ X₁) → (join M' M).ι), Good (join M' M) z J → gw w f z (rr J (f ≫ F)) (rl J f) = val t f z J := by
  first | exact @GlobalTheory.JoinPull.exists_iso_of_joinGen | exact GlobalTheory.JoinPull.exists_iso_of_joinGen | (intros; apply GlobalTheory.JoinPull.exists_iso_of_joinGen <;> assumption)
