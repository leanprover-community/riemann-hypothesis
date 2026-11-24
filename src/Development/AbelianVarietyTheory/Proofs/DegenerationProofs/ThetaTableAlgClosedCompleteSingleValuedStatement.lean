module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTableAlgClosedCompleteSingleValued
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.thetaTable_algClosed_complete_singleValued : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m n r : ℕ), Odd m → Odd n → ∀ (th : SecA A F 1) (τ : Fin r → SecA A F (m ^ 2)), (∀ t, ∃! a, Cmb τ a t) → (tab ρ m th τ).Full (m ^ 2) n ∧ (tab ρ m th τ).Uniq (m ^ 2) n := by
  first | exact @GlobalTheory.tab_full_uniq | exact GlobalTheory.tab_full_uniq | (intros; apply GlobalTheory.tab_full_uniq <;> assumption)
