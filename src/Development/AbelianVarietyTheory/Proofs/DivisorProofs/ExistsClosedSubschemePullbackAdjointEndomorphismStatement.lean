module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemePullbackAdjointEndomorphism
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_closedSubscheme_pullback_adjoint_endomorphism_pair : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (f f' : A ⟶ A), IsMonHom f → IsMonHom f' → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (g g' : A' ⟶ A'), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → g.left ≫ φ' = φ' ≫ f.left → g'.left ≫ φ' = φ' ≫ f'.left → (LBIso ((Q.pull φ₂').pull (lift (fst A' A' ≫ g) (snd A' A')).left) ((Q.pull φ₂').pull (lift (fst A' A') (snd A' A' ≫ g')).left) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  first | exact @GlobalTheory.EndLoc.exists_closed_adj | exact GlobalTheory.EndLoc.exists_closed_adj | (intros; apply GlobalTheory.EndLoc.exists_closed_adj <;> assumption)
