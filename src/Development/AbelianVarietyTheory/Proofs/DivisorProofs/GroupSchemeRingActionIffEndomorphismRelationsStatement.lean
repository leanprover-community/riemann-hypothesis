module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeRingActionIffEndomorphismRelations
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.groupScheme_ringAction_iff_endomorphism_relations : ∀ (O : Type) [Ring O] (r : ℕ) (e : Fin r → O), Submodule.span ℤ (Set.range e) = ⊤ → ∃ (m : ℕ) (N : Fin m → Fin r → ℤ) (c1 : Fin r → ℤ) (cm : Fin r → Fin r → Fin r → ℤ), ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (f : Fin r → (A ⟶ A)), (∀ k, IsMonHom (f k)) → ((∃ act : O → (A ⟶ A), IsRAct A act ∧ ∀ k, act (e k) = f k) ↔ ((∀ j, ∏ k, f k ^ N j k = 1) ∧ ∏ k, f k ^ c1 k = 𝟙 A ∧ ∀ i j, f i ≫ f j = ∏ k, f k ^ cm i j k)) := by
  first | exact @GlobalTheory.ActRel.ringAct_iff_relations | exact GlobalTheory.ActRel.ringAct_iff_relations | (intros; apply GlobalTheory.ActRel.ringAct_iff_relations <;> assumption)
