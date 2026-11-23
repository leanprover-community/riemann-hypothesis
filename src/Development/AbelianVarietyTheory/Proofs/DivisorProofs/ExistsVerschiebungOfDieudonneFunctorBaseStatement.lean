module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVerschiebungOfDieudonneFunctorBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_verschiebung_of_dieudonneFunctorBase : ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p (fun _ _ _ => True)), ∃ V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k), B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] B.M G trivial, (∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial), B.F G trivial (V G m) = p • m) ∧ ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial), V G (B.F G trivial m) = p • m := by
  first | exact @GlobalTheory.Dieu.exists_V_of_base | exact GlobalTheory.Dieu.exists_V_of_base | (intros; apply GlobalTheory.Dieu.exists_V_of_base <;> assumption)
