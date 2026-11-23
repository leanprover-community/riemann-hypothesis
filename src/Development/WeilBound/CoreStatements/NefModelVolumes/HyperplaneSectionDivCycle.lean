module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

namespace ChowFormCompatibility

theorem projCycle_eq_fundCycle {k : Type} [Field k] {N : ℕ} (J : Ideal (MvPolynomial (Fin N) k)) :
    GlobalTheory.ChowHt.projCycle J = GroundTheory.Heights₂.Heights.fundCycle J := by
  ext Q
  rw [GroundTheory.Heights₂.Heights.fundCycle, Finsupp.onFinset_apply]
  by_cases hQ : Q ∈ GroundTheory.Heights₂.Heights.relComps J
  · haveI hp : Q.IsPrime := hQ.1.1.1
    have h1 := GlobalTheory.ChowHt.cast_projCycle_apply (J := J) (Q := Q) hQ
    rw [if_pos hQ, GroundTheory.Heights₂.Heights.localMult, dite_eq_left hp]
    have h2 := congrArg ENat.toNat h1
    rw [ENat.toNat_coe] at h2
    exact h2
  · rw [if_neg hQ]
    exact GlobalTheory.ChowHt.projCycle_apply_of_notMem hQ

theorem hyperplane_section_divCycle : ∀ (k : Type) [Field k] (N B : ℕ) (P : Ideal (MvPolynomial (Fin N) k)) (u : Fin N → k) (f : MvPolynomial (Fin (B + 1) × Fin N) k), GlobalTheory.ChowHt.hyperplaneSection P u = GroundTheory.Heights₂.Heights.divCycle P u ∧ GlobalTheory.ChowHt.fixFirstBlock u f = GroundTheory.Heights₂.Heights.specFirst f u := by
  intro k _ N B P u f
  refine ⟨projCycle_eq_fundCycle _, ?_⟩
  have h : (fun p : Fin (B + 1) × Fin N =>
      (Fin.cons (fun j => C (u j)) (fun b j => X (b, j)) :
        Fin (B + 1) → Fin N → MvPolynomial (Fin B × Fin N) k) p.1 p.2) =
      GroundTheory.Heights₂.Heights.specFirstVar u := by
    funext ⟨b, j⟩
    induction b using Fin.cases with
    | zero => rfl
    | succ b => rfl
  rw [GlobalTheory.ChowHt.fixFirstBlock, h]
  rfl

end ChowFormCompatibility
