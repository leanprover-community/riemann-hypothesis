module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Coinv

noncomputable section

theorem CoinvStaircaseComponent.proof (h1 : CoinvStaircaseDegree.Statement) :
    CoinvStaircaseComponent.Statement := by
  intro K _ f n v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he, rfl⟩ := hx
    have hhom : monomial e (1 : K) ∈ homogeneousSubmodule (Fin f × Fin n) K e.degree :=
      (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial 1 rfl)
    obtain ⟨hle, heq⟩ := h1 f n e he
    refine ⟨fun d hd => ?_, ?_⟩
    · rw [homogeneousComponent_of_mem hhom, if_neg (by omega)]
    · rw [homogeneousComponent_of_mem hhom]
      by_cases h : coinvTop f n = e.degree
      · refine ⟨1, ?_⟩
        rw [if_pos h, heq h.symm, C_1, one_mul]
      · exact ⟨0, by rw [if_neg h, C_0, zero_mul]⟩
  | zero => exact ⟨fun d _ => map_zero _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, cx, hx2⟩ := hx
    obtain ⟨hy1, cy, hy2⟩ := hy
    refine ⟨fun d hd => by rw [map_add (f := _), hx1 d hd, hy1 d hd, add_zero], cx + cy, ?_⟩
    rw [map_add (f := _), hx2, hy2, C_add, add_mul]
  | smul a x _ hx =>
    obtain ⟨hx1, cx, hx2⟩ := hx
    refine ⟨fun d hd => by rw [map_smul, hx1 d hd, smul_zero], a * cx, ?_⟩
    rw [map_smul, hx2, smul_eq_C_mul, C_mul, mul_assoc]

end

end GroundTheory.Heights₂.Heights.RestTerms
