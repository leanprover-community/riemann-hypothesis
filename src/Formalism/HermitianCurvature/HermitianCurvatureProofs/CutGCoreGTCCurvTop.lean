module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCTheta
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem thetaC_eq_thetaNF {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A)
    (hTT : d.L.TT = (P.TT : ℂ)) : ThetaC d = ThetaNF P d := by
  unfold ThetaC ThetaNF
  rw [hTT]
  congr 3
  funext ρ
  rw [aC_eq]
  push_cast
  ring

theorem gTRTopNF_of_curvPoly (h : GTCCurvPoly) : GTRTopNF := by
  intro P A _ _ _ d _ hk _ hRel hTT
  obtain ⟨⟨a, ha⟩, -⟩ := h P A d hRel hk hTT
  have hk1 : P.k - 1 + 1 = P.k := by omega
  refine ⟨fun j => if j = P.k + 1 then 1 else if j = P.k then ThetaC d else if j < P.k then a j else 0,
    fun Y => ?_, 0, ?_⟩
  · have e := ha Y
    rw [hk1] at e
    dsimp only at e ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [show P.k ≠ P.k + 1 by omega, ↓reduceIte]
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [if_neg (by have := Finset.mem_range.1 hj; omega), if_neg (by have := Finset.mem_range.1 hj; omega),
        if_pos (Finset.mem_range.1 hj)]), ← e]
    abel
  · simp only [show P.k ≠ P.k + 1 by omega, if_false, if_true, Int.cast_zero, zero_smul, add_zero]
    exact thetaC_eq_thetaNF d hTT

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
