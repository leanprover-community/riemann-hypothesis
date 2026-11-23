module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFibMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

theorem self_adjoint_zero_holds : SAZero := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he X hX y hy h0
  have hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hw : 0 < Real.sqrt (MA.wq S.G.k y (D.parOf S v).TT) := by
    apply Real.sqrt_pos.2
    unfold MA.wq
    exact mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hy.1 l)) _)
      (pow_pos (sub_pos.2 hy.2) _)
  have hin : ∀ π, inner ℂ (B.hsVec (e π y.2)) (B.hsVec (X (B.gq (T v).base y))) = 0 := by
    intro π
    have hsm := En.trace_smoothness E Wp Wq S T v hplace e he X hX π
    have h := h0 π
    unfold trJ at h
    rw [En.toSm_val_of_mem _ hsm] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (Complex.ofReal_ne_zero.2 hw.ne')
    · exact h
  have hfib := En.fibre_membership_holds E Wp Wq S T v hplace X hX y hy
  rw [(he.2 y.2 hy.2).2.2 _ hfib]
  simp [hin]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
