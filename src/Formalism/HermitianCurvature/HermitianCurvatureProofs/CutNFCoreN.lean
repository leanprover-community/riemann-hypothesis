module

public import Formalism.HermitianCurvature.StatementMA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section aux

variable {P : M.Par}

theorem nf_actA_fsum (a : MA.A P (MA.DQ P)) {κ : Type} (s : Finset κ) (g : κ → M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (∑ k ∈ s, g k) = ∑ k ∈ s, MA.actA P a (g k) := by
  funext π
  rw [Finset.sum_apply]
  unfold MA.actA
  calc ∑ π', (a π π').1 ((∑ c ∈ s, g c) π') = ∑ π', ∑ c ∈ s, (a π π').1 (g c π') := by
        refine Finset.sum_congr rfl fun π' _ => ?_
        rw [Finset.sum_apply]
        exact map_sum (a π π').1 (fun c => g c π') s
    _ = ∑ c ∈ s, ∑ π', (a π π').1 (g c π') := Finset.sum_comm

theorem nf_norm_sum_sq {E : Type*} [SeminormedAddCommGroup E] {κ : Type*} (s : Finset κ) (a : κ → E) :
    ‖∑ k ∈ s, a k‖ ^ 2 ≤ s.card * ∑ k ∈ s, ‖a k‖ ^ 2 := by
  calc ‖∑ k ∈ s, a k‖ ^ 2 ≤ (∑ k ∈ s, ‖a k‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ s.card * ∑ k ∈ s, ‖a k‖ ^ 2 := sq_sum_le_card_mul_sum_sq

theorem nf_pow_le (G : ℝ) (hG : 0 ≤ G) {a N : ℕ} (ha : a ≤ N) : G ^ a ≤ 1 + G ^ (2 * N) := by
  rcases le_total G 1 with h | h
  · have h1 : G ^ a ≤ 1 := pow_le_one₀ hG h
    have h2 : 0 ≤ G ^ (2 * N) := pow_nonneg hG _
    linarith
  · have h1 : G ^ a ≤ G ^ (2 * N) := pow_le_pow_right₀ h (by omega)
    linarith

end aux

end

end Formalism.FourierDecayAlt.P.CutBP
