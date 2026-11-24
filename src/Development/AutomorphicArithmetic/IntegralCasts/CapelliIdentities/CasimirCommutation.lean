module

public import Formalism.RealPlaceAnalysis.StatementA
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm :
    ∀ {A : Type} [inst : Ring A] {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → A),
      Formalism.REAL.GlRel E → ∀ (c d : Fin n), ε c = ε d → Formalism.REAL.CasK ε E * E c d = E c d * Formalism.REAL.CasK ε E := by
  intro A _ n ε E h c d hcd
  have key : ∀ a b, E a b * E b a * E c d - E c d * (E a b * E b a) =
      E a b * (if a = c then E b d else 0) - E a b * (if d = b then E c a else 0)
        + (if b = c then E a d else 0) * E b a - (if d = a then E c b else 0) * E b a := by
    intro a b
    have h1 := h b a c d
    have h2 := h a b c d
    have : E a b * (if a = c then E b d else 0) - E a b * (if d = b then E c a else 0)
        + (if b = c then E a d else 0) * E b a - (if d = a then E c b else 0) * E b a
        = E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0))
          + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a := by
      noncomm_ring
    rw [this, ← h1, ← h2]
    noncomm_ring
  have S1 : ∑ a, ∑ b, (if ε a = ε b then E a b * (if a = c then E b d else 0) else 0)
      = ∑ b, if ε c = ε b then E c b * E b d else 0 := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
    simp
  have S4 : ∑ a, ∑ b, (if ε a = ε b then (if d = a then E c b else 0) * E b a else 0)
      = ∑ b, if ε d = ε b then E c b * E b d else 0 := by
    rw [Finset.sum_eq_single d (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  have S2 : ∑ a, ∑ b, (if ε a = ε b then E a b * (if d = b then E c a else 0) else 0)
      = ∑ a, if ε a = ε d then E a d * E c a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single d (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  have S3 : ∑ a, ∑ b, (if ε a = ε b then (if b = c then E a d else 0) * E b a else 0)
      = ∑ a, if ε a = ε c then E a d * E c a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have e : Formalism.REAL.CasK ε E * E c d - E c d * Formalism.REAL.CasK ε E =
      ∑ a, ∑ b, (if ε a = ε b then E a b * E b a * E c d - E c d * (E a b * E b a) else 0) := by
    simp only [Formalism.REAL.CasK, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have e2 : ∑ a, ∑ b, (if ε a = ε b then E a b * E b a * E c d - E c d * (E a b * E b a) else 0)
      = ∑ a, ∑ b, (if ε a = ε b then E a b * (if a = c then E b d else 0) else 0)
        - ∑ a, ∑ b, (if ε a = ε b then E a b * (if d = b then E c a else 0) else 0)
        + ∑ a, ∑ b, (if ε a = ε b then (if b = c then E a d else 0) * E b a else 0)
        - ∑ a, ∑ b, (if ε a = ε b then (if d = a then E c b else 0) * E b a else 0) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [key]
    split_ifs <;> simp
  rw [← sub_eq_zero, e, e2, S1, S2, S3, S4, hcd]
  abel
