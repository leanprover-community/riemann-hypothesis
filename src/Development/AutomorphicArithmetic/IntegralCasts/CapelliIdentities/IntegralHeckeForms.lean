module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

attribute [local instance] Submodule.module._proof_1 Formalism.MainNotions.S.lf._proof_1 Formalism.MainNotions.S.starE

theorem UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul :
    ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E}
    (F0 : Formalism.MainNotions.S.FlagG (Formalism.MainNotions.S.VS D) D.R.rS T)
    (M : Submodule (NumberField.RingOfIntegers D.host.E) (Formalism.MainNotions.S.WbQ D F0)),
    Submodule.span D.host.E (↑M : Set (Formalism.MainNotions.S.WbQ D F0)) = ⊤ →
      ∀ (m : Formalism.MainNotions.S.WbQ D F0),
        ∃ (k : ℕ),
          k ≠ (0 : ℕ) ∧
            (↑k : NumberField.RingOfIntegers D.host.E) • m ∈
              M := by
  intro D T F0 M h m
  simp only [Nat.cast_smul_eq_nsmul]
  refine Submodule.span_induction (p := fun x _ => ∃ k : ℕ, k ≠ 0 ∧ k • x ∈ M)
    (fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩) ⟨1, one_ne_zero, by simp⟩ ?_ ?_
    (h ▸ Submodule.mem_top : m ∈ Submodule.span D.host.E (M : Set _))
  · rintro x y - - ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    exact ⟨a * b, mul_ne_zero ha hb, by
      rw [smul_add, mul_nsmul' y, mul_nsmul x]; exact M.add_mem (nsmul_mem hx b) (nsmul_mem hy a)⟩
  · rintro c x - ⟨a, ha, hx⟩
    obtain ⟨b, s, hb, hs⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2
      (Algebra.IsAlgebraic.isAlgebraic c)).exists_nsmul_eq (NumberField.RingOfIntegers D.host.E)
    exact ⟨b * a, mul_ne_zero hb ha, by
      rw [mul_smul, smul_comm a c, ← smul_assoc, hs, algebraMap_smul]; exact M.smul_mem s hx⟩
