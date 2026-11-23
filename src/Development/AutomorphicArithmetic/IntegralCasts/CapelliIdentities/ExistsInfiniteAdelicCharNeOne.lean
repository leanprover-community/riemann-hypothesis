module

public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.Reformulated.B.Rd3.exists_infiniteAdelicChar_ne_one :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (w : NumberField.InfinitePlace F),
    ∃ (z : w.Completion),
      (GroundTheory.Global.infiniteAdelicChar F w : w.Completion → Circle) z ≠
        (1 : Circle) := by
  intro F _ _ w
  refine ⟨((2 * w.mult : ℕ) : w.Completion)⁻¹, fun h => ?_⟩
  have hm : (w.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr NumberField.InfinitePlace.mult_pos.ne'
  have hx : 2 * Real.pi * -((w.mult : ℝ) * (((2 * w.mult : ℕ) : ℝ))⁻¹) = -Real.pi := by
    push_cast
    field_simp
  rw [GroundTheory.Global.infiniteAdelicChar_apply, map_inv₀, map_natCast, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.ofReal_re] at h
  have h2 := congrArg (fun c : Circle => (c : ℂ)) h
  simp only [Real.fourierChar_apply, hx, Circle.coe_one] at h2
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I] at h2
  norm_num at h2
