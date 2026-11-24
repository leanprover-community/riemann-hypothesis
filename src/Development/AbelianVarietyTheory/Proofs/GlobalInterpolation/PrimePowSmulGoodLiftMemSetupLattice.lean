module

public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory

theorem goodLift_pow_smul_mem : ∀ (g : ℕ) (S : JMB.Setup g) (p : ℕ) [Fact p.Prime] (lam : JMB.Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.Ok →
    ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d,
      ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧
      ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x}, ((p : ℂ) ^ n) • y ∈ S.La := by
  intro g S p _ lam N₀ n hS y hy
  have hw : ∀ x ∈ S.La, JMB.w0 S.d • x ∈ S.La := hS.2.2.2.2.2.1
  have hzs : ∀ (z : ℤ) (x : Fin g → ℂ), x ∈ S.La → ((z : ℂ)) • x ∈ S.La := by
    intro z x hx
    rw [Int.cast_smul_eq_zsmul ℂ z x]
    exact S.La.smul_mem z hx
  have hp : ((p : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨κ, ⟨u, v, hκ⟩, _, x, hx, rfl⟩ := hy
    rw [smul_smul, mul_div_cancel₀ _ hp, hκ]
    have : ((u : ℂ) + (v : ℂ) * JMB.w0 S.d) * (N₀ : ℂ) = ((u * N₀ : ℤ) : ℂ) + ((v * N₀ : ℤ) : ℂ) * JMB.w0 S.d := by
      push_cast; ring
    rw [this, add_smul, mul_smul]
    exact S.La.add_mem (hzs _ _ hx) (hzs _ _ (hw x hx))
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact S.La.add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact S.La.neg_mem ha

end GlobalTheory
