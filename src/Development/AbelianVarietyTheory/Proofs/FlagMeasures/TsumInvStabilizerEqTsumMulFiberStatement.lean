module

public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumInvStabilizerEqTsumMulFiber
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped ENNReal

theorem _root_.GlobalTheory.T.tsum_inv_card_stabilizer_eq_tsum_mul_card_fiber : ∀ {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y] (π : L → Y), (∀ (g : Γ) (x : L), π (g • x) = g • π x) → (∀ y : Y, (∃ x, π x = y) → Finite (MulAction.stabilizer Γ y)) → (∑' o : MulAction.orbitRel.Quotient Γ L, (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹) = ∑' o : MulAction.orbitRel.Quotient Γ Y, (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹ * (((π ⁻¹' {o.out}).encard : ℝ≥0∞)) := by
  first | exact @GlobalTheory.tsum_inv_stabilizer_eq_tsum_mul_fiber | exact GlobalTheory.tsum_inv_stabilizer_eq_tsum_mul_fiber | (intros; apply GlobalTheory.tsum_inv_stabilizer_eq_tsum_mul_fiber <;> assumption)
