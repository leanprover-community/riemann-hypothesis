module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTensorRightOperator
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

open GlobalTheory.SliceSchwartz

theorem _root_.GlobalTheory.T.schwartz_tensor_right_operator : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type)
    [Fintype κ] [Fintype κ'] [Fintype κ₁'] (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ),
    ∃ Q : SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ₁' → V) ℂ,
      ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V), Q f s = P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr) := by
  first | exact @GlobalTheory.SliceOp.exists_tensor_clm | exact GlobalTheory.SliceOp.exists_tensor_clm | (intros; apply GlobalTheory.SliceOp.exists_tensor_clm <;> assumption)
