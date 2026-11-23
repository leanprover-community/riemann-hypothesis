module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemWeylCellUnitaryGroupLongSimpleReflectionIff
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

@[expose] public section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

theorem _root_.GlobalTheory.T.mem_weylCellUnitaryGroup_longSimpleReflection_iff : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n → ∀ (y : GU σ n),
    IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (u : GU σ n),
    u ∈ cellU y ↔ ∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  first | exact @GlobalTheory.cellU_rankOne_shape | exact GlobalTheory.cellU_rankOne_shape | (intros; apply GlobalTheory.cellU_rankOne_shape <;> assumption)
