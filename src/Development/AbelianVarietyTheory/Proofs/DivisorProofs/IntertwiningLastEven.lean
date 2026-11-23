module

public import Formalism.SatakeDualWeyl.StatementF
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.WeylCell.RankOneUnitary

theorem chiDeltaU_congr {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n m : ℕ}
    (q : ℕ) (α : Fin m → ℂ) (b c : GU σ n)
    (h : ∀ i, ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) :
    chiDeltaU q α b = chiDeltaU q α c := by
  unfold chiDeltaU
  simp only [h]

end GlobalTheory.WeylCell.RankOneUnitary

namespace GlobalTheory.WeylCell.RankOneUnitary

theorem ordL_of_v_eq {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (x : L) (z : ℤ)
    (hx : Valued.v x = ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) : ordL x = -z := by
  unfold ordL
  have h0 : Valued.v x ≠ 0 := by rw [hx]; exact WithZero.coe_ne_zero
  rw [dite_eq_right h0]
  have : WithZero.unzero h0 = Multiplicative.ofAdd z := by
    apply WithZero.coe_injective; rw [WithZero.coe_unzero, hx]
  rw [this]; rfl

end GlobalTheory.WeylCell.RankOneUnitary

end
