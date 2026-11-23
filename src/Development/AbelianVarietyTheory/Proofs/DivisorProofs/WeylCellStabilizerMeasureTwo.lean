module

public import Formalism.SatakeDualWeyl.StatementF
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich

@[expose] public section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory

namespace GKConjScale

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_eq_ofAdd_ordL {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := by simpa using hx
  unfold ordL
  rw [dite_eq_right h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

theorem coe_mul_le_iff (g h : Multiplicative ℤ) (x : WithZero (Multiplicative ℤ)) :
    (g : WithZero (Multiplicative ℤ)) * x ≤ h ↔ x ≤ ((g⁻¹ * h : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  constructor
  · intro H
    calc x = ((g⁻¹ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * (g * x) := by
          rw [← mul_assoc, ← WithZero.coe_mul, inv_mul_cancel, WithZero.coe_one, one_mul]
      _ ≤ ((g⁻¹ : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) * h := by gcongr
      _ = _ := by rw [WithZero.coe_mul]
  · intro H
    calc (g : WithZero (Multiplicative ℤ)) * x ≤ g * ((g⁻¹ * h : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
          by gcongr
      _ = h := by rw [WithZero.coe_mul, ← mul_assoc, ← WithZero.coe_mul, mul_inv_cancel, WithZero.coe_one, one_mul]

variable {n : ℕ}

theorem inv_offdiag {σ : L →+* L} (t : GU σ n)
    (ht : ∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) (i j : Fin n) (hij : i ≠ j) :
    (((t⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  rw [Subgroup.coe_inv, (GlobalTheory.LGrp.mem_GU_iff σ n _).1 t.2 i j,
    ht _ _ (fun h => hij (Fin.rev_injective h).symm), map_zero]


end GKConjScale

end GlobalTheory
