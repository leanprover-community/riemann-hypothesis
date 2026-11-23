module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.Development
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace QmCapCommW

theorem quantum_determinant_commutes : QdetCommute := by
  intro A _ _ n E hE u v
  have hc : ∀ c d, Commute (qdet E u) (E c d) := fun c d => qDetCentral A n E hE u c d
  have hT : ∀ w a b, Commute (qdet E u) (Tm E w a b) := by
    intro w a b
    unfold Tm
    refine Commute.add_right ?_ (hc a b)
    split_ifs
    · exact Algebra.commute_algebraMap_right w _
    · exact Commute.zero_right _
  have key : Commute (qdet E u) (qdet E v) := by
    show Commute (qdet E u) (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin n => Tm E (v - (k : ℂ)) (id (σ k)) (id k)).prod)
    refine Commute.sum_right _ _ _ fun σ _ => ?_
    refine Commute.mul_right Commute.intCast_right ?_
    refine Commute.list_prod_right _ _ fun y hy => ?_
    simp only [List.mem_ofFn] at hy
    obtain ⟨k, rfl⟩ := hy
    exact hT _ _ _
  exact key.eq

end QmCapCommW
