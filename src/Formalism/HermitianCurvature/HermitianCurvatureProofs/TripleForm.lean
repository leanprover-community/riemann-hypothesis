module

public import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A5x1

theorem lamN_last {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (j : ℕ) (hj : j + 1 = n) : lamN R Z j = lamLin R Z := by
  unfold lamN lamTil lamLin rowN lastCoord
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  have : (a.val = j ↔ a.val + 1 = n) := by omega
  simp [this]

end Formalism.FourierDecayAlt.P.A5x1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A5x1

theorem tripleForm : Formalism.FourierDecayAlt.A5.TripleForm := by
  intro K _ R ψ w w' k hw hw'
  unfold Kp intTT pairTerm
  apply finsum_congr
  intro q
  congr 2
  split_ifs with hI
  · congr 1
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro φ
    constructor
    · intro hφ
      refine ⟨hφ, ?_⟩
      intro j hkj hjn
      have hj : j = k := by omega
      subst hj
      refine ⟨0, ?_⟩
      intro v v' hv
      have h2 := hφ.2 v v' hv
      rw [lamN_last R _ j hw'.symm, lamN_last R _ j hw.symm, h2]
      simp
    · exact fun h => h.1
  · rfl

end Formalism.FourierDecayAlt.P
