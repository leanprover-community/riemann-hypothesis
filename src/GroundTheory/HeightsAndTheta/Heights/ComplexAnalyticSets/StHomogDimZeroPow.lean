module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsConeAvoid
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
public import Mathlib.RingTheory.MvPolynomial.Ideal
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

def HomogDimZeroPow.Statement : Prop :=
  ∀ (n : ℕ) (K : Ideal (MvPolynomial (Fin n) ℂ)),
    K.IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) ≤ 0 → ∃ N : ℕ, originIdeal n ^ N ≤ K

theorem originIdeal_eq_ker (n : ℕ) :
    originIdeal n = RingHom.ker (constantCoeff : MvPolynomial (Fin n) ℂ →+* ℂ) := by
  ext f
  rw [originIdeal, ← Set.image_univ, mem_ideal_span_X_image, RingHom.mem_ker, constantCoeff_eq]
  constructor
  · intro h
    by_contra h0
    obtain ⟨i, -, hi⟩ := h 0 (mem_support_iff.2 h0)
    exact hi rfl
  · intro h m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact mem_support_iff.1 hm h
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hm0
    exact ⟨i, Set.mem_univ _, hi⟩

theorem originIdeal_isMaximal (n : ℕ) : (originIdeal n).IsMaximal := by
  rw [originIdeal_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, constantCoeff_C _ _⟩)

end

end GroundTheory.Heights₂.Heights.ComplexSets
