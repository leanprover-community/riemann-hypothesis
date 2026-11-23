module

public import Formalism.UnipotentAdelicQuotients.StdAdditiveCharExists
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.BridgeStdAddChar
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

open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdelicChar

theorem exists_isCharAF_of_std :
    HeckeCharacterZeroLocus.StdAdditiveCharExists → ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F →
      ∃ ψ, IsCharAF F ψ := by
  intro h F _ _ hF
  obtain ⟨ψ, h1, h2, h3, h4, -⟩ := h F hF
  exact ⟨ψ, h1, h2, h3, h4⟩

theorem exists_isCharAF (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyReal F) :
    ∃ ψ, IsCharAF F ψ :=
  exists_isCharAF_of_std PI.Bridge.bridge_stdAddChar F hF

end GlobalTheory.CompanionTheory.AdelicChar
