module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResCharIff
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField

namespace PI.ProdFormulaE.ResCharP

theorem eq_iff_mem_asIdeal : St.ResCharIff := by
  intro F _ _ p ℓ hℓ
  show ringChar (𝓞 F ⧸ p.asIdeal) = ℓ ↔ _
  haveI : p.asIdeal.IsPrime := p.isPrime
  have hz : ((ℓ : 𝓞 F ⧸ p.asIdeal) = 0) ↔ (ℓ : 𝓞 F) ∈ p.asIdeal := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  rw [← hz]
  constructor
  · intro h
    rw [← h]
    exact ringChar.Nat.cast_ringChar
  · intro h
    rcases hℓ.eq_one_or_self_of_dvd _ (ringChar.dvd h) with h1 | h1
    · exfalso
      have hc := ringChar.Nat.cast_ringChar (R := 𝓞 F ⧸ p.asIdeal)
      rw [h1, Nat.cast_one] at hc
      exact one_ne_zero hc
    · exact h1

end PI.ProdFormulaE.ResCharP
