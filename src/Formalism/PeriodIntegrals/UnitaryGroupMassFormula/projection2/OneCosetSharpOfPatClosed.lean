module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Assemble
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

namespace PI.OneCosetSharp.W

theorem oneCosetSharp_of (h1 : Claim1) (h2 : Claim2) : OneCosetSharp := by
  intro k _ _ ψ₀ χ k₀ m t j n' c n hk hm hm4 hj1 hj2 hc ha hb
  exact ⟨h1 k ψ₀ χ k₀ m t j n' c n ⟨hk, hm, hm4, hj1, hj2, hc, ha, hb⟩ ,
    h2 k ψ₀ χ k₀ m t j n' c n ⟨hk, hm, hm4, hj1, hj2, hc, ha, hb⟩⟩

theorem oneCosetSharp_of_patClosed (hP : PatClosed) (hK : KappaZero) (hN : NElem) (hG : GaStep) (h2 : Claim2) :
    OneCosetSharp :=
  oneCosetSharp_of (claim1_of hP hK hN hG) h2

end PI.OneCosetSharp.W
