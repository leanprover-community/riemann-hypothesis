module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MulAction in
theorem UpperTheory.orbitalFiber_of_bot :
    UpperTheory.V.Z.Sym.Glob.Fib.Bot := by
  intro H Y _ _ H₀ k
  have hmul : ∀ (a : ℂ) (g : orbitRel.Quotient H Y → ℂ), ∑ᶠ o, a * g o = a * ∑ᶠ o, g o :=
    fun a g => by simpa only [smul_eq_mul] using (smul_finsum a g).symm
  refine ⟨fun a => ?_, fun hc htriv => ?_⟩
  · unfold UpperTheory.V.Z.Sym.gq
    rw [← hmul]
    exact finsum_congr fun o => mul_div_assoc _ _ _
  · unfold UpperTheory.V.Z.Sym.gq
    rw [← hmul]
    refine finsum_congr fun o => ?_
    have hle : H₀ ≤ stabilizer H o.out := fun z hz => htriv z hz _
    have h := Subgroup.relIndex_mul_relIndex ⊥ H₀ (stabilizer H o.out) bot_le hle
    rw [Subgroup.relIndex_bot_left] at h
    have hc' : (Nat.card H₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
    rw [← h, Nat.cast_mul, ← mul_div_assoc, mul_div_mul_left _ _ hc']
