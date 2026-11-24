module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SmoothRepIrreducibleSubcontainingVector
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

noncomputable section

namespace UpperTheory.NonzeroTypeTheory

namespace SchurKernelSubmodule

def kerSub {K : Type} [Group K] {d : ℕ} (ξ : Representation ℂ K (Fin d → ℂ)) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ K W) (g : (Fin d → ℂ) →ₗ[ℂ] W)
    (hint : ∀ k v, g (ξ k v) = ρ k (g v)) : Subrepresentation ξ :=
  ⟨LinearMap.ker g, fun k v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hint, hv, map_zero]⟩

end SchurKernelSubmodule

open SchurKernelSubmodule in
theorem schurInjective_holds : SchurInjectiveFromIrreducible := by
  intro K _ d ξ hξ W _ _ ρ g hg hint
  haveI : IsSimpleOrder (Subrepresentation ξ) := hξ
  rcases eq_bot_or_eq_top (kerSub ξ ρ g hint) with h | h
  · rw [← LinearMap.ker_eq_bot]
    have hk := congrArg Subrepresentation.toSubmodule h
    first
      | exact hk
  · exfalso
    apply hg
    rw [← LinearMap.ker_eq_top]
    have hk := congrArg Subrepresentation.toSubmodule h
    first
      | exact hk

end UpperTheory.NonzeroTypeTheory
