module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
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

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM
open scoped ComplexConjugate

namespace GlobalTheory.CompanionTheory.ThetaReal

theorem thetaSum_star_and_schA_star (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    thetaSum F (star Φ) = conj (thetaSum F Φ) ∧ (Φ ∈ schA F κ → star Φ ∈ schA F κ) := by
  refine ⟨?_, fun h => ?_⟩
  · unfold thetaSum
    rw [← RCLike.star_def, tsum_star]
    rfl
  · classical
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg, rfl⟩ := hx
      refine Submodule.subset_span ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) f, star g,
        ⟨hg.1.comp star, hg.2.comp_left (g := star) (star_zero ℂ)⟩, ?_⟩
      funext x
      simp [pureA]
    | zero => rw [star_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
    | smul a x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.CompanionTheory.ThetaReal
