module

public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import GroundTheory.ArithmeticGeometry.ToricVarieties.KrullDomain
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem HeightOneIntersection.proof : HeightOneIntersection.Statement := by
  intro A _ _ _ _ K _ _ _
  apply le_antisymm
  · intro x hx
    simp only [Submodule.mem_iInf]
    intro p _
    exact ⟨1, (Ideal.ne_top_iff_one _).mp p.isPrime.ne_top, by rwa [one_smul]⟩
  · intro x hx
    simp only [Submodule.mem_iInf] at hx
    change x ∈ (⊥ : Subalgebra A K)
    rw [Algebra.mem_bot]
    obtain ⟨y, hy⟩ := GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := A) (K := K) x
      (fun p hp h1 => by
        obtain ⟨s, hs, hsx⟩ := hx ⟨p, hp⟩ h1
        change s • x ∈ (⊥ : Subalgebra A K) at hsx
        obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hsx
        refine ⟨a, s, hs, ?_⟩
        rw [Algebra.smul_def] at ha
        rw [ha, mul_comm])
    exact ⟨y, hy⟩

end GroundTheory.Heights₂.Heights.Model
