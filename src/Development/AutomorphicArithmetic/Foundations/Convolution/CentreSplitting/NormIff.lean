module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.normIff :
    UpperTheory.ConvolutionTheory.Dp.NormIff := by
  intro E _ _ _ n π
  constructor
  · intro h ψ hψ
    refine mem_centralCuspForms.2 fun s x => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact congrArg ψ.1 (Subsingleton.elim _ _)
    · have hc : ((n : ℝ) * Module.finrank ℚ E) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.2 hn.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
      have hs : (⟨Real.exp (n * Module.finrank ℚ E * (Real.log s.1 / (n * Module.finrank ℚ E))), Real.exp_pos _⟩ :
          {r : ℝ // 0 < r}) = s := Subtype.ext (by
        change Real.exp _ = s.1
        rw [mul_div_cancel₀ _ hc, Real.exp_log s.2])
      have e := UpperTheory.V.KernelIndexFullLattice.splitEq_holds E n (Real.log s.1 / (n * Module.finrank ℚ E))
      rw [hs] at e
      have key := h (Cm.ofCusp E n ψ) hψ (Real.log s.1 / (n * Module.finrank ℚ E)) x
      rw [e] at key
      exact key
  · intro h φ hφ t g
    have hφ' : φ ∈ (Cm.carrier π).map (Cm.ofCusp E n) := by
      rw [Cm.map_carrier]; exact hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ'
    rw [UpperTheory.V.KernelIndexFullLattice.splitEq_holds E n t]
    exact h hψ _ g
