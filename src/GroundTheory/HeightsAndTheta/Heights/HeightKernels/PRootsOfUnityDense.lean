module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrass
public import Mathlib.Algebra.MvPolynomial.Funext
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RootsOfUnityDenseAlt

open Complex

theorem rootsOfUnity_infinite :
    {z : ℂ | ∃ k : ℕ, 0 < k ∧ z ^ k = 1}.Infinite := by
  have hprim : ∀ m : ℕ,
      IsPrimitiveRoot (exp (2 * Real.pi * I / ((m + 1 : ℕ) : ℂ))) (m + 1) :=
    fun m => Complex.isPrimitiveRoot_exp (m + 1) (Nat.succ_ne_zero m)
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => exp (2 * Real.pi * I / ((m + 1 : ℕ) : ℂ))) ?_ ?_
  · intro a b hab
    have ha := hprim a
    have hb := hprim b
    simp only at hab
    rw [hab] at ha
    have := IsPrimitiveRoot.unique ha hb
    omega
  · intro m
    exact ⟨m + 1, Nat.succ_pos m, (hprim m).pow_eq_one⟩

end RootsOfUnityDenseAlt

theorem RootsOfUnityDense.proof : RootsOfUnityDense.Statement := by
  intro n P hP
  refine MvPolynomial.funext_set (p := P) (q := 0)
    (fun _ => {z : ℂ | ∃ k : ℕ, 0 < k ∧ z ^ k = 1})
    (fun _ => RootsOfUnityDenseAlt.rootsOfUnity_infinite) ?_
  intro x hx
  rw [map_zero]
  exact hP x fun i => hx i (Set.mem_univ i)

end GroundTheory.Heights₂.Heights
