module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
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

@[expose] public section

set_option autoImplicit false

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDivGroup

theorem mem_symCocycles_of_pullTwo_mulP {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ)
    (c : G.A n ⊗[R] G.A n) (h : pullbackTwo (G.mulP n) c ∈ symCocycles R (G.A (n + 1))) :
    c ∈ symCocycles R (G.A n) := by
  rw [mem_symCocycles] at h ⊢
  have h3 : Function.Injective
      (TensorProduct.map (G.mulP n : G.A n →ₗ[R] G.A (n + 1)) (pullbackTwo (G.mulP n))) :=
    TensorProduct.map_injective_of_flat_flat _ _ (Test.mulP_injective G n)
      (G.pullbackTwo_mulP_injective n)
  refine ⟨h3 ?_, G.pullbackTwo_mulP_injective n ?_⟩
  · rw [← cobTwo_pullTwo, h.1, map_zero]
  · rw [← h.2]
    exact TensorProduct.map_comm _ _ c

end PDivGroup

end GlobalTheory
