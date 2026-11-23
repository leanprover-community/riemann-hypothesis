module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open TensorProduct CategoryTheory AlgebraicGeometry

universe u

namespace GlobalTheory.GaloisDescent

section Instances

variable (K L G V : Type*) [CommSemiring K] [Semiring L] [Algebra K L] [Monoid G]
  [MulSemiringAction G L]

end Instances

section Group

variable {K L G : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]

end Group

section AlgEquiv

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable [Algebra K ℂ]

theorem complex_stable_iff_exists_baseChange {V : Type*} [AddCommGroup V]
    [Module K V] (W : Submodule ℂ (ℂ ⊗[K] V)) :
    (∀ σ : ℂ ≃ₐ[K] ℂ, ∀ w ∈ W, σ.toLinearMap.rTensor V w ∈ W) ↔
      ∃! N : Submodule K V, N.baseChange ℂ = W :=
  stable_iff_exists_baseChange (fun σ : ℂ ≃ₐ[K] ℂ => σ.toAlgHom)
    complex_mem_range_of_forall_algEquiv W

end AlgEquiv

end GlobalTheory.GaloisDescent
