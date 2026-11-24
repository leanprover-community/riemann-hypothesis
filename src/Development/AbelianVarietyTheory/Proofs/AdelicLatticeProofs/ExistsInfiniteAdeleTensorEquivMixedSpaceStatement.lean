module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInfiniteAdeleTensorEquivMixedSpace
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

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_infiniteAdele_tensor_equiv_mixedSpace :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 →
      (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
      ∃ θ : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E,
        (∀ x : E, θ (1 ⊗ₜ[F] x) = mixedEmbedding E x) ∧
        @Continuous _ _ inferInstance
          (moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)) θ.symm ∧
        ∀ u : (mixedSpace E)ˣ, (∀ w, ((u : mixedSpace E).2 w).im = 0) →
          ∃ a : (InfiniteAdeleRing F)ˣ, θ ((a : InfiniteAdeleRing F) ⊗ₜ[F] 1) = u := by
  exact GlobalTheory.InfAdeleMixed.exists_equiv_mixedSpace
