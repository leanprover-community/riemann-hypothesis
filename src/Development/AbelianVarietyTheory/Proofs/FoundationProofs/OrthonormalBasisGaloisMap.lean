module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem aut_conj_comm (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (x : D.host.E) :
    σ (D.host.conj x) = D.host.conj (σ x) := by
  have h : σ * D.host.conj = D.host.conj * σ :=
    (D.host.gal).injective (by rw [map_mul, map_mul, mul_comm])
  exact congrArg (fun f : D.host.E ≃ₐ[ℚ] D.host.E => f x) h

theorem hYY_map_aut (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : ∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E))
    {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) : hYY D (x.map σ) (y.map σ) = hYY D x y := by
  let e : D.host.E ≃ₐ[D.host.K] D.host.E := { σ with commutes' := hσ }
  unfold hYY
  rw [← Algebra.trace_eq_of_algEquiv e (∑ i, ∑ j, x i j * D.host.conj (y i j))]
  congr 1
  show _ = σ _

  simp only [map_sum, map_mul, Matrix.map_apply, aut_conj_comm]

theorem onB_map_aut : ∀ (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E), (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) →
    ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → OnB D (fun j => (b j).map σ) := by
  intro D σ hσ N N' r b hb
  refine ⟨?_, ?_⟩
  · intro i j
    rw [hYY_map_aut D σ hσ]
    exact hb.1 i j
  · let e : D.host.E ≃ₐ[D.host.K] D.host.E := { σ with commutes' := hσ }
    let L : Matrix (Fin N') (Fin N) D.host.E ≃ₗ[D.host.K] Matrix (Fin N') (Fin N) D.host.E :=
      e.toLinearEquiv.mapMatrix
    have h : (fun j => (b j).map σ) = L.toLinearMap ∘ b := rfl
    rw [h, Set.range_comp, ← Submodule.map_span, hb.2, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.NormSum
