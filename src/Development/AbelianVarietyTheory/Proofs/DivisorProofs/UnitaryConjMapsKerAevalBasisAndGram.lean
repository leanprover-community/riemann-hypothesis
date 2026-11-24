module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAlgApply
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

open Matrix Polynomial

namespace GlobalTheory

theorem unitary_conj_ker_basis_gram {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K)
    (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1)
    (Q : K[X]) {ι : Type} (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hspan : Submodule.span K (Set.range u) =
      LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))) :
    LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧
    Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
      LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧
    (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) *
        ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) = Matrix.of fun i j => ∑ k, σ (u i k) * u j k := by
  first
  | exact @_root_.GlobalTheory.ConjugateAlgebraLemmas.main
  | exact _root_.GlobalTheory.ConjugateAlgebraLemmas.main
  | (apply _root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateAlgebraLemmas.main ..)

end GlobalTheory
