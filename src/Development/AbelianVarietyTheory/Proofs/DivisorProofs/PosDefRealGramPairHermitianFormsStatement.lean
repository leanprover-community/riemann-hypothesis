module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefRealGramPairHermitianForms
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

open Matrix

theorem _root_.GlobalTheory.T.posDef_real_gram_pair_hermitian_forms : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re).PosDef ∧
    ((Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ)).PosDef := by
  first | exact @GlobalTheory.HermGram.gram_posDef_pair | exact GlobalTheory.HermGram.gram_posDef_pair | (intros; apply GlobalTheory.HermGram.gram_posDef_pair <;> assumption)
