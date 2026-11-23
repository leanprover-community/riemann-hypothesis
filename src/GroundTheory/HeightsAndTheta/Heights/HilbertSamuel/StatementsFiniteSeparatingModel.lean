module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.Prime
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

def FiniteSeparatingModel.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℚ)) (f : MvPolynomial σ ℚ) (x : σ → ℂ),
    P.IsPrime → f ∉ P → (∀ g ∈ P, aeval x g = 0) →
    ∃ (e : ℕ) (ℓ : Fin e → MvPolynomial σ ℚ) (u : MvPolynomial σ ℚ)
      (G : Polynomial (MvPolynomial (Fin e) ℚ)) (c D : MvPolynomial (Fin e) ℚ),
      G.Monic ∧ c ≠ 0 ∧ D ≠ 0 ∧
      (∀ i : σ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ), p.Monic ∧
        ∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
          p.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (z i) = 0) ∧
      (∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
        G.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (aeval z u) = 0) ∧
      (∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
        aeval (fun j => aeval z (ℓ j)) c ≠ 0 → aeval z f ≠ 0) ∧
      (∀ (y : Fin e → ℂ) (t : ℂ), aeval y D ≠ 0 → G.eval₂ (aeval y).toRingHom t = 0 →
        ∃ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) ∧ (fun j => aeval z (ℓ j)) = y ∧ aeval z u = t) ∧
      (∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
        (fun j => aeval z (ℓ j)) = (fun j => aeval x (ℓ j)) → aeval z u = aeval x u → z = x)

end GroundTheory.Heights₂.Heights.HilbertSamuel
