module

public import Formalism.HermitianCurvature.StatementD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Finset

noncomputable section

namespace GlobalTheory.WigSh

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

def WigMap (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {V₁ V₂ : Type} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (π₂ : Q.Mx k r → (V₂ →L[ℂ] V₂)) (π₁ : Q.Mx k r → (V₁ →L[ℂ] V₁))
    (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (V₂ →L[ℂ] V₁)) : Prop :=
  (∃ (t : ℕ) (q : Fin t → MvPolynomial (Fin (2 * r + k + 1) ⊕ Fin (2 * r + k + 1)) ℂ) (Lm : Fin t → (V₂ →L[ℂ] V₁)),
      (∀ i, (q i).totalDegree ≤ d) ∧
        ∀ ω, A ω = ∑ i, MvPolynomial.eval (Sum.elim ω (fun j => star (ω j))) (q i) • Lm i) ∧
    (∀ h ∈ UWset k r z, ∀ ω, (A (h *ᵥ ω)).comp (π₂ h) = (π₁ h).comp (A ω)) ∧
    (∀ (t : ℝ) (ω : Fin (2 * r + k + 1) → ℂ), A ((t : ℂ) • ω) = ((t : ℂ) ^ d) • A ω) ∧
    ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ‖A ω‖ ^ 2 ≤ (herm (Hpk k r) ω ω).re ^ d

def omg (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) : Fin (2 * r + k + 1) → ℂ :=
  D.prW k r z' ((Hpk k r * gᴴ * Hpk k r) *ᵥ
    ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a)

end GlobalTheory.WigSh
