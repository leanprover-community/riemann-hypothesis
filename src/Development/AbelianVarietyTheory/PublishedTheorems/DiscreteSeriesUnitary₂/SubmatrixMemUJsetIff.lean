module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
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

open Formalism.MainNotions.S Matrix

namespace GlobalTheory.FormalDegree

def HarishChandra : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧
    ∀ (π : Equiv.Perm (Fin n)) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
        IsDS (ε ∘ π) lam (fun g => σ (g.submatrix π.symm π.symm)) →
        IsFdeg (Formalism.REAL.muG ε) σ (c * Formalism.QuantumDeterminants.fdegHC lam)

theorem HarishChandra.chamber (h : HarishChandra) (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
        IsFdeg (Formalism.REAL.muG ε) σ (c * Formalism.QuantumDeterminants.fdegHC lam) := by
  obtain ⟨c, hc, h1⟩ := h n ε
  exact ⟨c, hc, fun lam hl H _ _ σ hσ => h1 1 lam hl H σ (by simpa [Equiv.Perm.one_def] using hσ)⟩

end GlobalTheory.FormalDegree
