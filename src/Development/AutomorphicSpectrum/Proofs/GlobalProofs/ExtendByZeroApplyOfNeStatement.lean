module

public import Formalism.FormalDegreeBessel.StatementG
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExtendByZeroApplyOfNe
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

open Matrix

theorem _root_.GlobalTheory.T.unitary_element_prescribed_blocks : ∀ {n m : ℕ} (ε : Fin n → Bool) (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m)),
    xᴴ * Formalism.REAL.Jm ε * x = 0 → xᴴ * Formalism.REAL.Jm ε * y = 1 →
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * Formalism.REAL.Jm ε ∈ Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε) ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => y j i)),
        Formalism.REAL.Jm ε *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => y j i)) := by
  first | exact @GlobalTheory.CompanionTheory.EichlerTransf.eichler_transformation | exact GlobalTheory.CompanionTheory.EichlerTransf.eichler_transformation | (intros; apply GlobalTheory.CompanionTheory.EichlerTransf.eichler_transformation <;> assumption)
