module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoritaNonemptyEquivOfLocalQuotientMatrix
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


theorem _root_.GlobalTheory.T.morita_nonempty_equiv_of_local_quotient_matrix : ∀ (R : Type) [CommRing R] (I : Ideal R), IsLocalRing (R ⧸ I) → ∀ (m k : ℕ), 0 < m →
    ∀ (O : Type) [Ring O] [Algebra R O] (φ : O →ₐ[R] Matrix (Fin m) (Fin m) (R ⧸ I)), Function.Surjective φ →
    (∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) →
    ∀ (M N : Type) [AddCommGroup M] [Module O M] [Module R M] [IsScalarTower R O M]
      [AddCommGroup N] [Module O N] [Module R N] [IsScalarTower R O N],
    (M ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → (N ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → Nonempty (M ≃ₗ[O] N) := by
  first | (exact @GlobalTheory.MoritaLocal.morita_local) | (exact GlobalTheory.MoritaLocal.morita_local) | (intros; apply GlobalTheory.MoritaLocal.morita_local  <;> assumption)
