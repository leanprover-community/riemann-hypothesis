module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompleteModuleNoetherianRealization
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalLimit
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

theorem _root_.GlobalTheory.T.complete_module_noetherian_realization : ∀ {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B) {N : Type} [AddCommGroup N] [Module B N] [Module.Finite B N] (T : ℕ → Submodule B N), (∀ n, I ^ (n + 1) • (⊤ : Submodule B N) ≤ T n) → (∀ n, T n = T (n + 1) ⊔ I ^ (n + 1) • (⊤ : Submodule B N)) → ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : Algebra B R) (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module B M) (_ : IsScalarTower B R M) (_ : Module.Finite R M) (μ : N →ₗ[B] M), I.map (algebraMap B R) ≤ Ideal.jacobson ⊥ ∧ Submodule.span R (Set.range μ) = ⊤ ∧ ∀ n e, e ∈ T n ↔ μ e ∈ (I ^ (n + 1) • ⊤ : Submodule B M) := by
  exact @GlobalTheory.CompanionTheory.GE.CompletionTower.exists_completion_tower
