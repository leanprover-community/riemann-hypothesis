module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobsonIdealFaithfulModule
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

theorem _root_.GlobalTheory.T.jacobson_ideal_faithful_module : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)] (I : Ideal Γ(X, V)) {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R] {M : Type} [AddCommGroup M] [Module R M] [Module Γ(X, V) M] [IsScalarTower Γ(X, V) R M] [Module.Finite R M], I.map (algebraMap Γ(X, V) R) ≤ Ideal.jacobson ⊥ → (∀ a ∈ J.ideal ⟨V, hV⟩, ∀ m : M, a • m = 0) → ∀ f : Γ(X, V), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ y : M, (∀ n, ChartIn (ψ ≫ J.subschemeι) V (I ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) y) → ∃ k : ℕ, f ^ k • y = 0 := by
  exact @GlobalTheory.CompanionTheory.GE.Krull.fPow_torsion_of_chartIn
