module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureBasis
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.hermitian_signature_basis : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : 𝓞 E →+* Module.End K W) (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* K) (p q : ℕ) (v : Fin p → W) (w : Fin q → W), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent K v → Submodule.span K (Set.range v) = HT.eigSp ρ σ → LinearIndependent K w → Submodule.span K (Set.range w) = HT.eigSp ρ σ' → ∃ u, IsAdapted ρH σ v w u ∧ LinearIndependent K u ∧ Submodule.span K (Set.range u) = HT.eigSp ρH σ := by
  exact @GlobalTheory.CompanionTheory.Ar.Flat.AdaptedEx.exists_adapted_basis
