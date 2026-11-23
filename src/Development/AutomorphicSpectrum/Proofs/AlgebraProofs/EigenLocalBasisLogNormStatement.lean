module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenLocalBasisLogNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.eigen_local_basis_log_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes) (K : Type) [Field K] [CharZero K] (j : K →+* ℂ_[ℓ]) (V : Subring K) (U : Type) [AddCommGroup U] [Module K U] (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I J : Type) [Fintype I] [Fintype J] (u : I → U) (u' : J → U) (f : ℕ) (b : Fin f → 𝓞 E) (δ : K), (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ V) → Nat.card (E →+* K) = Module.finrank ℚ E → IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b → (∀ a, ρ H.rt (u a) = σ (H.rt : E) • u a) → (∀ a, ρ H.rt (u' a) = -σ (H.rt : E) • u' a) → LinearIndependent K (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1)) (fun q : J × Fin f => ρ (b q.2) (u' q.1))) → δ ≠ 0 → Real.log ‖j δ‖ = logIdeal ((j.comp σ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (σ (H.rt : E))‖ → LinearIndependent K (fun a => δ • HT.eigProj ρ σ (u a)) ∧ Submodule.span V (Set.range (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1)) (fun q : J × Fin f => ρ (b q.2) (u' q.1)))) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range fun a => δ • HT.eigProj ρ σ (u a)) := by
  exact @GlobalTheory.CompanionTheory.Ar.Fl.EigSubLat.eigSub_span
