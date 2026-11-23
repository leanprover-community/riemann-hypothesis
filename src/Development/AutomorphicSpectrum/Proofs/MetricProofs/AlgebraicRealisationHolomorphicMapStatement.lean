module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicRealisationHolomorphicMap
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.algebraic_realisation_holomorphic_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (P J : Ideal (MRing ι)) (D : ℕ) (σ : Type) (S : AnSys D σ) (Re : Realis S (imageZ v₁ P)) (R : AnLogRes P J D), IsBlockMap κ₁ v₁ → IsArithVar P (D + 1) → AlgOver Re → ∃ (π : R.X → S.X) (hπ : HoloMap R.A S.A π), (∀ (x : R.X) (x₁ : Re.R.X), SameOrbit (Re.R.lift x₁ x₁) (fun p => R.lift x x (v₁ p)) → π x = Re.π x₁) ∧ (∀ a (ref' : HermLine ι), IsPullHerm κ₁ v₁ (Re.ref a) ref' → SamePot R.A Set.univ (potOf R ref') ((S.th a).pullback π hπ.1)) ∧ (∀ a t, 0 < t → t ≤ S.t₀ → ∀ x, Real.log ((Re.line a t).h fun p => R.lift x x (v₁ p)) = Real.log ((Re.ref a).h fun p => R.lift x x (v₁ p)) + S.phT a t (π x)) ∧ ∃ (β : MRing ι) (b : K → ℕ), IsMultiHomog β b ∧ β ∉ P ∧ ∀ x, π x ∈ bdry S.s → evC (R.lift x x) β = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pull.realis_pullback | exact GlobalTheory.CompanionTheory.Ar.Pull.realis_pullback | (intros; apply GlobalTheory.CompanionTheory.Ar.Pull.realis_pullback <;> assumption)
