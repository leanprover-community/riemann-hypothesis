module

public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithmeticDegreePositiveHerm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.section_count_tendsto_geomDeg : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι), 1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A → (∀ W, IsArithVar W 2 → mCoordIdeal y ≤ W → 0 ≤ geomDeg W A 1) → (∀ τ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω))) ∧ Tendsto (fun τ : ℕ => (D.factorial : ℝ) * (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y A.a τ : Set Ω)) : ℝ) / (τ : ℝ) ^ D) atTop (𝓝 (geomDeg (mCoordIdeal y) A D)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.nefCount | exact GlobalTheory.CompanionTheory.Ar.Plug.nefCount | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.nefCount <;> assumption)
