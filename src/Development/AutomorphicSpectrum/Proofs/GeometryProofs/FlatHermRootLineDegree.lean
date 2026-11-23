module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.RootOfRealisationTelescoping
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

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_rootFlat_of_realis : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (S : GlobalTheory.CompanionTheory.Ar.PB.AnSys (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) (Option (Ψ × Fin N))) (Re : GlobalTheory.CompanionTheory.Ar.PB.Realis S M.P) (τ : Ψ) (i₀ : Fin N) (F : Type) [Field F] [NumberField F] (φ : F →+* M.Ω) (A : HermLine M.ι) (Sf : FlatHerm M.y φ A), OverInt M.y φ → IsSmoothHerm A → (i₀ : ℕ) + 1 = N → 0 < S.t₀ → A.a = ∑ i, M.xdeg (τ, i) → (∀ (σ : Ψ) (i : Fin N), M.xdeg (σ, i) + (Re.ref (some (σ, i))).a = if h : 0 < (i : ℕ) then (Re.ref (some (σ, ⟨i - 1, by omega⟩))).a else 0) → (∀ t, 0 < t → t ≤ S.t₀ → ∀ (σ : Ψ) (i : Fin N), ∀ z ∈ mcPts M.P, (M.x t (σ, i)).h z * (Re.line (some (σ, i)) t).h z = if h : 0 < (i : ℕ) then (Re.line (some (σ, ⟨i - 1, by omega⟩)) t).h z else 1) → (∀ x, Re.π x ∈ S.open' → -Real.log (A.h (Re.R.lift x x)) = Real.log ((Re.ref (some (τ, i₀))).h (Re.R.lift x x)) + S.ph (some (τ, i₀)) (Re.π x)) → ∃ R : RootFlat M τ, R.ht = Sf.ht :=
  PositivityTheory.Xgn.root_of_realisation_telescoping

end GlobalTheory.CompanionTheory.Ar.Flat
