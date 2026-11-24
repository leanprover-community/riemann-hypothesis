module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRangeStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem cInfAt_sheet_iff : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (f : CxPts t τ → ℝ) (y : CxPts p σ), CInfAt f (sheet t τ y) ↔ CInfAt (fun z : CxPts p σ => f (sheet t τ z)) y := by
  intro k _ _ X p t τ σ f y
  have hE := (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1
  constructor
  · rintro ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, hE.continuous.continuousAt.eventually h₅⟩
  · rintro ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩
    refine ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, ?_⟩
    show ∀ᶠ w in 𝓝 (sheet t τ y), f w = F fun a => ev t τ W (g a) w
    rw [← hE.map_nhds_eq, eventually_map]
    exact h₅

end GlobalTheory.CompanionTheory.Ar.BaseZ
