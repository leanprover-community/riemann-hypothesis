module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
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
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ZDens

theorem chernDens_sheet : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (c : AlgChart p σ D) (c' : AlgChart t τ D), (∀ y ∈ c.e.source, sheet t τ y ∈ c'.e.source ∧ c'.e (sheet t τ y) = c.e y) → ∀ y ∈ c.e.source, c'.chernDens ψ (sheet t τ y) = c.chernDens (φ σ) y := by
  intro k _ _ _ _ X p t τ σ D B φ ψ hW hφ hψ c c' hm y hy
  obtain ⟨hy', he⟩ := hm y hy
  have hi := GlobalTheory.CxPts.mem_pick (φ σ).isLB y
  set i := GlobalTheory.CxPts.pick (φ σ).isLB y
  have hi' : sheet t τ y ∈ ptsIn t τ (B.U i) := hi
  rw [c'.chernDens_eq hψ hy' hi', c.chernDens_eq (hφ σ) hy hi, AlgChart.hess, AlgChart.hess, he]
  have ho := GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hmem := GlobalTheory.ChartGlue.mem_over c.e hy hi
  have e : (fun v => ((ψ.φ i (c'.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => (((φ σ).φ i (c.e.symm v) : ℝ) : ℂ) := by
    filter_upwards [ho.mem_nhds hmem] with v hv
    have hw := c.e.map_target hv.1
    obtain ⟨h₁, h₂⟩ := hm _ hw
    have hs : c'.e.symm v = sheet t τ (c.e.symm v) := by
      rw [← c'.e.left_inv h₁, h₂, c.e.right_inv hv.1]
    rw [hs, hW σ i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]

end GlobalTheory.CompanionTheory.Ar.ZDens
