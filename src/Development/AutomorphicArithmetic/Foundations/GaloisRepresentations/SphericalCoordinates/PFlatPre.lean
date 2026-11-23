module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.flatPre_of :
    UpperTheory.Gal.W2.FlatPre := by
  intro V _ _ V' _ _ Y B s hs φ φ' v₀ w hφ hB
  have key : ∀ (U : Y.Opens) (f : Γ(Y, U)), ⊤ ≤ s (φ v₀) ⁻¹ᵁ U →
      fderiv ℂ (fun v => valAt' (s (φ v)) U f) v₀ w =
        fderiv ℂ (fun b => valAt' (s b) U f) (φ v₀) (φ' w) := by
    intro U f hU
    obtain ⟨hopen, hdiff⟩ := hs U f
    have hmem : φ v₀ ∈ {b ∈ B | ⊤ ≤ s b ⁻¹ᵁ U} := ⟨hB, hU⟩
    have hd : DifferentiableAt ℂ (fun b => valAt' (s b) U f) (φ v₀) :=
      (hdiff _ hmem).differentiableAt (hopen.mem_nhds hmem)
    have hc := hd.hasFDerivAt.comp v₀ hφ
    have he : fderiv ℂ (fun v => valAt' (s (φ v)) U f) v₀ = _ := hc.fderiv
    rw [he]
    rfl
  constructor
  · intro h U f hU
    rw [← key U f hU]
    exact h U f hU
  · intro h U f hU
    rw [key U f hU]
    exact h U f hU
