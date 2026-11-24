module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValSpMapComp
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.flatComp_of :
    UpperTheory.Gal.W2.FlatComp := by
  intro V _ _ Y Y' f s v₀ w h U a hU
  have hU' : ⊤ ≤ s v₀ ⁻¹ᵁ (f ⁻¹ᵁ U) := hU
  have e : (fun v => valAt' (s v ≫ f) U a) =
      fun v => valAt' (s v) (f ⁻¹ᵁ U) ((f.appLE U (f ⁻¹ᵁ U) le_rfl).hom a) :=
    funext fun v => GlobalTheory.ExpCoord.valAt'_comp (s v) f U a
  rw [e]
  exact h _ _ hU'
