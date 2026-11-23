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
import Mathlib.Tactic.Basify
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

theorem UpperTheory.Gal.W2.piLattice_of :
    UpperTheory.Gal.W2.PiLattice := by
  intro g k Λ hd hs
  constructor
  · let φ : ↥(AddSubgroup.pi Set.univ fun _ : Fin k => Λ) → (Fin k → ↥Λ) :=
      fun x i => ⟨x.1 i, (AddSubgroup.mem_pi _).mp x.2 i trivial⟩
    refine DiscreteTopology.of_continuous_injective (f := φ) ?_ ?_
    · refine continuous_pi fun i => ?_
      exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
    · intro x y hxy
      apply Subtype.ext
      funext i
      have := congrArg (fun z => (z i : Fin g → ℂ)) hxy
      simpa [φ] using this
  · rw [eq_top_iff]
    intro w _
    rw [← Finset.univ_sum_single w]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hw : w i ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hs]; trivial
    have hmap : (Submodule.span ℝ (Λ : Set (Fin g → ℂ))).map
        (LinearMap.single ℝ (fun _ : Fin k => Fin g → ℂ) i) ≤
        Submodule.span ℝ ↑(AddSubgroup.pi Set.univ fun _ : Fin k => Λ) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨v, hv, rfl⟩
      simp only [SetLike.mem_coe, AddSubgroup.mem_pi]
      intro j _
      by_cases hj : j = i
      · subst hj; simpa using hv
      · simp [hj]
    exact hmap ⟨w i, hw, rfl⟩
