module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_sub : ∀ (O : Type) [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L] (f : L →ₗ[O] TwMod s L) (I : Ideal O), I.map (s : O →+* O) ≤ I → ∀ x ∈ I • (⊤ : Submodule O L), (show L from f x) ∈ I • (⊤ : Submodule O L) := by
  intro O _ s L _ _ f I hI x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    have hsa : s a ∈ I := hI (Ideal.mem_map_of_mem (s : O →+* O) ha)
    have key : (show L from f (a • y)) = s a • (show L from f y) := f.map_smul a y
    rw [key]
    exact Submodule.smul_mem_smul hsa Submodule.mem_top
  · intro y z hy hz
    have key : (show L from f (y + z)) = (show L from f y) + (show L from f z) := f.map_add y z
    rw [key]
    exact Submodule.add_mem _ hy hz

end PositivityTheory.UnitarySelfGeneration
