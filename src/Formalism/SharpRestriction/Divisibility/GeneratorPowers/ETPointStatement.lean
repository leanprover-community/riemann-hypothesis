module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

def ETSpanStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite ℤ Y] (R' : ℕ), 2 ≤ R' → ∀ (r : ℕ) (y z : Fin r → Y),
    (∀ a : Y, ∃ u ∈ Submodule.span (𝓞 E) (Set.range y), ∃ t : Y, a = u + R' • t) →
    ∀ a : Y, ∃ n : ℕ, 0 < n ∧
      n • a ∈ Submodule.span (𝓞 E) (Set.range fun b => y b + R' • z b)

end Formalism.MainNotions.ModuliIntegralCharts.H1
