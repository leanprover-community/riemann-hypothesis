module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

namespace SemiampleNefAlt

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem charOf_prime {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} [W.IsPrime]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.charOf W ≠ 0) : (ReciprocityTheory.ChartRestriction.G.Geo.charOf W).Prime := by
  have hI : (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)).IsPrime := Ideal.comap_isPrime _ _
  have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) ≠ 0 := by
    intro h0
    apply h
    unfold ReciprocityTheory.ChartRestriction.G.Geo.charOf
    rw [h0]
    rfl
  rw [← Submodule.IsPrincipal.span_singleton_generator
    (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι))] at hI
  exact Int.prime_iff_natAbs_prime.mp ((Ideal.span_singleton_prime hg).mp hI)


end SemiampleNefAlt


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
