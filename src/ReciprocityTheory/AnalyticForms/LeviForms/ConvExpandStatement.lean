module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
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
public import ReciprocityTheory.AnalyticForms.LeviForms.MixedIntegralInclusionExclusion

@[expose] public section

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

def ConvDensStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ : LocPot X)
    (s : X → X → ℂ) (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ),
    IsClosed (bdry s) → IsPotential A Θ → (∀ i, IsPotential A (th i)) → (∀ i, A.SmoothOn (bdry s)ᶜ (ph i)) →
    (∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ i, A.Smooth (phT i t)) →
    (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) →
      ∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K →
        TendstoUniformlyOn (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
          (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j) (nhdsWithin 0 (Set.Ioi 0)) K

theorem conv_dens : ConvDensStatement := by
  intro e X _ A Θ s th ph phT hB hΘ hth hph hT hC2 j K hK hKc
  exact conv_dens_of_closed A Θ s th ph phT hB hΘ hth hph hT hC2 j K hK hKc

end

end ReciprocityTheory.AnForm.P
