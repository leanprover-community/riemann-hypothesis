module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem IntNumVanish.proof (h1 : HilbDegBound.Statement.{u})
    (h2 : HilbFnVanishBlock.Statement.{u}) (h3 : DegLTClosure.Statement)
    (h4 : EventualValueFacts.Statement) : IntNumVanish.Statement.{u} := by
  intro F _ K _ _ ι _ n Q hQ hQh hcase bs

  suffices hdeg : DegLT (hilbFn Q) n by
    exact (h4 K (mixedDiff bs (hilbFn Q)) 0 0).1 (hdeg bs)
  rcases hcase with hirr | hdim
  ·
    have hblock : ∃ k, ∀ i : ι k, (X ⟨k, i⟩ : MRing ι F) ∈ Q := by
      by_contra hne
      exact hirr fun k => by_contra fun h => hne ⟨k, fun i => by_contra fun hi => h ⟨i, hi⟩⟩
    obtain ⟨k, hk⟩ := hblock
    have hzero : (0 : (K → ℤ) → ℤ) =ᶠ[Filter.atTop] hilbFn Q := by
      filter_upwards [Filter.eventually_ge_atTop (fun _ : K => (1 : ℤ))] with m hm
      exact (h2 F K ι Q k hk m (hm k)).symm
    exact (h3 K n 0 (hilbFn Q) 0 0).2.2.2.2 hzero (degLT_zero n)
  · exact h1 F K ι n Q hQ hQh hdim

end

end GroundTheory.Heights₂.Heights.NumbersDVR
