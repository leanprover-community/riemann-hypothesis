module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMultGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVanishNearPoint
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem SliceLength.proof (hV : IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.Statement)
    (hR : SliceReducedGeneral.Statement) (hM : SliceMultGeneral.Statement) :
    SliceLength.Statement := by
  intro n d J W u hJ hdim hu hW
  have hWp : W.IsPrime := hW.1.1
  obtain ⟨f₁, hf₁W, hf₁⟩ := hR n d J W u hJ hdim hu hW
  obtain ⟨f₂, hf₂W, hf₂⟩ := hM n d J W u hJ hdim hu hW
  have hf : f₁ * f₂ ∉ W := fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W
  have hUo : IsOpen {x : Fin n → ℂ | eval x (f₁ * f₂) ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval (p := f₁ * f₂)) continuous_const
  refine ⟨{x | eval x (f₁ * f₂) ≠ 0}, hUo, ?_, ?_⟩
  ·
    intro x hx
    rw [mem_closure_iff_nhds]
    intro t ht
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hf
    refine hV n W (f₁ * f₂) x hWp hx ?_
    filter_upwards [ht] with y hyt hyW
    by_contra hne
    have hy : y ∈ t ∩ (zeroSet W ∩ {x | eval x (f₁ * f₂) ≠ 0}) := ⟨hyt, hyW, hne⟩
    rw [hempty] at hy
    exact hy
  ·
    rintro q ⟨hqW, hqf⟩
    rw [Set.mem_ofPred_eq, map_mul, mul_ne_zero_iff] at hqf
    obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf₁ q hqW hqf.1
    obtain ⟨O₂, -, hO₂d, hO₂⟩ := hf₂ q hqW hqf.2
    exact (hO₁d.inter_of_isOpen_left hO₂d hO₁o).mono fun L (hL : L ∈ O₁ ∩ O₂) => ⟨hO₁ L hL.1, hO₂ L hL.2⟩

end GroundTheory.Heights₂.Heights
