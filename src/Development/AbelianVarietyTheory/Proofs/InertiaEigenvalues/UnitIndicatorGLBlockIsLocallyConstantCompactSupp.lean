module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.UnitTest

theorem isLocallyConstant_indicator_one {Z : Type} [TopologicalSpace Z] {W : Set Z} (hW : IsClopen W) :
    IsLocallyConstant (W.indicator (1 : Z → ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ W
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem unitG_isTest (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (r : ℕ) : IsTest (unitG r F) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  set B : Set F := Metric.closedBall 0 1 with hB
  have hBo : IsOpen B := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsClosed B := Metric.isClosed_closedBall
  have hBk : IsCompact B := isCompact_closedBall 0 1
  set A : Set (Matrix (Fin r) (Fin r) F) := Set.univ.pi fun _ => Set.univ.pi fun _ => B with hA
  set V : Set (Fin r → F) := Set.univ.pi fun _ => B with hV
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hBo
  have hVc : IsClosed V := isClosed_set_pi fun _ _ => hBc
  have hVk : IsCompact V := isCompact_univ_pi fun _ => hBk
  have hAo : IsOpen A := isOpen_set_pi Set.finite_univ fun _ _ => hVo
  have hAc : IsClosed A := isClosed_set_pi fun _ _ => hVc
  have hAk : IsCompact A := isCompact_univ_pi (X := fun _ : Fin r => Fin r → F) fun _ => hVk
  set S : Set (Gl r F) := A ×ˢ (V ×ˢ (V ×ˢ B)) with hS
  have hSeq : {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
      = S := by
    ext Y
    rw [Set.mem_setOf_eq, hS, hA, hV, hB]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun i _ j _ => ?_, fun i _ => ?_, fun i _ => ?_, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h1 i j
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h2 i
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h3 i
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h4
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun i j => ?_, fun i => ?_, fun i => ?_, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h1 i trivial j trivial
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h2 i trivial
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h3 i trivial
      · simpa only [Metric.mem_closedBall, dist_zero_right] using h4
  have hSo : IsOpen S := hAo.prod (hVo.prod (hVo.prod hBo))
  have hSc : IsClosed S := hAc.prod (hVc.prod (hVc.prod hBc))
  have hSk : IsCompact S := hAk.prod (hVk.prod (hVk.prod hBk))
  unfold unitG
  rw [hSeq]
  exact ⟨isLocallyConstant_indicator_one ⟨hSc, hSo⟩,
    HasCompactSupport.intro' hSk hSc fun x hx => Set.indicator_of_notMem hx _⟩

end GlobalTheory.JR.UnitTest
