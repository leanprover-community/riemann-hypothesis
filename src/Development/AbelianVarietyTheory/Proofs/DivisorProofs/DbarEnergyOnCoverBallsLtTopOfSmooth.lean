module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem n1_lt_infty_of_isSSec : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ), A.IsSSec (A.kap + la) F0 → n1 C la F0 < ⊤ := by
  intro n Y _ _ _ _ _ ι La _ A C la F0 hF
  unfold n1
  rw [ENNReal.sum_lt_top]
  intro a _
  set i := C.idx a
  set T := (A.chart i).target
  have hT : IsOpen T := (A.chart i).open_target
  have hsub : closedBall (C.c a) (C.r a) ⊆ T := C.sub a
  have hF' : ContDiffOn ℝ ∞ (F0 i ∘ (A.chart i).symm) T := hF.1 i
  have hD : ContinuousOn (fun v => fderiv ℝ (F0 i ∘ (A.chart i).symm) v) T :=
    hF'.continuousOn_fderiv_of_isOpen hT (by simp)
  have hph : ContinuousOn (fun v => A.ph la i ((A.chart i).symm v)) T :=
    (A.smooth_ph la i).continuousOn
  have hcont : ContinuousOn (fun v => (∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
      Real.exp (-A.ph la i ((A.chart i).symm v))) (closedBall (C.c a) (C.r a)) := by
    refine ContinuousOn.mono ?_ hsub
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_finsetSum _ (fun j _ => ?_)
      refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
      unfold wdb
      refine ContinuousOn.div_const (ContinuousOn.add ?_ (ContinuousOn.mul continuousOn_const ?_)) _
      · exact hD.clm_apply continuousOn_const
      · exact hD.clm_apply continuousOn_const
    · exact (hph.neg).rexp
  have hint : IntegrableOn (fun v => (∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
      Real.exp (-A.ph la i ((A.chart i).symm v))) (closedBall (C.c a) (C.r a)) :=
    hcont.integrableOn_compact (isCompact_closedBall _ _)
  calc _ ≤ ∫⁻ v in closedBall (C.c a) (C.r a), ENNReal.ofReal
        ((∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
          Real.exp (-A.ph la i ((A.chart i).symm v))) :=
        lintegral_mono_set ball_subset_closedBall
    _ < ⊤ := hint.lintegral_lt_top

end GlobalTheory
