module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarHaarA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarInv
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarRight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem muPolar_isHaar (ε : Fin n → Bool) : (muPolar ε).IsHaarMeasure := by
  haveI hR : (muPolar ε).IsMulRightInvariant := ⟨fun g => muPolar_mul_right ε g⟩
  have hinv : (muPolar ε).inv = muPolar ε := muPolar_inv ε
  haveI hL : (muPolar ε).IsMulLeftInvariant := by
    rw [← hinv]; infer_instance

  have hsurj : Function.Surjective (fdphPhi ε) := by
    intro g
    have hg : toM g ∈ UJset ε := g.2
    refine ⟨polarInv ε ⟨toM g, hg⟩, ?_⟩
    have h := fdph_toM_phi ε (polarInv ε ⟨toM g, hg⟩)
    rw [polarM_polarInv] at h
    exact Subtype.ext (Units.ext h)
  haveI hF : IsFiniteMeasureOnCompacts (muPolar ε) := by
    refine ⟨fun K hK => ?_⟩
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    rw [fdph_apply ε hKm, ← fdph_preimage]
    exact ((polarM_isClosedEmbedding ε).isCompact_preimage
      (hK.image (by fun_prop))).measure_lt_top
  haveI hO : (muPolar ε).IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [fdph_apply ε hU.measurableSet]
    exact ((hU.preimage (fdph_phi_continuous ε)).measure_ne_zero _
      (hne.preimage hsurj))
  exact {}

end ReciprocityTheory.ChartRestriction.DS
