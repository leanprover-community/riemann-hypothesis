module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ClosedSubgroupsStatement
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSFA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TransposeUnitary

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS.Mult1

theorem haarUniq2 : HaarUniq2Statement := by
  intro k r U μ ν hU hμ hν
  haveI : Fact (Formalism.FourierDecayAlt.B2.IsClosedSubgroup U) := ⟨hU⟩
  obtain ⟨hμs, hμ0, hμc, hμl⟩ := hμ
  obtain ⟨hνs, hν0, hνc, hνl⟩ := hν
  have hμc' : μ (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hμc
  have hνc' : ν (HaarSigmaFiniteUniqueness.Aset U)ᶜ = 0 := hνc
  haveI := hμs
  haveI := hνs
  haveI := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ
  haveI := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) ν
  haveI := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap μ hμc' hμl
  haveI := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap ν hνc' hνl
  have hμ0' : μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r) ≠ 0 := by
    intro h
    apply hμ0
    rw [← HaarSigmaFiniteUniqueness.map_comap_val μ hμc', h, Measure.map_zero]
  have hν0' : ν.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r) ≠ 0 := by
    intro h
    apply hν0
    rw [← HaarSigmaFiniteUniqueness.map_comap_val ν hνc', h, Measure.map_zero]
  obtain ⟨c, hc, hcE⟩ := HaarSigmaFiniteUniqueness.eq_smul_of_sigmaFinite _ _ hν0' hμ0'
  refine ⟨c, pos_iff_ne_zero.mpr hc, ?_⟩
  have hval : AEMeasurable (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r)
      (μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Formalism.QuantumDeterminants.Mt k r)) :=
    (HaarSigmaFiniteUniqueness.mEmb (U := U)).measurable.aemeasurable
  rw [← HaarSigmaFiniteUniqueness.map_comap_val ν hνc', hcE, Measure.map_smul _ hval,
    HaarSigmaFiniteUniqueness.map_comap_val μ hμc']

end ReciprocityTheory.ChartRestriction.DS.Lap
