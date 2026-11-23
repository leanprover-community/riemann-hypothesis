module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ExistsKhwGenSubOfKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv

@[expose] public section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.PsCo.PcEF

theorem eq_discreteSeries_of_lowestKType_casimir : DatumEquiv := by
  intro n ε lam hgap H _ _ _ σ hσ hirr V hV hV0 hc X _ _ D hD
  haveI : CompleteSpace X := hD.1
  have hσD : IsURepOn (UJset ε) D := hD.2.2.1
  have hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v :=
    kStable_of_isKStableSub hσ (isDerivedOn_smE hσ) V hV.1 hV.2.1
  obtain ⟨V', hV', hV0', hVK', hc'⟩ := arb_datum hD (casOnSmooth_of_isDS hD hgap)
  have htop := data_closGen_eq_top hgap hσ (isDerivedOn_smE hσ) hV hc hVK hirr hV0
  have htop' := data_closGen_eq_top hgap hσD (isDerivedOn_smE hσD) hV' hc' hVK' hD.2.2.2.1 hV0'
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap hσ (isDerivedOn_smE hσ) hV hc hVK hV0
    hσD (isDerivedOn_smE hσD) hV' hc' hVK' hV0'
  refine ⟨((LinearIsometryEquiv.ofTop _ _ htop).symm.trans U).trans (LinearIsometryEquiv.ofTop _ _ htop'),
    fun g hg x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.ofTop_apply]
  apply hU g hg
  simp only [LinearIsometryEquiv.ofTop_symm_apply_coe]

end GlobalTheory.PsCo.PcEF
