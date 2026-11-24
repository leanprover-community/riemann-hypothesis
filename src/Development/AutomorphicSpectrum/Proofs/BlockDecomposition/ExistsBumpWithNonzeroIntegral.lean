module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.UrysohnsLemma

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.MeasureBump

theorem exists_integral_ne_zero_of_carried_by_isOpen
    (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) (U : Set X)
    (hU : IsOpen U) (hc : m Uᶜ = 0) (hm : m ≠ 0)
    (hint : ∀ χ : X → ℝ, Continuous χ → HasCompactSupport χ → tsupport χ ⊆ U → Integrable χ m) :
    ∃ χ : X → ℝ, Continuous χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∫ x, χ x ∂m ≠ 0 := by
  have hmU : m U ≠ 0 := by
    intro h0
    apply hm
    rw [← Measure.measure_univ_eq_zero]
    have huniv : (Set.univ : Set X) = U ∪ Uᶜ := (Set.union_compl_self U).symm
    rw [huniv]
    exact measure_union_null h0 hc
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨K, hK, hKU⟩ := hσ
  have hex : ∃ n, m (K n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hmU
    rw [← hKU]
    exact measure_iUnion_null hcon
  obtain ⟨n, hn⟩ := hex
  have hsub : K n ⊆ U := hKU ▸ Set.subset_iUnion K n
  obtain ⟨f, hf1, hfc, hfU, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen (hK n) hU hsub
  refine ⟨f, f.continuous, hfc, hfU, ?_⟩
  have hI : Integrable (f : X → ℝ) m := hint f f.continuous hfc hfU
  have hnn : 0 ≤ᵐ[m] (f : X → ℝ) := Filter.Eventually.of_forall fun x => (hf01 x).1
  have hpos : 0 < ∫ x, f x ∂m := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hI]
    refine lt_of_lt_of_le (pos_iff_ne_zero.2 hn) (measure_mono ?_)
    intro x hx
    simp [Function.mem_support, hf1 hx]
  exact hpos.ne'

end GlobalTheory.CompanionTheory.MeasureBump
