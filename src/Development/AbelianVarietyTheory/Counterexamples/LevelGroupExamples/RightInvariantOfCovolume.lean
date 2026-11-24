module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Pointwise
namespace GlobalTheory.AutQuotCheck

section Alg
variable {G : Type} [Group G] (Γ : Subgroup G)

abbrev cls (g : G) : Quotient (QuotientGroup.rightRel Γ) := Quotient.mk _ g


open MeasureTheory in
open scoped Pointwise in
variable {G : Type} [Group G] (Γ : Subgroup G) in
theorem _root_.GlobalTheory.AutQuotCheck.cls_eq_iff (g g' : G) :
    _root_.GlobalTheory.AutQuotCheck.cls Γ g = _root_.GlobalTheory.AutQuotCheck.cls Γ g' ↔ ∃ γ ∈ Γ, g' = γ * g := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply]
  constructor
  · intro h
    exact ⟨g' * g⁻¹, h, by group⟩
  · rintro ⟨γ, hγ, rfl⟩
    simpa using hγ

open MeasureTheory in
open scoped Pointwise in
variable {G : Type} [Group G] (Γ : Subgroup G) in
theorem _root_.GlobalTheory.AutQuotCheck.cls_smul (γ : Γ) (x : G) :
    _root_.GlobalTheory.AutQuotCheck.cls Γ (γ • x) = _root_.GlobalTheory.AutQuotCheck.cls Γ x := by
  rw [_root_.GlobalTheory.AutQuotCheck.cls_eq_iff]
  refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, ?_⟩
  rw [Subgroup.smul_def, smul_eq_mul, inv_mul_cancel_left]

open MeasureTheory in
open scoped Pointwise in
variable {G : Type} [Group G] (Γ : Subgroup G) in
theorem _root_.GlobalTheory.AutQuotCheck.measurable_cls [MeasurableSpace G] :
    Measurable (_root_.GlobalTheory.AutQuotCheck.cls Γ) := fun _ hs => hs


open MeasureTheory in
open scoped Pointwise in
variable {G : Type} [Group G] (Γ : Subgroup G) in
theorem _root_.GlobalTheory.AutQuotCheck.map_restrict_eq [MeasurableSpace G] [Countable Γ]
    [MeasurableConstSMul Γ G] (μ : Measure G) [SMulInvariantMeasure Γ G μ] {F F' : Set G}
    (h : IsFundamentalDomain Γ F μ) (h' : IsFundamentalDomain Γ F' μ) :
    (μ.restrict F).map (_root_.GlobalTheory.AutQuotCheck.cls Γ) =
      (μ.restrict F').map (_root_.GlobalTheory.AutQuotCheck.cls Γ) := by
  ext s hs
  have hA := _root_.GlobalTheory.AutQuotCheck.measurable_cls Γ hs
  rw [Measure.map_apply (_root_.GlobalTheory.AutQuotCheck.measurable_cls Γ) hs,
    Measure.map_apply (_root_.GlobalTheory.AutQuotCheck.measurable_cls Γ) hs,
    Measure.restrict_apply hA, Measure.restrict_apply hA]
  refine h.measure_set_eq h' hA fun γ => ?_
  ext x
  simp only [Set.mem_preimage, _root_.GlobalTheory.AutQuotCheck.cls_smul]

end Alg

section Top
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [Countable Γ]


open MeasureTheory in
open scoped Pointwise in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [Countable Γ] in
theorem _root_.GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (μ : Measure G) [μ.IsHaarMeasure] {F : Set G}
    (h : IsFundamentalDomain Γ F μ) (h0 : μ F ≠ 0) (h1 : μ F ≠ ⊤) (g : G) :
    μ.map (· * g) = μ := by
  haveI := Measure.isHaarMeasure_map_mul_right μ g
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
  have hF' : IsFundamentalDomain Γ ((· * g) ⁻¹' F) μ :=
    h.preimage_of_equiv (quasiMeasurePreserving_mul_right μ g) Function.bijective_id
      fun γ x => by simp [Subgroup.smul_def, mul_assoc]
  have hmeas : μ.map (· * g) F = μ F := by
    rw [show (· * g) = (MeasurableEquiv.mulRight g : G → G) from rfl,
      MeasurableEquiv.map_apply]
    exact hF'.measure_eq h
  have hc1 : (μ.map (· * g)).haarScalarFactor μ = 1 := by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hmeas
    exact ENNReal.coe_eq_one.mp ((ENNReal.mul_eq_right h0 h1).mp hmeas)
  rw [hc, hc1, one_smul]

end Top
end GlobalTheory.AutQuotCheck
