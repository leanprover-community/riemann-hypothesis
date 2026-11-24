module

public import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import GroundTheory.GlobalFields.Adele.Approximation
import GroundTheory.GlobalFields.Adele.Topology
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal

namespace GroundTheory.Global

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem countable_quotient_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] {W : Subgroup G}
    (hW : IsOpen (W : Set G)) : Countable (G ⧸ W) := by
  have : DiscreteTopology (G ⧸ W) := QuotientGroup.discreteTopology hW
  have h : IsLindelof (Set.univ : Set (G ⧸ W)) := by
    rw [← Set.image_univ_of_surjective (QuotientGroup.mk_surjective (s := W))]
    exact isLindelof_univ.image QuotientGroup.continuous_mk
  exact Set.countable_univ_iff.1 h.countable_of_discrete

variable {K}

theorem hasSum_integral_ideleMeasure_of_invariant {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (W : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ)
    (hWo : IsOpen (W : Set (FiniteAdeleRing (𝓞 K) K)ˣ)) {F : IdeleGroup K → E} (hFi : Integrable F (ideleMeasure K))
    (hF : ∀ x : IdeleGroup K, ∀ w ∈ W, F (x * (IdeleGroup.prodEquiv K).symm (1, w)) = F x) :
    HasSum (fun c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W ↦ (finiteIdeleMeasure K W).toReal •
        ∫ a, F ((IdeleGroup.prodEquiv K).symm (a, c.out)) ∂infiniteIdeleMeasure K)
      (∫ x, F x ∂ideleMeasure K) := by
  have hc : Countable ((FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W) := countable_quotient_of_isOpen hWo
  set μ := (infiniteIdeleMeasure K).prod (finiteIdeleMeasure K)
  set G : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ → E :=
    fun p ↦ F ((IdeleGroup.prodEquiv K).symm p)
  have hG : Integrable G μ :=
    (integrable_map_equiv (IdeleGroup.prodEquiv K).symm.toHomeomorph.toMeasurableEquiv F).1 hFi

  set S : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W → Set (FiniteAdeleRing (𝓞 K) K)ˣ :=
    fun c ↦ QuotientGroup.mk ⁻¹' {c}
  have : DiscreteTopology ((FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W) := QuotientGroup.discreteTopology hWo
  have hSm : ∀ c, MeasurableSet (S c) := fun c ↦
    (isOpen_discrete ({c} : Set ((FiniteAdeleRing (𝓞 K) K)ˣ ⧸ W))).preimage
      QuotientGroup.continuous_mk |>.measurableSet
  have hSW : ∀ c, S c = (fun b ↦ c.out⁻¹ * b) ⁻¹' (W : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
    intro c
    ext b
    simp only [S, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rw [eq_comm, QuotientGroup.eq]
  have hmeasS : ∀ c, finiteIdeleMeasure K (S c) = finiteIdeleMeasure K W := fun c ↦ by
    rw [hSW c, measure_preimage_mul]
  have hGS : ∀ c, ∀ a, ∀ b ∈ S c, G (a, b) = G (a, c.out) := by
    intro c a b hb
    rw [hSW c] at hb
    have hw : c.out⁻¹ * b ∈ W := hb
    have : (a, b) = (a, c.out) * (1, c.out⁻¹ * b) := by simp
    simp only [G]
    rw [this, map_mul, hF _ _ hw]
  have hT : ∀ c, MeasurableSet ((Set.univ : Set (InfiniteAdeleRing K)ˣ) ×ˢ S c) := fun c ↦
    MeasurableSet.univ.prod (hSm c)
  have hTd : Pairwise (Function.onFun Disjoint
      fun c ↦ (Set.univ : Set (InfiniteAdeleRing K)ˣ) ×ˢ S c) := by
    intro c d hcd
    refine Set.disjoint_left.2 fun p hp hq ↦ hcd ?_
    exact hp.2.symm.trans hq.2
  have hTu : ⋃ c, (Set.univ : Set (InfiniteAdeleRing K)ˣ) ×ˢ S c = Set.univ := by
    refine Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.2 ⟨(p.2 : _ ⧸ W), trivial, rfl⟩
  have h := hasSum_integral_iUnion hT hTd hG.integrableOn
  rw [hTu, Measure.restrict_univ] at h
  rw [integral_ideleMeasure]
  convert h using 1
  funext c
  symm
  have e : μ.restrict (Set.univ ×ˢ S c) =
      (infiniteIdeleMeasure K).prod ((finiteIdeleMeasure K).restrict (S c)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [e, integral_prod _ (by rw [← e]; exact hG.integrableOn), ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a ↦ ?_)
  simp only
  rw [setIntegral_congr_fun (hSm c) fun b hb ↦ hGS c a b hb, setIntegral_const, Measure.real,
    hmeasS c]

theorem hasSum_integral_ideleMeasure_of_invariant_finiteIntegralUnits {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {F : IdeleGroup K → E}
    (hFi : Integrable F (ideleMeasure K))
    (hF : ∀ x : IdeleGroup K, ∀ w ∈ finiteIntegralUnits K,
      F (x * (IdeleGroup.prodEquiv K).symm (1, w)) = F x) :
    HasSum (fun c : (FiniteAdeleRing (𝓞 K) K)ˣ ⧸ finiteIntegralUnits K ↦
        ∫ a, F ((IdeleGroup.prodEquiv K).symm (a, c.out)) ∂infiniteIdeleMeasure K)
      (∫ x, F x ∂ideleMeasure K) := by
  have h := hasSum_integral_ideleMeasure_of_invariant (finiteIntegralUnits K)
    (isOpen_finiteIntegralUnits K) hFi hF
  simpa [finiteIdeleMeasure_finiteIntegralUnits] using h

end

end GroundTheory.Global
