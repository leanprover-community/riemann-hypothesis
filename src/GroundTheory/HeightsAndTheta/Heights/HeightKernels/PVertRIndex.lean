module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CharacterNondegenerate
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial NumberField

noncomputable section

namespace VerticalIndex

variable {T : Type} [Fintype T] {K' : Type} [Field K']

theorem aeval_mem_sectionMod (y : (Σ _ : Unit, T) → K') {s : MRing (fun _ : Unit => T)}
    (hs : IsMultiHomog s (fun _ => 1)) : aeval y s ∈ sectionMod y :=
  HilbertSamuel.NormCountBounded.secM_le_chartLat y 1 (Submodule.subset_span ⟨s, hs, rfl⟩)


omit [Fintype T] in
theorem span_toAddSubgroup (y : (Σ _ : Unit, T) → K') (x : K') :
    (Submodule.span (curveRing y) {x}).toAddSubgroup = curveMul y x := by
  ext z
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, curveMul, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩


omit [Fintype T] in
theorem genIndex_eq_card (y : (Σ _ : Unit, T) → K') {x : K'} (hx : x ∈ sectionMod y) :
    genIndex (chartLat y (fun _ => 1) 1) (curveMul y x) = Nat.card (sectionQuot y x) := by
  have hle : curveMul y x ≤ chartLat y (fun _ => 1) 1 := by
    rw [← span_toAddSubgroup]
    intro z hz
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) hz
  rw [genIndex, AddSubgroup.relIndex_eq_one.mpr hle, Nat.cast_one, div_one, ← span_toAddSubgroup]
  rfl

end VerticalIndex


open IndefiniteRowSideFullHecke.HeightsSet in
theorem VertRIndex.proof (hL : LogCardLength.Statement) (hF : SectionQuotFinite.Statement)
    (hV : VertPointLength.Statement) (hR : VertPointResidue.Statement) : VertRIndex.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  have := hF T K' y s hP hs hsP
  obtain ⟨hbij, hmult⟩ := hV T K' y s hP hs hsP
  rw [VerticalIndex.genIndex_eq_card y (VerticalIndex.aeval_mem_sectionMod y hs),
    hL (curveRing y) (sectionQuot y (aeval y s)), vertR]
  calc _ = ∑ᶠ W ∈ divSupp (mCoordIdeal y) s, (locLen (curvePtIdeal y W) (sectionQuot y (aeval y s)) : ℝ) *
          Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W)) := by
        refine finsum_mem_congr rfl fun W hW => ?_
        rw [if_neg (CurveDivVertical.full Unit (fun _ => T) _ s _ hP hs hsP W hW), hmult W hW,
          ← hR T K' y s hP hs hsP W hW]
        congr 3
    _ = ∑ᶠ m ∈ {m : Ideal (curveRing y) | m.IsMaximal ∧ locLen m (sectionQuot y (aeval y s)) ≠ 0},
          (locLen m (sectionQuot y (aeval y s)) : ℝ) * Real.log (Nat.card (curveRing y ⧸ m)) :=
        finsum_mem_eq_of_bijOn _ hbij fun _ _ => rfl
    _ = _ := by
        refine finsum_mem_inter_support_eq _ _ {m : Ideal (curveRing y) | m.IsMaximal} ?_
        ext m
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, fun h0 => h2 (by simp [h0])⟩, h2⟩⟩

end

end GroundTheory.Heights₂.Heights
