module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem hat_bounded_decay_holds : JDHatBdd := by
  intro P L hTT hL X hX b hb
  have hLaw : (MA.DQ P).Laws P.TT := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT
  have hS := Formalism.FourierDecayAlt.P.MAx3.H.hyp_model hL hLaw
  have hV := Formalism.FourierDecayAlt.P.MAx3.K.hypV_model hL hLaw
  have gen : ∀ b' ∈ Submonoid.closure (MA.bddSet P L), ∀ X' ∈ MA.hatSet P L,
      b' * X' ∈ Submodule.span ℂ (bddHat P L) := fun b' hb' X' hX' =>
    Submodule.subset_span ⟨b', hb', X', hX', rfl⟩
  have mA : ∀ y, L.Ahat y ∈ MA.hatSet P L := fun y => Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))
  have mR : ∀ y, L.R0 y ∈ MA.hatSet P L := fun y => Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))
  have mAv : ∀ y, L.Ahatv y ∈ MA.hatSet P L := fun y => Or.inl (Or.inr ⟨y, rfl⟩)
  have mRv : ∀ y, L.R0v y ∈ MA.hatSet P L := fun y => Or.inr ⟨y, rfl⟩
  have sumA : ∀ ts : List (ℂ × MA.A P (MA.DQ P) × ℂ), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (MA.bddSet P L)) →
      (ts.map fun x => x.1 • (x.2.1 * L.Ahat x.2.2)).sum ∈ Submodule.span ℂ (bddHat P L) := by
    intro ts hts
    refine list_sum_mem fun u hu => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    exact Submodule.smul_mem _ _ (gen _ (hts x hx) _ (mA _))
  have sumAv : ∀ ts : List (ℂ × MA.A P (MA.DQ P) × ℂ), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (MA.bddSet P L)) →
      (ts.map fun x => x.1 • (x.2.1 * L.Ahatv x.2.2)).sum ∈ Submodule.span ℂ (bddHat P L) := by
    intro ts hts
    refine list_sum_mem fun u hu => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    exact Submodule.smul_mem _ _ (gen _ (hts x hx) _ (mAv _))
  rcases hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
  · obtain ⟨t, ht⟩ := hS.ahat b hb
    rw [ht y]; exact gen _ hb _ (mA _)
  · obtain ⟨t, ts, hts, he⟩ := hS.r0 b hb y
    rw [he]; exact Submodule.add_mem _ (gen _ hb _ (mR _)) (sumA ts hts)
  · obtain ⟨t, ht⟩ := hV.ahatv b hb
    rw [ht y]; exact gen _ hb _ (mAv _)
  · obtain ⟨t, ts, hts, he⟩ := hV.r0v b hb y
    rw [he]; exact Submodule.add_mem _ (gen _ hb _ (mRv _)) (sumAv ts hts)

end

end Formalism.FourierDecayAlt.P.CutMP
