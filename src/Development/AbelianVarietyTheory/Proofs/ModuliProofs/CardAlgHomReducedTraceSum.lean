module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

theorem finite_card_trace_algHom_of_isReduced_baseChange :
    ∀ (O H K : Type) [CommRing O] [Nontrivial O] [CommRing H] [Algebra O H] [Module.Free O H]
      [Module.Finite O H] [Field K] [IsAlgClosed K] [Algebra O K], IsReduced (K ⊗[O] H) →
      Finite (H →ₐ[O] K) ∧ Nat.card (H →ₐ[O] K) = Module.finrank O H ∧
        ∀ h : H, algebraMap O K (Algebra.trace O H h) = ∑ᶠ ga : H →ₐ[O] K, ga h := by
  classical
  intro O H K _ _ _ _ _ _ _ _ _ hred
  have : IsReduced (K ⊗[O] H) := hred
  have hcard : Nat.card (H →ₐ[O] K) = Module.finrank O H :=
    natCard_algHom_eq_finrank_of_isReduced_baseChange O H K
  have hfin : Finite (H →ₐ[O] K) := by
    by_cases h0 : Module.finrank O H = 0
    · have : IsEmpty (H →ₐ[O] K) := by
        refine ⟨fun f => ?_⟩
        have hι : IsEmpty (Module.Free.ChooseBasisIndex O H) := by
          rw [← Fintype.card_eq_zero_iff, ← Module.finrank_eq_card_chooseBasisIndex]
          exact h0
        have h10 : (1 : H) = 0 :=
          (Module.Free.chooseBasis O H).repr.injective (Subsingleton.elim _ _)
        have h1 := congrArg f h10
        rw [map_one, map_zero] at h1
        exact one_ne_zero h1
      infer_instance
    · exact Nat.finite_of_card_ne_zero (hcard ▸ h0)
  refine ⟨hfin, hcard, fun h => ?_⟩
  let _ := Fintype.ofFinite (H →ₐ[O] K)
  rw [finsum_eq_sum_of_fintype]
  exact algebraMap_trace_eq_sum_algHom_of_card (R := O) (S := H) (L := K)
    (by rw [← Nat.card_eq_fintype_card, hcard]) (P := fun g => g) (fun _ _ e => e) h

end GlobalTheory
