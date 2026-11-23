module

public import Formalism.WachLatticeTwists.CoprimeLiftBounds.SelmerInjColumnPlace
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Imports
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

theorem selmer_inj_tensor_form : SelmerInjTensorForm := by
  intro O _ _ _ D _ L V M _ _ _ _ _ _ _ _ ρL ρV ρM i q tens htens hi hq hker hsat hiρ hqρ Ff j κ
    hF1 hF2 hF3 hF4 x m hx a
  choose y hy using fun b => Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (x b)
  have hsum : ∀ g, q (∑ b, y b • i ((κ b : D → L) g)) = ρM g m - m := by
    intro g

    rw [← hx g, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hy b, htens]
  have key := c3 O D L V M ρL ρV ρM i q hi hq hker hsat hiρ hqρ Ff j κ hF1 hF2 hF3 hF4 y m hsum a
  rw [← hy a]
  exact (Submodule.Quotient.mk_eq_zero _).mpr key

theorem selmer_inj_column_place : SelmerInjColumnPlace := by
  intro O _ _ _ A T' G _ _ _ _ M _ _ _ _ L _ _ _ _ V _ _ _ _ _ _ r χ Dl i q tens hiA hqA htens hi hq
    hker hsat Ff j κ κz hκ hF1 hF2 hF3 hF4 x hx
  obtain ⟨m, hm⟩ := LinearMap.mem_range.mp hx
  refine selmer_inj_tensor_form O Dl L V M (resRep (uRep O (M := L) r χ) Dl)
    (resRep (uRep (FractionRing O) (M := V) r χ) Dl) (resRep (uRep O (M := M) r χ) Dl) i q tens
    htens hi hq hker hsat ?_ ?_ Ff j κz hF1 hF2 hF3 hF4 x m ?_
  · intro g v
    exact hiA (uElt r χ (g : G)) v
  · intro g v
    exact hqA (uElt r χ (g : G)) v
  · intro g
    have h1 := congrFun hm g
    simp only [hκ]
    exact h1.symm

end Formalism.RepresentationBoundsCohomology.BR
