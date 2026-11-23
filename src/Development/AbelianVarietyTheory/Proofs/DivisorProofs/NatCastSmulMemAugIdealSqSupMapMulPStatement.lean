module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open scoped TensorProduct
open Coalgebra GlobalTheory.PDiv in

theorem _root_.GlobalTheory.T.natCast_smul_mem_augIdealSq_sup_map_mulP : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))), (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 ⊔ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n a ha
  have ha₀ : counit (R := R) a = 0 := ha
  have hres : G.res n a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A n)) := by
    change counit (R := R) (G.res n a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha₀]
  have hmap : mulBy R (G.A (n + 1)) p a ∈ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
      ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
    rw [← G.mulP_res n a]
    exact Ideal.mem_map_of_mem _ hres
  have hdiff : mulBy R (G.A (n + 1)) p a - (p : R) • a ∈
      RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 := by
    have hd : dUnit (R := R) (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0 := by
      change GlobalTheory.AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))
        (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0
      rw [map_sub, map_smul]
      change dUnit (R := R) (mulBy R (G.A (n + 1)) p a) - (p : R) • dUnit (R := R) a = 0
      rw [← cotMap_d, cotMap_mulBy, sub_self]
    have h := (GlobalTheory.AugCot.d_eq_zero_iff _ _).1 hd
    have hc : Bialgebra.counitAlgHom R (G.A (n + 1))
        (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0 := by
      change counit (R := R) (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0
      rw [map_sub, map_smul, CoalgHomClass.counit_comp_apply, ha₀, smul_zero, sub_zero]
    rwa [hc, map_zero, sub_zero] at h
  have hsmul : (p : R) • a = mulBy R (G.A (n + 1)) p a - (mulBy R (G.A (n + 1)) p a - (p : R) • a) :=
    (sub_sub_cancel _ _).symm
  rw [hsmul]
  exact sub_mem (Ideal.mem_sup_right hmap) (Ideal.mem_sup_left hdiff)
