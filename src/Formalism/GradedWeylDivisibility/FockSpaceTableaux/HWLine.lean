module

public import Formalism.GradedWeylDivisibility.StatementB
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem highest_weight_line : HWLine := by
  intro K _ _ r n hn ν hν f hf hraise
  have hfP := (dualWeylPoint K r n ν f).mp hf
  have hhP := (dualWeylPoint K r n ν (hw K hn ν)).mp (hwMem K r n hn ν hν)
  have hid : ∀ (a : Fin r) (j : Fin n), a.val ≠ j.val → idPoint K r n (a, j) = 0 := by
    intro a j h
    simp [idPoint, h]
  have hP1 : ∏ v, idPoint K r n v ^ (lhwline_mnu hn ν) v = 1 := by
    refine Finset.prod_eq_one fun v _ => ?_
    obtain ⟨a, j⟩ := v
    rw [lhwline_mnu_apply]
    by_cases h : a.val = j.val <;> simp [idPoint, h]
  have hcf : eval (idPoint K r n) f = AddMonoidAlgebra.coeff f (lhwline_mnu hn ν) := by
    rw [lhwline_diag hn ν f hfP.1 _ hid, hP1, mul_one]
  have hch : AddMonoidAlgebra.coeff (hw K hn ν) (lhwline_mnu hn ν) = 1 := by
    have h1 := lhwline_diag hn ν (hw K hn ν) hhP.1 _ hid
    rw [hP1, mul_one] at h1
    rw [← h1]
    simp [hw, eval_idPoint_lpMinor]
  set c := eval (idPoint K r n) f with hc
  refine ⟨c, ?_⟩
  have hgw : IsWeightedHomogeneous (colW r n) (f - c • hw K hn ν) ν := by
    have h1 : f ∈ weightedHomogeneousSubmodule K (colW r n) ν :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hfP.1
    have h2 : hw K hn ν ∈ weightedHomogeneousSubmodule K (colW r n) ν :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hhP.1
    exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (Submodule.sub_mem _ h1 (Submodule.smul_mem _ c h2))
  have hg0 : f - c • hw K hn ν = 0 := by
    apply lhwline_vanish
    · intro a b hab
      rw [map_sub, map_smul, lhwline_rowGen_eq a b f (hraise a b hab),
        lhwline_rowGen_eq a b (hw K hn ν) (fun k hk => hwRaise K r n hn ν a b k hab hk)]
      simp [Polynomial.smul_C]
    · intro l j hlj c'
      rw [map_sub, map_smul, hfP.2 l j hlj c', hhP.2 l j hlj c']
    · intro D hD
      rw [lhwline_diag hn ν _ hgw D hD, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, hch, ← hcf]
      simp
  exact sub_eq_zero.mp hg0

end Formalism.GradedWeylDivisibility
