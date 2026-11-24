module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagIntegralPermute.proof (h1 : FlagCoeffBlockPermute.Statement) :
    FlagIntegralPermute.Statement := by
  classical
  intro f N w H
  let e : Fin f × Fin N ≃ Fin f × Fin N := Equiv.prodShear (Equiv.refl _) w
  have hcomp : ∀ α : Fin f × Fin N →₀ ℕ,
      (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) =
        Finsupp.equivMapDomain e.symm α := by
    intro α; ext p; simp [Finsupp.equivMapDomain_apply, e, Equiv.prodShear]
  have hH : ∀ α, AddMonoidAlgebra.coeff (blockPermute f N w H) α = AddMonoidAlgebra.coeff H (Finsupp.equivMapDomain e.symm α) := by
    intro α; rw [h1, hcomp]
  have hD : ∀ α, AddMonoidAlgebra.coeff (blockVandermonde f N) (Finsupp.equivMapDomain e.symm α) =
      blockSign f N w * AddMonoidAlgebra.coeff (blockVandermonde f N) α := by
    intro α
    rw [← hcomp, ← h1, Flag.blockPermute_blockVandermonde, MvPolynomial.coeff_smul, smul_eq_mul]
  have hs2 : blockSign f N w * blockSign f N w = 1 := Flag.blockSign_mul_self f N w
  have hs0 : blockSign f N w ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hs2; exact zero_ne_one hs2
  have hfac : ∀ α : Fin f × Fin N →₀ ℕ,
      (Finsupp.equivMapDomain e.symm α).prod (fun _ n => (n.factorial : ℚ)) =
        α.prod (fun _ n => (n.factorial : ℚ)) := by
    intro α; rw [Finsupp.prod_equivMapDomain]
  unfold flagIntegral
  rw [Finset.mul_sum]
  refine Finset.sum_equiv (Finsupp.domCongr e.symm).toEquiv (fun α => ?_) (fun α _ => ?_)
  · simp only [MvPolynomial.mem_support_iff, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv,
      Finsupp.domCongr_apply, hD]
    exact ⟨fun h => mul_ne_zero hs0 h, fun h h' => h (by rw [h', mul_zero])⟩
  · simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Finsupp.domCongr_apply, hH, hD, hfac]
    linear_combination (-(AddMonoidAlgebra.coeff H (Finsupp.equivMapDomain e.symm α) *
      AddMonoidAlgebra.coeff (blockVandermonde f N) α * α.prod (fun _ n => (n.factorial : ℚ)))) * hs2

end RestTerms

end GroundTheory.Heights₂.Heights
