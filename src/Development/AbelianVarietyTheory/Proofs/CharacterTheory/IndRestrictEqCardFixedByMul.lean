module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedClassFunctionFromSubgroupEqFinsumCosets
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

open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

theorem out_conj_mem_iff_smul_eq {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    q.out⁻¹ * g * q.out ∈ H ↔ g • q = q := by
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, ← H.inv_mem_iff]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem ind_restrict_eq_card_fixedBy_mul : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (χ : G → L), (∀ g x : G, χ (x⁻¹ * g * x) = χ g) → ∀ g : G, ind H (fun h : H => χ h) g = (Nat.card (MulAction.fixedBy (G ⧸ H) g) : L) * χ g := by
  intro L _ _ G _ _ H χ hχ g
  classical
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hψ : ∀ h x : H, (fun h : H => χ h) (x⁻¹ * h * x) = (fun h : H => χ h) h := by
    intro h x
    simpa using hχ h x
  have hterm : ∀ q : G ⧸ H, ext0 H (fun h : H => χ h) (q.out⁻¹ * g * q.out)
      = (if g • q = q then (1 : L) else 0) * χ g := by
    intro q
    unfold ext0
    by_cases hq : g • q = q
    · have hm := (out_conj_mem_iff_smul_eq H g q).2 hq
      rw [dite_eq_left hm, if_pos hq, one_mul]
      exact hχ g q.out
    · have hm : q.out⁻¹ * g * q.out ∉ H := fun h => hq ((out_conj_mem_iff_smul_eq H g q).1 h)
      rw [dite_eq_right hm, if_neg hq, zero_mul]
  rw [ind_eq_finsum_cosets L G H _ hψ g, finsum_eq_sum_of_fintype]
  simp_rw [hterm]
  rw [← Finset.sum_mul, Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end GlobalTheory.BI
