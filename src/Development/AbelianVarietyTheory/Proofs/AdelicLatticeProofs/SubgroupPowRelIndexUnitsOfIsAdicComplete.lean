module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowIndexTorsionKerRangeMulStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexOneUnitsMulEqCardQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowImageUnitsCongruentOneModOfIsAdicCompStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pIdx_eq_pTor_of_finite_group (p : ℕ) {G : Type} [CommGroup G] [Finite G]
    (U : Subgroup G) : pTor p U ≠ 0 ∧ pIdx p U = pTor p U := by
  have h1 : pTor p U = Nat.card (powMonoidHom p : U →* U).ker := by
    unfold pTor
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
        invFun := fun y => ⟨y.1.1, y.1.2, congrArg Subtype.val y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h2 : pIdx p U = (powMonoidHom p : U →* U).range.index := by
    unfold pIdx pows Subgroup.relIndex
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext h⟩
    · rintro ⟨y, h⟩
      exact ⟨y.1, y.2, congrArg Subtype.val h⟩
  have h3 := (powMonoidHom p : U →* U).range.card_mul_index
  have h4 := (powMonoidHom p : U →* U).ker.card_mul_index
  rw [Subgroup.index_ker] at h4
  have h5 : Nat.card (powMonoidHom p : U →* U).range ≠ 0 := Nat.card_pos.ne'
  refine ⟨h1 ▸ Nat.card_pos.ne', ?_⟩
  rw [h1, h2]
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h5)
  rw [h3, ← h4, mul_comm]

theorem pIdx_units_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → Nat.card (O ⧸ Ideal.span {(p : O) * π}) ≠ 0 → pTor p (⊤ : Subgroup Oˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Oˣ) = Nat.card (O ⧸ Ideal.span {(p : O)}) * pTor p (⊤ : Subgroup Oˣ) := by
  intro p O _ _ _ π hp hπ hc hfin
  haveI : Finite (O ⧸ Ideal.span {(p : O) * π}) := Nat.finite_of_card_ne_zero hfin
  have hp0 : (p : O) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  obtain ⟨hd1, hd2⟩ := GlobalTheory.T.subgroupPowImage_unitsCongruentOneMod_of_isAdicComplete p O π hp hπ hc
  have hle : Ideal.span {(p : O) * π} ≤ Ideal.span {π} :=
    Ideal.span_singleton_le_span_singleton.mpr (Dvd.intro_left _ rfl)
  have hle' : Ideal.span {(p : O) * π} ≤ Ideal.span {(p : O)} :=
    Ideal.span_singleton_le_span_singleton.mpr (Dvd.intro _ rfl)
  have hs := GlobalTheory.T.relIndex_oneUnits_mul_eq_card_quotient' O ((p : O) * π) p (mul_ne_zero hp0 hπ) (Dvd.intro _ rfl)
    (hle.trans (IsAdicComplete.le_jacobson_bot _))
  have hk : pIdx p (oneUnits ((p : O) * π)) = Nat.card (O ⧸ Ideal.span {(p : O)}) := by
    unfold pIdx
    rw [hd1, ← hs, sq, mul_assoc]
  haveI : Finite (O ⧸ Ideal.span {(p : O)}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle')
  have hk0 : Nat.card (O ⧸ Ideal.span {(p : O)}) ≠ 0 := Nat.card_pos.ne'
  let g : Oˣ →* (O ⧸ Ideal.span {(p : O) * π})ˣ :=
    Units.map (Ideal.Quotient.mk (Ideal.span {(p : O) * π}) : O →* O ⧸ Ideal.span {(p : O) * π})
  have hker : g.ker = oneUnits ((p : O) * π) := rfl
  obtain ⟨hr1, hr2⟩ := pIdx_eq_pTor_of_finite_group p g.range
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.powIndex_torsion_ker_range_mul p _ _ g (by rw [hker, hk]; exact hk0)
    (by rw [hker, hd2]; exact one_ne_zero) (by rw [hr2]; exact hr1) hr1
  refine ⟨h2, ?_⟩
  rw [hker, hd2, hk, hr2, mul_one, mul_right_comm] at h3
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hr1) h3

end GlobalTheory.CNorm
