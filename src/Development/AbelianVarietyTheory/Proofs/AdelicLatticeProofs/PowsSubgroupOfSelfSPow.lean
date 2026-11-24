module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSUnitsNumberFieldAddOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexTopOfGroupFg
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm


open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in
theorem _root_.GlobalTheory.CNorm.pTor_pIdx_sUnits : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F]
    (ζ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p →
    _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) = p ∧
      _root_.GlobalTheory.CNorm.pIdx p (_root_.GlobalTheory.QNorm.sUnits F S) =
        p ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro p F _ _ ζ S hp hζ
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Group.FG (_root_.GlobalTheory.QNorm.sUnits F S) := _root_.GlobalTheory.QNorm.sUnits_fg F S
  obtain ⟨-, h2⟩ := _root_.GlobalTheory.CNorm.pIdx_top_of_fg p (_root_.GlobalTheory.QNorm.sUnits F S) hp.pos
  have hroots : ∀ x : Fˣ, x ^ p = 1 → x ∈ _root_.GlobalTheory.QNorm.sUnits F S := by
    intro x hx
    rw [_root_.GlobalTheory.QNorm.mem_sUnits]
    intro v _
    have h := congrArg (fun y : Fˣ => HeightOneSpectrum.valuation F v (y : F)) hx
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h
    exact (pow_eq_one_iff_of_nonneg zero_le' hp.ne_zero).mp h
  have htor : _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) = p := by
    unfold _root_.GlobalTheory.CNorm.pTor
    refine (Nat.card_congr ?_).trans hζ.card_rootsOfUnity
    exact
      { toFun := fun x => ⟨x.1, (mem_rootsOfUnity p x.1).mpr x.2.2⟩
        invFun := fun y => ⟨y.1, hroots y.1 ((mem_rootsOfUnity p y.1).mp y.2),
          (mem_rootsOfUnity p y.1).mp y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have htorTop : _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup (_root_.GlobalTheory.QNorm.sUnits F S)) =
      _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) := by
    unfold _root_.GlobalTheory.CNorm.pTor
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, by rw [← Subgroup.coe_pow, x.2.2, OneMemClass.coe_one]⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subgroup.mem_top _, Subtype.ext y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hidxTop : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup (_root_.GlobalTheory.QNorm.sUnits F S)) =
      _root_.GlobalTheory.CNorm.pIdx p (_root_.GlobalTheory.QNorm.sUnits F S) := by
    unfold _root_.GlobalTheory.CNorm.pIdx _root_.GlobalTheory.CNorm.pows
    rw [Subgroup.relIndex_top_right]
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, powMonoidHom_apply,
      Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, y.2, by rw [← hy]; rfl⟩
    · rintro ⟨y, hyH, hy⟩
      exact ⟨⟨y, hyH⟩, Subtype.ext hy⟩
  refine ⟨htor, ?_⟩
  rw [← hidxTop, h2, htorTop, htor, ← _root_.GlobalTheory.QNorm.sUnits_rank F S, pow_succ]

end GlobalTheory.CNorm
