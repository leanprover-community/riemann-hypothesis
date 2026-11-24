module

public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

theorem conv_mul_right {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₂ : IsBiInv K f₂) (g : G) (b : K) : conv K f₁ f₂ (g * b) = conv K f₁ f₂ g := by
  unfold conv
  congr 1
  funext x
  have h := hf₂ 1 b (x.out⁻¹ * g)
  simp only [OneMemClass.coe_one, one_mul] at h
  rw [← mul_assoc, h]

theorem conv_mul_left {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) (a : K) (g : G) :
    conv K f₁ f₂ ((a : G) * g) = conv K f₁ f₂ g := by
  have key : ∀ y : G ⧸ K, ∃ c : K, ((a : G) • y).out = (a : G) * y.out * c := by
    intro y
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K ((a : G) * y.out)
    refine ⟨c, ?_⟩
    have e : (a : G) • y = (QuotientGroup.mk ((a : G) * y.out) : G ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' y]
      rfl
    rw [e, hc]
  unfold conv
  refine (finsum_comp_equiv (MulAction.toPerm (a : G) : Equiv.Perm (G ⧸ K))).symm.trans ?_
  congr 1
  funext y
  obtain ⟨c, hc⟩ := key y
  simp only [MulAction.toPerm_apply]
  rw [hc, hf₁ a c y.out]
  have e2 : ((a : G) * y.out * c)⁻¹ * ((a : G) * g) = ((c⁻¹ : K) : G) * (y.out⁻¹ * g) * ((1 : K) : G) := by
    simp only [InvMemClass.coe_inv, OneMemClass.coe_one, mul_one]
    group
  rw [e2, hf₂]

theorem conv_biInv {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) : IsBiInv K (conv K f₁ f₂) := by
  intro a b g
  rw [conv_mul_right K f₁ f₂ hf₂ ((a : G) * g) b, conv_mul_left K f₁ f₂ hf₁ hf₂ a g]

theorem conv_finDosetSupp {k : Type} [CommRing k] {K : Subgroup G} (hK : IsCommensurated K)
    (f₁ f₂ : G → k) (hs₁ : FinDosetSupp K f₁) (hs₂ : FinDosetSupp K f₂) :
    FinDosetSupp K (conv K f₁ f₂) := by
  classical
  have hX := finite_support_cosets hK hs₁
  obtain ⟨S₂, hS₂⟩ := hs₂
  set T : Set G := ⋃ t ∈ (S₂ : Set G), ⋃ x ∈ {x : G ⧸ K | f₁ x.out ≠ 0},
    ⋃ y ∈ {y : G ⧸ K | ∃ a b : K, y.out = (a : G) * t * b}, {x.out * y.out} with hTdef
  have hT : T.Finite :=
    S₂.finite_toSet.biUnion fun t _ => hX.biUnion fun x _ =>
      (finite_cosets_in_doset hK t).biUnion fun y _ => Set.finite_singleton _
  refine ⟨hT.toFinset, fun g hg => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : G ⧸ K, f₁ x.out * f₂ (x.out⁻¹ * g) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg (finsum_eq_zero_of_forall_eq_zero h)
  have h1 : f₁ x.out ≠ 0 := left_ne_zero_of_mul hx
  have h2 : f₂ (x.out⁻¹ * g) ≠ 0 := right_ne_zero_of_mul hx
  obtain ⟨t, ht, a, b, hab⟩ := hS₂ _ h2
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K ((a : G) * t)
  refine ⟨x.out * (QuotientGroup.mk ((a : G) * t) : G ⧸ K).out, ?_, 1, c⁻¹ * b, ?_⟩
  · rw [Set.Finite.mem_toFinset, hTdef]
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ⟨t, ht, x, h1, _, ⟨a, c, hc⟩, rfl⟩
  · rw [hc]
    have e : g = x.out * (x.out⁻¹ * g) := by group
    rw [e, hab]
    simp only [OneMemClass.coe_one, one_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
    group

theorem hecke_convolution_mem_holds : Formalism.UG.HeckeConvMem := by
  intro G _ K k _ hK f₁ hf₁ f₂ hf₂
  have h1 : IsBiInv K f₁ ∧ FinDosetSupp K f₁ := hf₁
  have h2 : IsBiInv K f₂ ∧ FinDosetSupp K f₂ := hf₂
  show IsBiInv K (conv K f₁ f₂) ∧ FinDosetSupp K (conv K f₁ f₂)
  exact ⟨conv_biInv K f₁ f₂ h1.1 h2.1, conv_finDosetSupp hK f₁ f₂ h1.2 h2.2⟩

theorem convolution_count_holds : Formalism.UG.ConvCount := by
  classical
  intro G _ K k _ hK a b g
  set S : Set (G ⧸ K) := {x : G ⧸ K | x.out ∈ DoubleCoset.doubleCoset a (K : Set G) K ∧
    x.out⁻¹ * g ∈ DoubleCoset.doubleCoset b (K : Set G) K} with hSdef
  have hfin : S.Finite := by
    refine (finite_cosets_in_doset hK a).subset fun x hx => ?_
    obtain ⟨h, hh, c, hc, e⟩ := DoubleCoset.mem_doubleCoset.1 hx.1
    exact ⟨⟨h, hh⟩, ⟨c, hc⟩, e⟩
  have hterm : ∀ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) =
      if x ∈ S then 1 else 0 := by
    intro x
    simp only [dosetInd, Set.indicator_apply, Pi.one_apply, hSdef, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  show ∑ᶠ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) = _
  rw [finsum_congr hterm, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
  · rw [Finset.sum_congr rfl (fun x hx => if_pos (hfin.mem_toFinset.1 hx))]
    simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  · intro x hx
    rw [Function.mem_support] at hx
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hx (if_neg h)

end Formalism.UG.P
