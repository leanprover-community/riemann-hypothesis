module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.cobIndex :
    ∀ (O Γ : Type) [CommRing O] [IsDomain O] [CharZero O] [Group Γ] (θ : Γ →* Oˣ) (z : Γ → O), Coc θ z → ∀ U D : Subgroup Γ, U.relIndex D ≠ 0 → CobOn θ z (U ⊓ D) → CobOn θ z D := by
  intro O Γ _ _ _ _ θ z hz U D hUD hcob
  obtain ⟨a, ha, m, hm⟩ := hcob
  haveI : (U.subgroupOf D).FiniteIndex := ⟨hUD⟩
  haveI : Fintype (D ⧸ U.subgroupOf D) := Fintype.ofFinite _
  let T : D ⧸ U.subgroupOf D → O := fun q => a * z ((q.out : D) : Γ) - (θ ((q.out : D) : Γ) : O) * m
  have key : ∀ (g : D) (q : D ⧸ U.subgroupOf D), T (g • q) = a * z (g : Γ) + (θ (g : Γ) : O) * T q := by
    intro g q
    have e1 : g • q = (QuotientGroup.mk (g * q.out) : D ⧸ U.subgroupOf D) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf D) (g * q.out)
    have hhU : ((h : D) : Γ) ∈ U ⊓ D := ⟨Subgroup.mem_subgroupOf.1 h.2, (h : D).2⟩
    have hmh := hm _ hhU
    simp only [T]
    rw [e1, hh]
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul]
    rw [hz, hz]
    simp only [map_mul, Units.val_mul]
    linear_combination (θ (g : Γ) : O) * (θ ((q.out : D) : Γ) : O) * hmh
  have hn : (Fintype.card (D ⧸ U.subgroupOf D) : O) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  refine ⟨(Fintype.card (D ⧸ U.subgroupOf D) : O) * a, mul_ne_zero hn ha, -(∑ q, T q), ?_⟩
  intro g hg
  have hs : ∑ q, T ((MulAction.toPerm (⟨g, hg⟩ : D)) q) = ∑ q, T q := Equiv.sum_comp _ T
  simp only [MulAction.toPerm_apply, key, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hs
  linear_combination hs
