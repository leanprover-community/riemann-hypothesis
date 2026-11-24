module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Index
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb

@[expose] public section

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pAvgK :
    ∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out := by
  intro X V _ _ _ K K₀ hle hidx Ψ hΨ
  haveI : Finite (K ⧸ K₀.subgroupOf K) := Nat.finite_of_card_ne_zero hidx
  haveI : Fintype (K ⧸ K₀.subgroupOf K) := Fintype.ofFinite _
  let e := Subgroup.quotientEquivProdOfLE hle
  let F : X ⧸ K → V := fun y => Ψ y.out
  have he : ∀ x : X ⧸ K₀, Ψ x.out = F (e x).1 := by
    intro x
    have h1 : (e x).1 = ((x.out : X) : X ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' x]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x.out
    simp only [F, h1, hk, hΨ k k.2]
  have hcard : Fintype.card (K ⧸ K₀.subgroupOf K) = K₀.relIndex K := by
    rw [Fintype.card_eq_nat_card]
    rfl
  have h2 : ∑ᶠ x : X ⧸ K₀, Ψ x.out = ∑ᶠ p : (X ⧸ K) × (K ⧸ K₀.subgroupOf K), F p.1 :=
    (finsum_congr he).trans (finsum_comp_equiv e (f := fun p => F p.1))
  rw [h2]
  by_cases hfin : (Function.support F).Finite
  · have hG : Function.HasFiniteSupport (fun p : (X ⧸ K) × (K ⧸ K₀.subgroupOf K) => F p.1) := by
      refine (hfin.prod (Set.finite_univ (α := K ⧸ K₀.subgroupOf K))).subset ?_
      intro p hp
      exact ⟨hp, trivial⟩
    rw [finsum_curry _ hG, smul_finsum]
    refine finsum_congr fun a => ?_
    show ∑ᶠ _ : K ⧸ K₀.subgroupOf K, Ψ a.out = _
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, hcard, Nat.cast_smul_eq_nsmul ℂ]
  · have h3 : ∑ᶠ y : X ⧸ K, Ψ y.out = 0 := finsum_of_infinite_support hfin
    rw [h3, smul_zero]
    apply finsum_of_infinite_support
    intro hG
    apply hfin
    refine (hG.image Prod.fst).subset ?_
    intro a ha
    exact ⟨(a, ((1 : K) : K ⧸ K₀.subgroupOf K)), ha, rfl⟩
