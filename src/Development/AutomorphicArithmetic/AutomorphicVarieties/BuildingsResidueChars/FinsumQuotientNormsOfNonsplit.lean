module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsNE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NonsqMul
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

theorem UpperTheory.finsum_quotient_norms_of_nonsplit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ¬ IsSquare (τ ^ 2 - 4) → (∃ g : Kˣ, g ∉ NE τ) ∧ ∀ f : Kˣ → ℂ, (∀ t ∈ NE τ, ∀ x, f (t * x) = f x) → ∀ g : Kˣ, g ∉ NE τ → (∑ᶠ t : Kˣ ⧸ NE τ, f t.out) = f 1 + f g := by
  intro O K _ _ _ _ _ Δ τ L hτ hs0
  classical
  have hN := hsNE O K Δ τ L hτ
  refine ⟨?_, fun f hf g hg => ?_⟩
  · obtain ⟨x, hx, h⟩ := (hsLaw O K Δ L).2.2.1 _ hτ hs0
    exact ⟨Units.mk0 x hx, fun h' => by have := (hN _).1 h'; rw [Units.val_mk0, h] at this; norm_num at this⟩
  have neg : ∀ t : Kˣ, t ∉ NE τ → hs (τ ^ 2 - 4) (t : K) = -1 := fun t ht => by
    have := mt (hN t).2 ht
    unfold hs at this ⊢
    split_ifs at this ⊢ with h
    · exact absurd rfl this
    · rfl
  have out : ∀ x : Kˣ, f (x : Kˣ ⧸ NE τ).out = f x := fun x => by
    have : x⁻¹ * (x : Kˣ ⧸ NE τ).out ∈ NE τ := QuotientGroup.eq.1 (by simp)
    rw [← hf _ this x, mul_comm _ x, mul_inv_cancel_left]
  have hne : ((1 : Kˣ) : Kˣ ⧸ NE τ) ≠ (g : Kˣ ⧸ NE τ) := fun h => hg (by simpa using QuotientGroup.eq.1 h)
  rw [finsum_eq_sum_of_support_subset (s := {((1 : Kˣ) : Kˣ ⧸ NE τ), (g : Kˣ ⧸ NE τ)}) _ fun t _ => ?_, Finset.sum_pair hne, out, out]
  induction t using QuotientGroup.induction_on with
  | H t =>
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases ht : t ∈ NE τ
    · exact .inl (QuotientGroup.eq.2 (by simpa using ht))
    · refine .inr (QuotientGroup.eq.2 ((hN _).2 ?_))
      rw [Units.val_mul, hsMul O K Δ L _ _ _ hτ (Units.ne_zero _) g.ne_zero, neg _ hg, neg _ fun h => ht (by simpa using h)]
      norm_num
