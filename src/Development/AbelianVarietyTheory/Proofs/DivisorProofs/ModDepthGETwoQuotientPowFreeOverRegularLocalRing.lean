module

public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEThreeOfFreeRegularLocal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open IsLocalRing

namespace GlobalTheory


open Pointwise in
theorem modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R,
      f ≠ 0 → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B]
      [Nontrivial B] (k : ℕ), 1 ≤ k →
      ReciprocityTheory.CA.ModDepthGE R (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) 2 := by
  intro R _ _ hd f hf hf0 B _ _ _ _ _ k hk
  haveI : IsDomain R := GlobalTheory.isDomain_of_isRegularLocalRing R
  have h3 : ReciprocityTheory.CA.ModDepthGE R B 3 :=
    GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing R hd B
  have hfk0 : f ^ k ≠ 0 := pow_ne_zero k hf0
  have hfkm : f ^ k ∈ maximalIdeal R := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_succ]
    exact Ideal.mul_mem_left _ _ hf
  have hreg : IsSMulRegular B (f ^ k) := smul_right_injective B hfk0
  have h2 : ReciprocityTheory.CA.ModDepthGE R (QuotSMulTop (f ^ k) B) 2 :=
    ReciprocityTheory.CA.ModDepthGE.quotSMulTop hfkm hreg h3
  have hpow : (Ideal.span {f}).map (algebraMap R B) ^ k =
      (Ideal.span {f ^ k}).map (algebraMap R B) := by
    rw [← Ideal.map_pow, Ideal.span_singleton_pow]
  have heq : ((f ^ k) • (⊤ : Submodule R B)) =
      ((Ideal.span {f}).map (algebraMap R B) ^ k).restrictScalars R := by
    rw [hpow]
    ext x
    simp [Submodule.mem_smul_pointwise_iff_exists, Ideal.map_span, Ideal.mem_span_singleton',
      Algebra.smul_def, mul_comm]
  let e : QuotSMulTop (f ^ k) B ≃ₗ[R] (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) :=
    (Submodule.quotEquivOfEq _ _ heq).trans
      (Submodule.Quotient.restrictScalarsEquiv R ((Ideal.span {f}).map (algebraMap R B) ^ k))
  exact (ReciprocityTheory.CA.modDepthGE_congr e 2).mp h2

end GlobalTheory
