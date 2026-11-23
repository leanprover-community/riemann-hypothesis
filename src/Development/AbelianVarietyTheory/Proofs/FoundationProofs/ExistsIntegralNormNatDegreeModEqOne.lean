module

public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
public import Mathlib.RingTheory.Localization.NormTrace

@[expose] public section

open Polynomial

namespace GlobalTheory


open Polynomial in
theorem _root_.GlobalTheory.exists_integral_norm_natDegree_mod_eq_one :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
      [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (N : ℕ), 1 ≤ N →
      ∃ f : FunctionField.ringOfIntegers k K, f ≠ 0 ∧ (Algebra.norm k[X] f).natDegree % N = 1 % N := by
  intro k K _ _ _ _ _ _ _ _ N hN
  set O := FunctionField.ringOfIntegers k K
  have hC1 : _root_.GlobalTheory.NeedB.IsFirstChernClassOfLineBundle (RatFunc k) := by
    unfold _root_.GlobalTheory.NeedB.IsFirstChernClassOfLineBundle
    intro n d f hf hd hdn
    obtain ⟨x, hx, h⟩ := _root_.GlobalTheory.tsenLang_ratFunc k n 1 d (fun _ => f) (fun _ => hf) hd (by simpa using hdn)
    exact ⟨x, hx, h 0⟩
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.norm_surjective_of_is_c1 (RatFunc k) K hC1
    RatFunc.X RatFunc.X_ne_zero
  haveI : Module.IsTorsionFree k[X] K := .trans_faithfulSMul k[X] (RatFunc k) K
  haveI : Module.Free k[X] O := Module.free_of_finite_type_torsion_free'
  haveI := IsIntegralClosure.isLocalization k[X] (RatFunc k) K O
  have hnorm : ∀ a : O, algebraMap k[X] (RatFunc k) (Algebra.norm k[X] a) =
      Algebra.norm (RatFunc k) (algebraMap O K a) := fun a =>
    (Algebra.norm_localization k[X] (nonZeroDivisors k[X]) (Rₘ := RatFunc k) (Sₘ := K) a).symm
  obtain ⟨⟨a, s⟩, hxa⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid O (nonZeroDivisors k[X])) x
  obtain ⟨b, hb, hbs⟩ := s.2
  simp only at hxa
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set r := Module.finrank k[X] O
  have hs : Algebra.norm k[X] (s : O) = b ^ r := by rw [← hbs]; exact Algebra.norm_algebraMap b
  have ha : Algebra.norm k[X] a = X * b ^ r := by
    apply IsFractionRing.injective k[X] (RatFunc k)
    rw [hnorm, ← hxa, map_mul, hx, ← hnorm, hs, map_mul, RatFunc.algebraMap_X]
  have hexp : r + r * (N - 1) = r * N := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hf : Algebra.norm k[X] (a * (s : O) ^ (N - 1)) = X * b ^ (r * N) := by
    rw [map_mul, map_pow, ha, hs, mul_assoc, ← pow_mul, ← pow_add, hexp]
  refine ⟨a * (s : O) ^ (N - 1), ?_, ?_⟩
  · intro h
    have h0 := hf
    rw [h, Algebra.norm_zero] at h0
    exact mul_ne_zero X_ne_zero (pow_ne_zero _ hb0) h0.symm
  · rw [hf, natDegree_mul X_ne_zero (pow_ne_zero _ hb0), natDegree_X, natDegree_pow,
      show r * N * b.natDegree = r * b.natDegree * N by ring, Nat.add_mul_mod_self_right]

end GlobalTheory
