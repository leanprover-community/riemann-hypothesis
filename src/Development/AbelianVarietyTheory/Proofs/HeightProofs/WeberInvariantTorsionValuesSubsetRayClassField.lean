module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardEqIffStabilizer
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PrincipalRayPrimesSplitCompletelyWeberValues
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.InRayAny

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in
private theorem weberSet_subset_of_isRay_span_natCast :
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 →
      discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) →
      ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R],
      _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) → _root_.GlobalTheory.FieldSize.weberSet L n ⊆ R := by
  intro K _ _ h2 hd L hL n hn R _ _ hR
  obtain ⟨hM, S, hS⟩ := _root_.GlobalTheory.WeberSplitAny.splits_completely_of_three_le K h2 hd L hL n hn
  have hn0 : 0 < n := by omega
  have hN : Ideal.absNorm (Ideal.span {(n : 𝓞 K)}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn0.ne'
  have hMR : IntermediateField.adjoin (↥K) (_root_.GlobalTheory.FieldSize.weberSet L n) ≤ R := by
    apply _root_.GlobalTheory.Bauer.le_of_finite_split_not_split (↥K) ℂ R _
    refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K)
      (S.sup id + Ideal.absNorm (Ideal.span {(n : 𝓞 K)}))).preimage
      (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro 𝔭 ⟨hp, hsplit, hnot⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    by_cases hpS : Ideal.absNorm 𝔭.asIdeal ∈ S
    · exact le_add_right (Finset.le_sup (f := id) hpS)
    by_cases hn𝔭 : (n : 𝓞 K) ∈ 𝔭.asIdeal
    · refine le_add_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) ?_)
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hn𝔭)
    · exfalso
      obtain ⟨π, hπ, hπ1⟩ :=
        (_root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff (↥K) (↥R) n hn0 hR 𝔭 hn𝔭).mp hsplit
      apply hnot
      rw [hπ] at hp hpS ⊢
      exact hS π _ hp hpS rfl hπ1
  exact fun x hx => hMR (IntermediateField.subset_adjoin _ _ hx)


set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in
theorem _root_.GlobalTheory.FieldSize.InRayAny.weberSet_subset :
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 →
      discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) →
      ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R],
      _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) → _root_.GlobalTheory.FieldSize.weberSet L n ⊆ R :=
  weberSet_subset_of_isRay_span_natCast

end GlobalTheory.FieldSize.InRayAny
