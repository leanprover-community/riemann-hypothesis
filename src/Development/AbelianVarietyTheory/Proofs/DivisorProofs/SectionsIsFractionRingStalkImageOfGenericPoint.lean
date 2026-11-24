module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem sections_isDomain_isFractionRing_stalk : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z] (U : Z.Opens), IsAffineOpen U →
    (U : Set Z) ⊆ Set.range π → ∀ h : GlobalTheory.NormSheafDescent.genPt π ∈ U,
    IsDomain Γ(Z, U) ∧ (letI := GlobalTheory.NormSheafDescent.algAK π U h
      IsFractionRing Γ(Z, U) (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by
  intro Y Z π _ _ U hU hUr h
  set ζ := genPt π with hζ
  have hcl : (U : Set Z) ⊆ closure {ζ} := by
    rintro _ hx
    obtain ⟨y, rfl⟩ := hUr hx
    exact specializes_iff_mem_closure.mp ((genericPoint_specializes y).map π.continuous)
  have hirr : IsIrreducible (U : Set Z) :=
    ⟨⟨ζ, h⟩, (isIrreducible_singleton.closure).isPreirreducible.open_subset U.isOpen hcl⟩
  obtain ⟨hD, -⟩ := GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hirr
  refine ⟨hD, ?_⟩
  letI := algAK π U h
  have hl := hU.isLocalization_stalk ⟨ζ, h⟩
  have hbot : (hU.primeIdealOf ⟨ζ, h⟩).asIdeal = ⊥ := by
    let q : PrimeSpectrum Γ(Z, U) := ⟨⊥, Ideal.isPrime_bot⟩
    have hq : hU.fromSpec q ∈ U := hU.range_fromSpec.le ⟨_, rfl⟩
    have hs : hU.fromSpec (hU.primeIdealOf ⟨ζ, h⟩) ⤳ hU.fromSpec q := by
      rw [hU.fromSpec_primeIdealOf]
      exact specializes_iff_mem_closure.mpr (hcl hq)
    have hs' := hU.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.mp hs
    exact le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ q).mpr hs')
  have hc : (hU.primeIdealOf ⟨ζ, h⟩).asIdeal.primeCompl = nonZeroDivisors Γ(Z, U) := by
    ext x; simp [hbot, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  unfold IsLocalization.AtPrime at hl
  rw [hc] at hl
  exact hl

end GlobalTheory.NormSheafDescent
