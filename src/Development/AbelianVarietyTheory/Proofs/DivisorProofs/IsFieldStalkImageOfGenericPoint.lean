module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem isField_stalk_of_forall_specializes {Z : Scheme.{0}} (ζ : Z) [IsDomain (Z.presheaf.stalk ζ)]
    (h : ∀ z : Z, z ⤳ ζ → z = ζ) : IsField (Z.presheaf.stalk ζ) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  let p : Spec (Z.presheaf.stalk ζ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Z.presheaf.stalk ζ))
  have hp : Z.fromSpecStalk ζ p ∈ Set.range (Z.fromSpecStalk ζ) := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  have h1 : Z.fromSpecStalk ζ p = Z.fromSpecStalk ζ (IsLocalRing.closedPoint _) :=
    (h _ hp).trans Scheme.fromSpecStalk_closedPoint.symm
  have h2 := (Z.fromSpecStalk ζ).isEmbedding.injective h1
  exact (congrArg PrimeSpectrum.asIdeal h2).symm

theorem isField_stalk_genPt :
    ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z], IsOpen (Set.range π) →
    IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  intro Y Z π _ _ hW
  haveI := GlobalTheory.IsNormalScheme.isDomain_stalk (X := Z) (genPt π)
  refine isField_stalk_of_forall_specializes _ fun z hz => ?_
  obtain ⟨y, rfl⟩ : z ∈ Set.range π := hz.mem_open hW ⟨_, rfl⟩
  exact (hz.antisymm ((genericPoint_specializes y).map π.continuous)).eq

end GlobalTheory.NormSheafDescent
