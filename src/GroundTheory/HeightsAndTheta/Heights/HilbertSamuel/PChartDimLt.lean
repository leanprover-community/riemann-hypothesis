module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChartA
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Eval
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartImageNull
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Order.CompletePartialOrder

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ChartDimLtTorus, GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChangeMinimal, GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDimLt

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ChartDimLtTorus =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ChartDimLtTorus", "h": "module\n\npublic import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Finiteness.ModuleFinitePresentation\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\npublic import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChartA\nimport ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField\npublic import Mathlib.RingTheory.AlgebraicIndependent.Basic\npublic import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Algebra

noncomputable section

namespace ChartDimLt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_dim_add_card_le {J : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hJ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal J) (p : (k : K) → ι k)
    (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [𝔮.IsPrime] (h𝔮 : ReciprocityTheory.AnForm.R.chartIdeal J p ≤ 𝔮) :
    ∃ s : ℕ, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = s ∧
      ((s + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) := by
  classical
  let : CommRing (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.commRing 𝔮
  have : IsDomain (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  let y : (Σ k, ι k) → MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    fun q => C (Ideal.Quotient.mk 𝔮 (X q))
  let θ : (MvPolynomial (Σ k, ι k) ℂ) →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    aeval (fun q => (X q.1 : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) * y q)
  have hy : ∀ f : (MvPolynomial (Σ k, ι k) ℂ), aeval y f = C (Ideal.Quotient.mk 𝔮 f) := by
    intro f
    have : (aeval y : (MvPolynomial (Σ k, ι k) ℂ) →ₐ[ℂ] MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
        (IsScalarTower.toAlgHom ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)
          (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).comp (Ideal.Quotient.mkₐ ℂ 𝔮) := by
      apply MvPolynomial.algHom_ext
      intro q
      simp [y, MvPolynomial.algebraMap_eq]
    rw [this]
    simp [MvPolynomial.algebraMap_eq]
  have hJθ : J ≤ RingHom.ker θ := by
    obtain ⟨S, hS, hJS⟩ := hJ
    have hle : Ideal.span S ≤ RingHom.ker θ := by
      rw [Ideal.span_le]
      intro f hf
      obtain ⟨a, ha⟩ := hS f hf
      have hfJ : f ∈ J := by rw [hJS]; exact Ideal.subset_span hf
      have hf𝔮 : f ∈ 𝔮 := h𝔮 (Ideal.mem_sup_left hfJ)
      show θ f = 0
      simp only [θ]
      rw [ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog ha
          (X : K → MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) y, hy,
        Ideal.Quotient.eq_zero_iff_mem.mpr hf𝔮, map_zero, mul_zero]
    rw [hJS]
    exact hle
  have hdimR : ringKrullDim θ.range ≤ ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) := by
    let g : (MvPolynomial (Σ k, ι k) ℂ) ⧸ J →+* θ.range :=
      Ideal.Quotient.lift J (θ.rangeRestrict : (MvPolynomial (Σ k, ι k) ℂ) →+* θ.range)
        (fun a ha => Subtype.ext (by simpa using hJθ ha))
    refine ringKrullDim_le_of_surjective g ?_
    intro x
    obtain ⟨a, ha⟩ := θ.rangeRestrict_surjective x
    exact ⟨Ideal.Quotient.mk J a, ha⟩
  have : Algebra.FiniteType ℂ θ.range :=
    Algebra.FiniteType.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have : Algebra.FiniteType ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ 𝔮) (Ideal.Quotient.mkₐ_surjective ℂ 𝔮)
  obtain ⟨sA, hAdim, hAtr⟩ :=
    ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  obtain ⟨sR, hRdim, hRtr⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := θ.range)
  have : FaithfulSMul ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) :=
    (faithfulSMul_iff_algebraMap_injective ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)).mpr
      (algebraMap ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)).injective
  have : FaithfulSMul (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)
      (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).mpr
      (MvPolynomial.C_injective K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have : FaithfulSMul ℂ θ.range :=
    (faithfulSMul_iff_algebraMap_injective ℂ θ.range).mpr (algebraMap ℂ θ.range).injective
  have : FaithfulSMul θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    (faithfulSMul_iff_algebraMap_injective θ.range
      (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))).mpr Subtype.val_injective
  have hT1 : trdeg ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) +
      trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)

  have h1 : ∀ k, Ideal.Quotient.mk 𝔮 (X ⟨k, p k⟩ : (MvPolynomial (Σ k, ι k) ℂ)) = 1 := by
    intro k
    rw [← map_one (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq]
    exact h𝔮 (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))
  have hXk : ∀ k, (X k : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) ∈ θ.range := by
    intro k
    refine (θ.mem_range).mpr ⟨X ⟨k, p k⟩, ?_⟩
    simp only [θ, y, aeval_X, h1, map_one, mul_one]
  have hXq : ∀ q, (X q.1 : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) * y q ∈ θ.range := fun q =>
    (θ.mem_range).mpr ⟨X q, by simp only [θ, aeval_X]⟩
  let AC := Subalgebra.algebraicClosure θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮))
  have hRAC : ∀ t ∈ θ.range, t ∈ AC := fun t ht =>
    (Subalgebra.mem_algebraicClosure _ _).mpr (isAlgebraic_algebraMap (⟨t, ht⟩ : θ.range))
  have hyAC : ∀ q, y q ∈ AC := fun q =>
    (Subalgebra.mem_algebraicClosure _ _).mpr (IsAlgebraic.of_mul
      (mem_nonZeroDivisors_of_ne_zero (X_ne_zero q.1))
      ((Subalgebra.mem_algebraicClosure _ _).mp (hRAC _ (hXk q.1)))
      ((Subalgebra.mem_algebraicClosure _ _).mp (hRAC _ (hXq q))))
  have hCAC : ∀ f : (MvPolynomial (Σ k, ι k) ℂ), C (Ideal.Quotient.mk 𝔮 f) ∈ AC := by
    intro f
    refine MvPolynomial.induction_on (motive := fun f => C (Ideal.Quotient.mk 𝔮 f) ∈ AC) f ?_ ?_ ?_
    · intro c
      apply hRAC
      refine (θ.mem_range).mpr ⟨C c, ?_⟩
      simp only [θ, aeval_C, MvPolynomial.algebraMap_apply]
      rfl
    · intro f g hf hg
      rw [map_add (f := _), map_add (f := _)]
      exact AC.add_mem hf hg
    · intro f q hf
      rw [map_mul, map_mul]
      exact AC.mul_mem hf (hyAC q)
  have hall : ∀ t : MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮), t ∈ AC := by
    intro t
    refine MvPolynomial.induction_on (motive := fun t => t ∈ AC) t ?_ ?_ ?_
    · intro a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact hCAC f
    · intro f g hf hg
      exact AC.add_mem hf hg
    · intro f k hf
      exact AC.mul_mem hf (hRAC _ (hXk k))
  have : Algebra.IsAlgebraic θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    ⟨fun t => (Subalgebra.mem_algebraicClosure _ _).mp (hall t)⟩
  have hT2 : trdeg ℂ θ.range + trdeg θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      trdeg ℂ (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) :=
    trdeg_add_eq ℂ θ.range
  have h0 : trdeg θ.range (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) = 0 := trdeg_eq_zero
  rw [h0, add_zero] at hT2
  have hK : trdeg (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) (MvPolynomial K (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮)) =
      (Fintype.card K : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
  rw [hK, hAtr, ← hT2, hRtr] at hT1
  have hnat : sA + Fintype.card K = sR := by exact_mod_cast hT1
  refine ⟨sA, hAdim, ?_⟩
  rw [hnat, ← hRdim]
  exact hdimR

end ChartDimLt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ChartDimLtTorus =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChangeMinimal =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChangeMinimal", "h": "module\n\nimport GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim\npublic import Mathlib.RingTheory.KrullDimension.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\npublic import Mathlib.RingTheory.KrullDimension.NonZeroDivisors\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Algebra.MvPolynomial.Eval\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

namespace BaseChangeMin

variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']

section GD

attribute [local instance] MvPolynomial.algebraMvPolynomial



end GD

theorem ringKrullDim_quotient_le_of_minimalPrimes {R : Type*} [CommRing R] (I : Ideal R)
    {N : WithBot ℕ∞} (h : ∀ Z ∈ I.minimalPrimes, ringKrullDim (R ⧸ Z) ≤ N) :
    ringKrullDim (R ⧸ I) ≤ N := by
  apply GroundTheory.Heights₂.Heights.ComplexSets.quotient_dim_le_of_minimalPrimes <;> assumption

end BaseChangeMin

end GroundTheory.Heights₂.Heights.Targets
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChangeMinimal =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDimLt =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDimLt", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartImageNull\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ChartDimLtTorus\npublic import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.BaseChangeMinimal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.Order.CompletePartialOrder\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Algebra

noncomputable section

theorem ChartDimLt.proof : ChartDimLt.Statement := by
  intro K _ ι _ J e p hJ hdim
  have key : ∀ Z ∈ (ReciprocityTheory.AnForm.R.chartIdeal J p).minimalPrimes,
      ∃ s : ℕ, ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Z) = s ∧ s < e := by
    intro Z hZ
    have : Z.IsPrime := hZ.1.1
    obtain ⟨s, hs, hle⟩ := ChartDimLt.exists_dim_add_card_le hJ p Z hZ.1.2
    have hlt : ((s + Fintype.card K : ℕ) : WithBot ℕ∞) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) :=
      lt_of_le_of_lt hle hdim
    have hlt' : s + Fintype.card K < e + Fintype.card K := by exact_mod_cast hlt
    exact ⟨s, hs, by omega⟩
  cases e with
  | zero =>
    refine lt_of_le_of_lt
      (Targets.BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes (N := ⊥) _ fun Z hZ => ?_)
      (WithBot.bot_lt_coe _)
    obtain ⟨s, -, hs⟩ := key Z hZ
    omega
  | succ n =>
    have hn : ((n : ℕ) : WithBot ℕ∞) < ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast Nat.lt_succ_self n
    refine lt_of_le_of_lt
      (Targets.BaseChangeMin.ringKrullDim_quotient_le_of_minimalPrimes (N := ((n : ℕ) : WithBot ℕ∞)) _
        fun Z hZ => ?_) hn
    obtain ⟨s, hs, hsn⟩ := key Z hZ
    rw [hs]
    exact_mod_cast (by omega : s ≤ n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDimLt =====
