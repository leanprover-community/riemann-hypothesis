module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDvrConeDimTrdeg
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimGe
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace DvrConeDimTrdeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem proof : Statement := by
  intro O _ _ _ K _ _ ι _ P hP hPC
  classical
  let F := FractionRing O
  have hPp : P.IsPrime := hP.isPrime
  have hG : (genFib P).IsPrime := (GenericFibProps.full.{0} O K ι P hP hPC).1
  have hdim : ringKrullDim (MRing ι O ⧸ P) = ringKrullDim (MRing ι F ⧸ genFib P) + 1 :=
    le_antisymm (GenericDimGe.proof.{0} O K ι P hPp hPC) (GenericDimBound.full.{0} O K ι P hP hPC)

  have hB : ringKrullDim (MRing ι F ⧸ genFib P) =
      (Algebra.trdeg F (MRing ι F ⧸ genFib P)).toENat :=
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F

  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C : O →+* MRing ι O)
  have : IsLocalization M (MRing ι F) := MvPolynomial.isLocalization (nonZeroDivisors O) F
  have hdisj : Disjoint (M : Set (MRing ι O)) (P : Set (MRing ι O)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hPC] at this
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 this)
  have hcomap : (genFib P).comap (algebraMap (MRing ι O) (MRing ι F)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι F) hPp hdisj
  let φ : (MRing ι O ⧸ P) →+* (MRing ι F ⧸ genFib P) :=
    Ideal.quotientMap (genFib P) (algebraMap (MRing ι O) (MRing ι F)) hcomap.ge
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' hcomap.le
  let _ : Algebra (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) := φ.toAlgebra
  have : IsScalarTower O (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change _ = φ (Ideal.Quotient.mk P (C a))
      simp [φ, Ideal.quotientMap_mk]
      rfl
  have : FaithfulSMul (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : FaithfulSMul O (MRing ι O ⧸ P) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 ((injective_iff_map_eq_zero (algebraMap O (MRing ι O ⧸ P))).2 fun a ha => ?_)
    have h : (C a : MRing ι O) ∈ P :=
      Ideal.Quotient.eq_zero_iff_mem.1 (show Ideal.Quotient.mk P (C a) = 0 from ha)
    have : a ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hPC] at this
    exact (Submodule.mem_bot _).1 this
  have : FaithfulSMul O F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective O F)
  have : FaithfulSMul F (MRing ι F ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective F (MRing ι F ⧸ genFib P)).2 (algebraMap F _).injective
  have : Algebra.IsAlgebraic O F := IsLocalization.isAlgebraic F (nonZeroDivisors O)
  have : Algebra.IsAlgebraic (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) := by
    refine ⟨fun b => ?_⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective M g
    have hspec := IsLocalization.mk'_spec (MRing ι F) s m
    let y := algebraMap (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) (Ideal.Quotient.mk P (m : MRing ι O))
    have hy0 : y ≠ 0 := by
      refine (map_ne_zero_iff _ hφ).2 fun h => ?_
      exact Set.disjoint_left.1 hdisj m.2 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hy0) (isAlgebraic_algebraMap _) ?_
    have : y * Ideal.Quotient.mk (genFib P) (IsLocalization.mk' (MRing ι F) s m) =
        algebraMap (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) (Ideal.Quotient.mk P s) := by
      change φ _ * _ = φ _
      simp only [φ, Ideal.quotientMap_mk, ← map_mul]
      rw [mul_comm, hspec]
    rw [this]
    exact isAlgebraic_algebraMap _
  have h1 := trdeg_add_eq O F (A := MRing ι F ⧸ genFib P)
  have h2 := trdeg_add_eq O (MRing ι O ⧸ P) (A := MRing ι F ⧸ genFib P)
  rw [trdeg_eq_zero (R := O) (A := F), zero_add] at h1
  rw [trdeg_eq_zero (R := MRing ι O ⧸ P) (A := MRing ι F ⧸ genFib P), add_zero] at h2
  rw [hdim, hB, h1, ← h2]
  rfl

end DvrConeDimTrdeg

end

end GroundTheory.Heights₂.Heights.NumbersDVR
