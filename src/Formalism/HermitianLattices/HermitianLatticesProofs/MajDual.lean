import Mathlib
import Formalism.HermitianLattices.HermitianLatticesProofs.MajLattice

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLatticesTheory


section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]




lemma majDual_jW_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) p :
    jW h b X w p = sgnAt h b X p.1 p.2.1 * w p := rfl


end

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]



end

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

lemma majDual_star_int (r : RingOfIntegers K) : IsIntegral ℤ (star (r : K)) := by
  exact (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom


abbrev majDualI (K : Type) [Field K] [NumberField K] :
    FractionalIdeal (RingOfIntegers K)⁰ K :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (RingOfIntegers K)⁰ K)


end

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]



end

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]



def majDualJ (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) :
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) where
  toFun := jW h b X
  map_add' := by
    intro u w; ext p; simp only [majDual_jW_apply, PiLp.add_apply]; ring
  map_smul' := by
    intro c u; ext p; simp only [majDual_jW_apply, PiLp.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring



variable [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]


end


end Formalism.HermitianLatticesTheory
