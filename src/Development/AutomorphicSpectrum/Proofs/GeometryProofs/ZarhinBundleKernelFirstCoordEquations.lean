module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ar

namespace ProjCoord

section OpenImm

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]

def push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (p : Cpt η) : Cpt (η ≫ f) :=
  ⟨f p.1, p.2.map f.continuous⟩

theorem genMap_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (p : Cpt η) :
    genMap (η ≫ f) (push η f p) = (genMap η p).comp (f.stalkMap p.1).hom := by
  have h1 := Scheme.stalkClosedPointTo_comp η f
  have h2 := Scheme.Hom.stalkSpecializes_stalkMap f _ _ p.2
  have h3 : X.presheaf.stalkSpecializes (push η f p).2 ≫ Scheme.stalkClosedPointTo (η ≫ f) =
      f.stalkMap p.1 ≫ (Y.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo η) :=
    (congrArg (X.presheaf.stalkSpecializes (push η f p).2 ≫ ·) h1).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Scheme.stalkClosedPointTo η) h2).trans
        (Category.assoc _ _ _)))
  exact congrArg (fun g => g.hom) h3

theorem regAt_push (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f] (p : Cpt η) :
    regAt (η ≫ f) (push η f p) = regAt η p := by
  have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
  unfold regAt
  rw [genMap_push]
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := hb.2 s
    exact ⟨t, rfl⟩

theorem genMap_push_injective (η : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f]
    (p : Cpt η) (h : Function.Injective (genMap η p)) :
    Function.Injective (genMap (η ≫ f) (push η f p)) := by
  have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
  rw [genMap_push]
  exact h.comp hb.1

end OpenImm

section Chart

variable {X : Scheme.{0}} {Ω A : Type} [Field Ω] [CommRing A]

end Chart

section Away

open HomogeneousLocalization

variable {σ A Ω : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [Field Ω]

end Away

section Poly

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem aeval_mul_of_isHomogeneous {B : Type} [CommRing B] [Algebra o B] (x : κ → B) (t : B)
    {g : MvPolynomial κ o} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun j => t * x j) g = t ^ n * aeval x g := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h : ∑ i ∈ d.support, d i = n := by
    have := hg (mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
  ring

end Poly

end ProjCoord

attribute [local instance] MvPolynomial.gradedAlgebra

end GlobalTheory.CompanionTheory.Ar
