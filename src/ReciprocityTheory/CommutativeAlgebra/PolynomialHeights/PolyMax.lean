module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Jacobson.Ring

@[expose] public section

namespace ReciprocityTheory.CA

open Polynomial IsLocalRing

variable {P : Type*} [CommRing P] [IsLocalRing P]

theorem isIntegral_quotient_of_isMaximal_of_comap_eq {S : Type*} [CommRing S] [Algebra P S]
    [Algebra.FiniteType P S] (𝔑 : Ideal S) [𝔑.IsMaximal]
    (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) : Algebra.IsIntegral P (S ⧸ 𝔑) := by
  classical
  letI : Field (P ⧸ maximalIdeal P) := Ideal.Quotient.field _
  letI : Field (S ⧸ 𝔑) := Ideal.Quotient.field _
  letI : Algebra (P ⧸ maximalIdeal P) (S ⧸ 𝔑) :=
    (Ideal.quotientMap 𝔑 (algebraMap P S) h.ge).toAlgebra
  haveI : IsScalarTower P (P ⧸ maximalIdeal P) (S ⧸ 𝔑) := by
    first
    | exact IsScalarTower.of_algebraMap_eq (fun p => rfl)
  haveI : Algebra.FiniteType P (S ⧸ 𝔑) := by
    first
    | infer_instance
  haveI : Algebra.FiniteType (P ⧸ maximalIdeal P) (S ⧸ 𝔑) :=
    Algebra.FiniteType.of_restrictScalars_finiteType P _ _
  haveI : Module.Finite (P ⧸ maximalIdeal P) (S ⧸ 𝔑) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  haveI : Algebra.IsIntegral P (P ⧸ maximalIdeal P) := by
    first
    | infer_instance
  exact Algebra.IsIntegral.trans (P ⧸ maximalIdeal P)

theorem isMaximal_comap_of_isMaximal_of_comap_eq {S' S : Type*} [CommRing S'] [CommRing S]
    [Algebra P S'] [Algebra P S] [Algebra S' S] [IsScalarTower P S' S] [Algebra.FiniteType P S]
    (𝔑 : Ideal S) [𝔑.IsMaximal] (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) :
    (𝔑.comap (algebraMap S' S)).IsMaximal := by
  haveI := isIntegral_quotient_of_isMaximal_of_comap_eq 𝔑 h
  haveI : Algebra.IsIntegral S' (S ⧸ 𝔑) := by
    first
    | exact Algebra.IsIntegral.tower_top P
  letI : Field (S ⧸ 𝔑) := Ideal.Quotient.field _
  have hbot := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := S') (⊥ : Ideal (S ⧸ 𝔑))
  have heq : (⊥ : Ideal (S ⧸ 𝔑)).comap (algebraMap S' (S ⧸ 𝔑)) = 𝔑.comap (algebraMap S' S) := by
    ext y
    rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_comap]
    first
    | exact Ideal.Quotient.eq_zero_iff_mem
  rw [← heq]
  exact hbot

theorem exists_monic_aeval_mem_of_isMaximal {S : Type*} [CommRing S] [Algebra P S]
    [Algebra.FiniteType P S] (𝔑 : Ideal S) [𝔑.IsMaximal]
    (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) (x : S) :
    ∃ g : P[X], g.Monic ∧ aeval x g ∈ 𝔑 := by
  haveI := isIntegral_quotient_of_isMaximal_of_comap_eq 𝔑 h
  obtain ⟨g, hg, hgx⟩ := Algebra.IsIntegral.isIntegral (R := P) (Ideal.Quotient.mk 𝔑 x)
  refine ⟨g, hg, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have key : Ideal.Quotient.mk 𝔑 (aeval x g) = aeval (Ideal.Quotient.mk 𝔑 x) g := by
    first
    | exact (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ P 𝔑) x g).symm
  rw [key, Polynomial.aeval_def]
  exact hgx

end ReciprocityTheory.CA
