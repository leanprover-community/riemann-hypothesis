module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteIntegralClosureOfIsIntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmoothOfIsDedekindDomain
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CurveNorm

theorem exists_lift_of_isIntegral {k E E' : Type} [Field k] [IsAlgClosed k] [CommRing E]
    [CommRing E'] [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']
    [Algebra.IsIntegral E E'] (hinj : Function.Injective (algebraMap E E')) (e : E →ₐ[k] k) :
    ∃ e' : E' →ₐ[k] k, e'.comp (IsScalarTower.toAlgHom k E E') = e := by
  have hsurj : Function.Surjective e := fun c => ⟨algebraMap k E c, by simp⟩
  haveI hp : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := E')
    (RingHom.ker e) ⊥ (by
      intro x hx
      have : x = 0 := hinj (by simpa using hx)
      simp [this])
  have key : ∀ x : E, algebraMap k (E' ⧸ Q) (e x) = Ideal.Quotient.mk Q (algebraMap E E' x) := by
    intro x
    have h1 : algebraMap k E (e x) - x ∈ RingHom.ker e := by simp [RingHom.mem_ker]
    rw [← hQc, Ideal.mem_comap, map_sub, ← Ideal.Quotient.eq, ← IsScalarTower.algebraMap_apply] at h1
    exact h1
  haveI : Algebra.IsIntegral k (E' ⧸ Q) := by
    constructor
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpm, hp0⟩ := Algebra.IsIntegral.isIntegral (R := E) y
    refine ⟨p.map (e : E →+* k), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap k (E' ⧸ Q)).comp (e : E →+* k)
        = (Ideal.Quotient.mk Q).comp (algebraMap E E') := RingHom.ext key
    rw [this, ← Polynomial.hom_eval₂, hp0, map_zero]
  have hbij : Function.Bijective (algebraMap k (E' ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ : k ≃ₐ[k] (E' ⧸ Q) := AlgEquiv.ofBijective (Algebra.ofId k _) hbij
  refine ⟨(φ.symm : (E' ⧸ Q) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k Q), ?_⟩
  ext x
  apply φ.injective
  exact (φ.apply_symm_apply _).trans (key x).symm

theorem exists_smooth_normalisation (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E]
    [Algebra.FiniteType ℂ E] [Ring.DimensionLEOne E] (e : E →ₐ[ℂ] ℂ) :
    ∃ (E' : Type) (_ : CommRing E') (_ : IsDomain E') (_ : Algebra ℂ E') (ρ : E →ₐ[ℂ] E')
      (e' : E' →ₐ[ℂ] ℂ), Algebra.Smooth ℂ E' ∧ Function.Injective ρ ∧ e'.comp ρ = e := by
  let F := FractionRing E
  let E' : Type := integralClosure E F
  haveI : Module.Finite E E' := GlobalTheory.NormFin.finite_integralClosure_of_isAlgClosed ℂ E F
  letI : Algebra ℂ E' := ((algebraMap E E').comp (algebraMap ℂ E)).toAlgebra
  haveI : IsScalarTower ℂ E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType ℂ E' := Algebra.FiniteType.trans (S := E) inferInstance inferInstance
  haveI : IsNoetherianRing E' := Algebra.FiniteType.isNoetherianRing ℂ E'
  haveI : Ring.DimensionLEOne E' := Ring.DimensionLEOne.integralClosure E F
  haveI : IsIntegrallyClosed E' := integralClosure.isIntegrallyClosedOfFiniteExtension F
  haveI : IsDedekindRing E' := ⟨⟩
  haveI : IsDedekindDomain E' := inferInstance
  have hinj : Function.Injective (algebraMap E E') := by
    intro x y h
    apply IsFractionRing.injective E F
    exact congrArg Subtype.val h
  obtain ⟨e', he'⟩ := exists_lift_of_isIntegral hinj e
  exact ⟨E', inferInstance, inferInstance, inferInstance, IsScalarTower.toAlgHom ℂ E E', e',
    GlobalTheory.DedekindSmooth.smooth_of_isDedekindDomain ℂ E', hinj, he'⟩

end GlobalTheory.CurveNorm
