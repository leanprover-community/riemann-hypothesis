module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.abField :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : AbF) (L : Type) [Field L] [NumberField L] [Algebra L Ω], IsAbField A L → galOf ℚ L Ω = abU Ω A := by
  intro Ω _ _ _ A L _ _ _ hL
  obtain ⟨N, hN, j, ζ, hm, hζ, hj⟩ := hL
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Normal ℚ (CyclotomicField N ℚ) := by
    haveI : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.2 (NeZero.ne N)⟩
    have h := CyclotomicField.isCyclotomicExtension (n := N) (K := ℚ)
    have h2 := (@IsCyclotomicExtension.isGalois _ _ _ _ _ _ h).to_normal
    convert h2
    exact Subsingleton.elim _ _
  let k : CyclotomicField N ℚ →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra (CyclotomicField N ℚ) Ω := k.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField N ℚ) Ω :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsScalarTower ℚ L Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have key : ∀ σ : G ℚ Ω, (∀ x : L, σ (k (j x)) = k (j x)) ↔ galChar Ω A.m σ ∈ A.H := by
    intro σ
    let τ := σ.restrictNormal (CyclotomicField N ℚ)
    have hτ : ∀ y, k (τ y) = σ (k y) := fun y => σ.restrictNormal_commutes (CyclotomicField N ℚ) y
    have hkζ : IsPrimitiveRoot (k ζ) N := hζ.map_of_injective k.injective
    have hσζ : σ (k ζ) = k ζ ^ (galChar Ω N σ : ZMod N).val :=
      galChar_spec N σ (k ζ) hkζ.pow_eq_one
    have hτζ : τ ζ = ζ ^ (galChar Ω N σ : ZMod N).val := by
      apply k.injective
      show k (τ ζ) = k (ζ ^ _)
      rw [hτ, hσζ, map_pow]
    have h1 := hj τ _ hτζ
    have hfix : (∀ x : L, τ (j x) = j x) ↔ (∀ x : L, σ (k (j x)) = k (j x)) :=
      forall_congr' fun x => by rw [← hτ]; exact k.injective.eq_iff.symm
    rw [← hfix, h1]
    obtain ⟨d, hd⟩ := hm
    have hprim : IsPrimitiveRoot (k ζ ^ d) A.m :=
      hkζ.pow (Nat.pos_of_ne_zero (NeZero.ne N)) (hd.trans (mul_comm _ _))
    have e1 := galChar_spec A.m σ (k ζ ^ d) hprim.pow_eq_one
    rw [map_pow, hσζ, ← pow_mul, mul_comm _ d, pow_mul] at e1
    have hfin : IsOfFinOrder (k ζ ^ d) := isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hprim.pow_eq_one⟩
    have hmod : (galChar Ω N σ : ZMod N).val ≡ (galChar Ω A.m σ : ZMod A.m).val [MOD A.m] := by
      have h2 := hfin.pow_eq_pow_iff_modEq.1 e1
      rwa [← hprim.eq_orderOf] at h2
    have hcast : (((galChar Ω N σ : ZMod N).val : ℕ) : ZMod A.m) = (galChar Ω A.m σ : ZMod A.m) := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hmod, ZMod.natCast_zmod_val]
    constructor
    · rintro ⟨u, hu, hua⟩
      have hu' : u = galChar Ω A.m σ := Units.ext (hua.trans hcast)
      exact hu' ▸ hu
    · intro h
      exact ⟨_, h, hcast.symm⟩
  let σ₀ : Ω →ₐ[ℚ] Ω := j.liftNormal Ω
  have hσ₀ : ∀ x : L, σ₀ (algebraMap L Ω x) = k (j x) := fun x => j.liftNormal_commutes Ω x
  let e : Ω ≃ₐ[ℚ] Ω := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  have he : ∀ x : L, e (algebraMap L Ω x) = k (j x) := hσ₀
  have hconj : ∀ σ : G ℚ Ω, galChar Ω A.m (e * σ * e⁻¹) = galChar Ω A.m σ := by
    intro σ
    rw [map_mul, map_mul, map_inv, mul_comm (galChar Ω A.m e), mul_assoc, mul_inv_cancel, mul_one]
  ext σ
  change (∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x) ↔ galChar Ω A.m σ ∈ A.H
  rw [← hconj σ, ← key]
  refine forall_congr' fun x => ?_
  rw [← he, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply,
    e.injective.eq_iff]
