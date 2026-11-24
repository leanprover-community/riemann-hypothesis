module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange
public import Mathlib.RingTheory.Flat.Basic
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module
open TensorProduct

namespace GlobalTheory

namespace GenericFreeness

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem IsBasisAway.exists_basis_apply_eq {a : R} {s : Set M}
    (h : IsBasisAway a (⊥ : Submodule R M) ⊤ s) :
    ∃ b : Module.Basis s (Localization.Away a) (Localization.Away a ⊗[R] M),
      ∀ x : s, b x = 1 ⊗ₜ (x : M) := by
  let f := TensorProduct.mk R (Localization.Away a) M 1
  refine ⟨Module.Basis.mk (v := f ∘ fun x : s => (x : M))
    (LinearIndependent.of_isLocalizedModule (Localization.Away a) (.powers a) f h.linearIndepOn)
    ?_, fun x => Module.Basis.mk_apply _ _ x⟩
  intro y _
  induction y with
  | add y z hy hz => exact Submodule.add_mem _ (hy trivial) (hz trivial)
  | tmul c m =>
    obtain ⟨n, hn⟩ := h.2.2 m trivial
    rw [bot_sup_eq] at hn
    have h1 := Submodule.mem_map_of_mem (f := f) hn
    rw [Submodule.map_span] at h1
    have h2 := Submodule.span_subset_span R (Localization.Away a) _ h1
    obtain ⟨u, hu⟩ :=
      ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).pow n).exists_left_inv
    have e : c ⊗ₜ[R] m = (c * u) • f (a ^ n • m) := by
      simp only [f, TensorProduct.mk_apply, ← smul_tmul, smul_tmul', smul_eq_mul,
        Algebra.smul_def, map_pow, mul_one, mul_assoc, hu]
    rw [e, Set.range_comp, Subtype.range_coe]
    exact Submodule.smul_mem _ _ h2

theorem IsBasisAway.one_tmul_ne_zero {a : R} {s : Set M}
    (h : IsBasisAway a (⊥ : Submodule R M) ⊤ s) (K : Type*) [CommRing K] [Nontrivial K]
    [Algebra R K] (ha : IsUnit (algebraMap R K a)) {x : M} (hx : x ∈ s) :
    (1 : K) ⊗ₜ[R] x ≠ 0 := by
  obtain ⟨b, hb⟩ := h.exists_basis_apply_eq
  letI : Algebra (Localization.Away a) K := (IsLocalization.Away.lift a ha).toAlgebra
  haveI : IsScalarTower R (Localization.Away a) K :=
    .of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq a ha r).symm
  have := ((b.baseChange K).map (AlgebraTensorModule.cancelBaseChange R _ K K M)).ne_zero ⟨x, hx⟩
  simpa [hb] using this

end GenericFreeness

open GenericFreeness

section

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {A₀ : Type*} [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
  {A : Type*} [CommRing A] [Algebra R A] (φ : A₀ →ₐ[R] A)

theorem exists_pow_smul_ker_eq_zero_of_dense {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (h : ∀ x ∈ D, Function.Injective (Algebra.TensorProduct.map
      (AlgHom.id R x.asIdeal.ResidueField) φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ y : A₀, φ y = 0 → ∃ n : ℕ, a ^ n • y = 0 := by
  haveI : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing R A₀
  let J : Ideal A₀ := RingHom.ker φ
  obtain ⟨a, ha0, ha⟩ := exists_hasBasisAway_of_finiteType (R := R) (A := A₀) J
  obtain ⟨b, hb0, hb⟩ := exists_hasBasisAway_quotient R A₀ A₀ J (IsNoetherian.noetherian J)
  have ha1 := HasBasisAway.map (a := a) (J.subtype.restrictScalars R) ⊥ (by
    have : Submodule.comap (J.subtype.restrictScalars R) ⊥ = ⊥ :=
      LinearMap.ker_eq_bot.2 Subtype.val_injective
    rwa [this])
  have e : (⊥ : Submodule R A₀) ⊔ LinearMap.range (J.subtype.restrictScalars R) =
      J.restrictScalars R := by
    rw [bot_sup_eq]
    ext x
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [e] at ha1
  obtain ⟨s, hs⟩ := ha1.of_dvd (dvd_mul_right a b)
  obtain ⟨t, ht⟩ := hb.of_dvd (dvd_mul_left b a)
  have hst := hs.union bot_le le_top ht
  have hab := mul_ne_zero ha0 hb0
  obtain ⟨x, hxD, hxa⟩ := hD.exists_mem_open (PrimeSpectrum.basicOpen (a * b)).isOpen
    ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hab⟩
  have hu : IsUnit (algebraMap R x.asIdeal.ResidueField (a * b)) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]
    exact hxa
  obtain rfl : s = ∅ := Set.eq_empty_of_forall_notMem fun y hy => by
    refine hst.one_tmul_ne_zero _ hu (Or.inl hy) (h x hxD ?_)
    have : φ y = 0 := hs.1 hy
    rw [Algebra.TensorProduct.map_tmul, this, tmul_zero, map_zero]
  refine ⟨a * b, hab, fun y hy => ?_⟩
  simpa using hs.2.2 y hy

theorem exists_baseChange_injective_of_dense.{w} {D : Set (PrimeSpectrum R)} (hD : Dense D)
    (h : ∀ x ∈ D, Function.Injective (Algebra.TensorProduct.map
      (AlgHom.id R x.asIdeal.ResidueField) φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type w) [CommRing R'] [Algebra R R'] [Module.Flat R R'],
      IsUnit (algebraMap R R' a) →
        Function.Injective (Algebra.TensorProduct.map (AlgHom.id R R') φ) := by
  obtain ⟨a, ha0, ha⟩ := exists_pow_smul_ker_eq_zero_of_dense φ hD h
  refine ⟨a, ha0, fun R' _ _ _ hu => (injective_iff_map_eq_zero _).2 fun z hz => ?_⟩
  have hex := Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map φ.toLinearMap)
  obtain ⟨w, rfl⟩ := (hex z).1 hz
  clear hz
  induction w with
  | add y z hy hz => rw [map_add (f := _), hy, hz, add_zero]
  | tmul c y =>
    obtain ⟨n, hn⟩ := ha y y.2
    obtain ⟨u, hu⟩ := (hu.pow n).exists_left_inv
    have e : c = a ^ n • (c * u) := by
      rw [Algebra.smul_def, map_pow, mul_comm, mul_assoc, hu, mul_one]
    rw [LinearMap.lTensor_tmul, e, smul_tmul, Submodule.subtype_apply, hn, tmul_zero]

end

end GlobalTheory
