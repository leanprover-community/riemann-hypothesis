import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

open Module in

theorem comap_map_eq_of_isUnit_finrank : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [CommRing V'] [IsDomain V'] [Algebra V V'] [Module.Finite V V'], Function.Injective (algebraMap V V') → IsUnit ((Module.finrank V V' : ℕ) : V) → ∀ I : Ideal V, (I.map (algebraMap V V')).comap (algebraMap V V') = I := by
  intro V V' _ _ _ _ _ _ _ hinj hunit I
  refine le_antisymm ?_ Ideal.le_comap_map
  let K := FractionRing V
  let L := FractionRing V'
  have hinjL : Function.Injective (algebraMap V L) := by
    rw [IsScalarTower.algebraMap_eq V V' L]
    exact (IsFractionRing.injective V' L).comp hinj
  haveI : FaithfulSMul V L := (faithfulSMul_iff_algebraMap_injective V L).mpr hinjL
  letI : Algebra K L := FractionRing.liftAlgebra V L
  haveI : IsScalarTower V K L := FractionRing.isScalarTower_liftAlgebra V L
  have hrank : finrank K L = finrank V V' := IsFractionRing.finrank_eq V K V' L
  have hn0 : finrank K L ≠ 0 := by
    intro h
    rw [← hrank, h, Nat.cast_zero] at hunit
    exact not_isUnit_zero hunit
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hn0)
  haveI : Module.Free K L := Module.Free.of_divisionRing K L
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'

  have htrV : ∀ z : V', ∃ t : V, algebraMap V K t = Algebra.trace K L (algebraMap V' L z) := by
    intro z
    have hz : IsIntegral V (algebraMap V' L z) :=
      (Algebra.IsIntegral.isIntegral (R := V) z).map (IsScalarTower.toAlgHom V V' L)
    exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace hz)
  have hmul : ∀ (i : V) (w : L), Algebra.trace K L (algebraMap V L i * w) =
      algebraMap V K i * Algebra.trace K L w := by
    intro i w
    rw [IsScalarTower.algebraMap_apply V K L, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have key : ∀ y ∈ I.map (algebraMap V V'), ∀ z : V', ∃ c ∈ I,
      algebraMap V K c = Algebra.trace K L (algebraMap V' L (z * y)) := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, hi, rfl⟩ z
      obtain ⟨t, ht⟩ := htrV z
      refine ⟨i * t, I.mul_mem_right t hi, ?_⟩
      rw [map_mul, ht, mul_comm z, map_mul, ← IsScalarTower.algebraMap_apply V V' L, hmul]
    · intro z
      exact ⟨0, I.zero_mem, by simp⟩
    · intro x y _ _ hx hy z
      obtain ⟨c, hc, hcx⟩ := hx z
      obtain ⟨d, hd, hdy⟩ := hy z
      exact ⟨c + d, I.add_mem hc hd, by rw [map_add, hcx, hdy, mul_add, map_add, map_add]⟩
    · intro w x _ hx z
      obtain ⟨c, hc, hcx⟩ := hx (z * w)
      exact ⟨c, hc, by rw [hcx, smul_eq_mul, _root_.mul_assoc]⟩
  intro a ha
  obtain ⟨c, hc, hca⟩ := key _ ha 1
  rw [_root_.one_mul, ← IsScalarTower.algebraMap_apply V V' L, IsScalarTower.algebraMap_apply V K L,
    Algebra.trace_algebraMap, hrank, nsmul_eq_mul, ← map_natCast (algebraMap V K), ← map_mul] at hca
  have hc' : c = (finrank V V' : V) * a := IsFractionRing.injective V K hca
  obtain ⟨u, hu⟩ := hunit
  have : a = ↑u⁻¹ * c := by rw [hc', ← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  rw [this]
  exact I.mul_mem_left _ hc

end GlobalTheory.Poinc.Sep
end

section
open IsLocalRing

namespace GlobalTheory.LocExt

theorem exists_isCN_integralClosure_of_isUnit_finrank : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.TorRef.IsCN V → ∀ (K' : Type) [Field K'] [Algebra (FractionRing V) K'] [FiniteDimensional (FractionRing V) K'], IsUnit ((Module.finrank (FractionRing V) K' : ℕ) : V) → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (j : V' →+* K'), GlobalTheory.TorRef.IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ Function.Injective j ∧ j.comp io = (algebraMap (FractionRing V) K').comp (algebraMap V (FractionRing V)) ∧ ∀ x : K', (∃ P : Polynomial V, P.Monic ∧ P.eval₂ ((algebraMap (FractionRing V) K').comp (algebraMap V (FractionRing V))) x = 0) → ∃ y, j y = x := by
  intro V _ _ _ hV K' _ _ _ hunit
  obtain ⟨hnoeth, hnorm, hcomp, hchar⟩ := hV
  let K := FractionRing V
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  letI : Algebra V K' := ((algebraMap K K').comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let W := integralClosure V K'
  haveI hWf : Module.Finite V W := IsIntegralClosure.finite V K K' W
  haveI : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := V) W
  have hVL : Function.Injective (algebraMap V K') :=
    (algebraMap K K').injective.comp (IsFractionRing.injective V K)
  have hinjW : Function.Injective (algebraMap V W) := fun x y h => hVL (congrArg Subtype.val h)
  haveI : CharZero W := charZero_of_injective_algebraMap hinjW
  have h1 : (maximalIdeal W).comap (algebraMap V W) = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal W))
  have hlocW : IsLocalHom (algebraMap V W) := ((local_hom_TFAE _).out 0 4).2 h1
  haveI : IsFractionRing W K' := IsIntegralClosure.isFractionRing_of_finite_extension V K K' W
  have hrank : Module.finrank V W = Module.finrank K K' := (IsFractionRing.finrank_eq V K W K').symm
  have hunit' : IsUnit ((Module.finrank V W : ℕ) : V) := by rw [hrank]; exact hunit
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, (integralClosure V K').val.toRingHom,
    ⟨IsNoetherianRing.of_finite V W, integralClosure.isIntegrallyClosedOfFiniteExtension K,
      CompleteFiniteExtension.isAdicComplete_of_finite_local V W, inferInstance⟩, hinjW,
    RingHom.finite_algebraMap.2 hWf, hlocW,
    GlobalTheory.Poinc.Sep.comap_map_eq_of_isUnit_finrank V W hinjW hunit',
    Subtype.val_injective, RingHom.ext fun _ => rfl, ?_⟩
  rintro x ⟨P, hmon, hP⟩
  exact ⟨⟨x, P, hmon, hP⟩, rfl⟩

end GlobalTheory.LocExt
end
