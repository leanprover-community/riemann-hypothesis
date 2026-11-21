import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalLocalCoverOfFiniteHomStatement

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqRoots

open Polynomial

theorem exists_sqrt_one (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (b : R)
    (h : IsCN R) : ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R')
      (ρ : R →+* R') (s : R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧
      s ^ 2 = ρ b := by
  set g : R[X] := X ^ 2 - C b with hg_def
  have hg : g.Monic := monic_X_pow_sub_C b two_ne_zero
  have hdeg : g.natDegree = 2 := natDegree_X_pow_sub_C
  have hinj : Function.Injective (AdjoinRoot.of g) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hne
    have hdvd : g ∣ C r := by
      rw [AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at hr
      exact hr
    refine hg.not_dvd_of_natDegree_lt (C_ne_zero.mpr hne) ?_ hdvd
    rw [natDegree_C, hdeg]; norm_num
  have hfin : (AdjoinRoot.of g).Finite := by
    have := RingHom.finite_algebraMap.mpr hg.finite_adjoinRoot
    rwa [AdjoinRoot.algebraMap_eq] at this
  obtain ⟨R', _, _, _, ρ, σ, hC, hi, hf, hl, hσ⟩ :=
    GlobalTheory.T.exists_complete_normal_local_cover_of_finite_hom R (AdjoinRoot g) (AdjoinRoot.of g) h hinj hfin
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, σ (AdjoinRoot.root g), hC, hi, hf, hl, ?_⟩
  have hroot : AdjoinRoot.root g ^ 2 = AdjoinRoot.of g b := by
    have h0 : AdjoinRoot.mk g g = 0 := AdjoinRoot.mk_self
    rw [hg_def, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
    exact h0
  rw [← map_pow, hroot, ← RingHom.comp_apply, hσ]

theorem exists_sqrt_fin : ∀ (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (a : Fin n → R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R')
      (ρ : R →+* R') (r : Fin n → R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧
      ∀ i, r i ^ 2 = ρ (a i) := by
  intro n
  induction n with
  | zero =>
    intro R _ _ _ a h
    exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, Fin.elim0, h,
      Function.injective_id, RingHom.Finite.id R, inferInstance, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro R _ _ _ a h
    obtain ⟨R₁, _, _, _, ρ₁, r₁, hC₁, hi₁, hf₁, hl₁, hr₁⟩ := ih R (fun i => a i.castSucc) h
    obtain ⟨R₂, _, _, _, ρ₂, s, hC₂, hi₂, hf₂, hl₂, hs⟩ :=
      exists_sqrt_one R₁ (ρ₁ (a (Fin.last n))) hC₁
    refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ₂.comp ρ₁,
      Fin.lastCases s (fun i => ρ₂ (r₁ i)), hC₂, hi₂.comp hi₁, hf₂.comp hf₁, ?_, ?_⟩
    · haveI := hl₁; haveI := hl₂; infer_instance
    · intro i
      induction i using Fin.lastCases with
      | last => beta_reduce; rw [Fin.lastCases_last, hs, RingHom.comp_apply]
      | cast i => beta_reduce; rw [Fin.lastCases_castSucc, ← map_pow, hr₁, RingHom.comp_apply]

end GlobalTheory.SqRoots

theorem GlobalTheory.sqrt_of_finite_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Type) [Finite I] (a : I → R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : I → R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ i, r i ^ 2 = ρ (a i) := by
  intro R _ _ _ I _ a h
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  obtain ⟨R', _, _, _, ρ, r, hC, hi, hf, hl, hr⟩ := GlobalTheory.SqRoots.exists_sqrt_fin n R (a ∘ e.symm) h
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, r ∘ e, hC, hi, hf, hl, fun i => ?_⟩
  simpa using hr (e i)
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_completeNormal_ext_sqrt_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Type) [Finite I] (a : I → R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : I → R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ i, r i ^ 2 = ρ (a i) := by
  atlas_forward_decl GlobalTheory.sqrt_of_finite_family
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootHom

theorem exists_sqrt_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h : X → (FractionRing R)ˣ) (m : ℕ) (t : Fin m → R), IsCN R → (∀ a b, h (a + b) = h a * h b) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (gam : FractionRing R →+* FractionRing R') (r : Fin m → R') (eta : X → (FractionRing R')ˣ), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x)) ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ (∀ a b, eta (a + b) = eta a * eta b) ∧ ∀ a, eta a ^ 2 = Units.map gam.toMonoidHom (h a) := by
  intro R _ _ _ X _ _ _ h m t hR hh
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hpq : ∀ k, ∃ p q : R, q ∈ nonZeroDivisors R ∧
      algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q = (h (b k) : FractionRing R) :=
    fun k => IsFractionRing.div_surjective R _
  choose p q hq hpq using hpq
  obtain ⟨R', _, _, _, ρ, r, hR', hinj, hfin, hloc, hr⟩ :=
    GlobalTheory.T.exists_finite_completeNormal_ext_sqrt_family R (Fin m ⊕ Module.Free.ChooseBasisIndex ℤ X) (Sum.elim t (fun k => p k * q k)) hR
  have hι : Function.Injective (algebraMap R' (FractionRing R')) := IsFractionRing.injective R' (FractionRing R')
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) := hι.comp hinj
  let gam : FractionRing R →+* FractionRing R' := IsFractionRing.lift hinj'
  have hgam : ∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x) := fun x => IsFractionRing.lift_algebraMap hinj' x
  have hq0 : ∀ k, algebraMap R' (FractionRing R') (ρ (q k)) ≠ 0 := by
    intro k h0
    have : ρ (q k) = 0 := hι (by simpa using h0)
    exact nonZeroDivisors.ne_zero (hq k) (hinj (by simpa using this))
  have hp0 : ∀ k, p k ≠ 0 := by
    intro k h0
    have := hpq k
    rw [h0, map_zero, zero_div] at this
    exact (h (b k)).ne_zero this.symm
  have hs : ∀ k, (r (Sum.inr k)) ^ 2 = ρ (p k * q k) := fun k => by simpa using hr (Sum.inr k)
  have hs0 : ∀ k, algebraMap R' (FractionRing R') (r (Sum.inr k)) ≠ 0 := by
    intro k h0
    have h1 : r (Sum.inr k) = 0 := hι (by simpa using h0)
    have h2 := hs k
    rw [h1, zero_pow two_ne_zero] at h2
    exact mul_ne_zero (hp0 k) (nonZeroDivisors.ne_zero (hq k)) (hinj (by simpa using h2.symm))
  let e : Module.Free.ChooseBasisIndex ℤ X → (FractionRing R')ˣ := fun k =>
    Units.mk0 (algebraMap R' _ (r (Sum.inr k)) / algebraMap R' _ (ρ (q k))) (div_ne_zero (hs0 k) (hq0 k))
  let L : X →ₗ[ℤ] Additive (FractionRing R')ˣ := b.constr ℤ (fun k => Additive.ofMul (e k))
  let H : X →+ Additive (FractionRing R)ˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (h a)) (fun a c => by
    simp [hh a c])
  let G : X →+ Additive (FractionRing R')ˣ := (MonoidHom.toAdditive (Units.map gam.toMonoidHom)).comp H
  have hLG : L + L = G.toIntLinearMap := by
    refine b.ext fun k => ?_
    simp only [LinearMap.add_apply, L, Module.Basis.constr_basis, AddMonoidHom.coe_toIntLinearMap, G, H,
      AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.mk'_apply, MonoidHom.toAdditive_apply_apply]
    rw [← ofMul_mul]
    congr 1
    ext
    simp only [Units.val_mul, e, Units.val_mk0, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, toMul_ofMul]
    rw [← hpq k, map_div₀, hgam, hgam, div_mul_div_comm, div_eq_div_iff (mul_ne_zero (hq0 k) (hq0 k)) (hq0 k)]
    have := congrArg (algebraMap R' (FractionRing R')) (hs k)
    rw [map_pow, map_mul, map_mul] at this
    rw [← sq, this]
    ring
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, gam, fun i => r (Sum.inl i), fun a => Additive.toMul (L a),
    hR', hinj, hfin, hloc, hgam, fun i => by simpa using hr (Sum.inl i), fun a c => by simp [map_add], fun a => ?_⟩
  have h2 : Additive.toMul (L a + L a) = Units.map gam.toMonoidHom (h a) := by
    rw [← LinearMap.add_apply, LinearMap.congr_fun hLG a]
    rfl
  rw [sq, ← toMul_add]
  exact h2

end GlobalTheory.RootHom
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqrt_latticeHom_finiteExtension_complete : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h : X → (FractionRing R)ˣ) (m : ℕ) (t : Fin m → R), IsCN R → (∀ a b, h (a + b) = h a * h b) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (gam : FractionRing R →+* FractionRing R') (r : Fin m → R') (eta : X → (FractionRing R')ˣ), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x)) ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ (∀ a b, eta (a + b) = eta a * eta b) ∧ ∀ a, eta a ^ 2 = Units.map gam.toMonoidHom (h a) := by
  atlas_forward_decl GlobalTheory.RootHom.exists_sqrt_hom
end
