import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingThetaConstantsGenerateIntegralTorsionLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointGenericFibreMemberHasLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusSpreadOverTraitSpecialisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapCommutesEndomorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionSectionOfSpreadThroughLatticeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePullbackSemiAbelianOverNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalNoetherianStalkFactorOfFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackUniformisingGroupSameGenericFib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianEndExtendingAbelianSchemeEnd

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_spread_over_trait_specialisation : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → IsIntegral B → IsLocallyNoetherian B → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → ∃ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_spread₂ | exact GlobalTheory.Poinc.Sep.Spz.exists_spread₂ | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_spread₂ <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_spread_lattice_map_surjective : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → Function.Surjective ρ := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.spread₂_surjective | exact GlobalTheory.Poinc.Sep.Spz.spread₂_surjective | (intros; apply GlobalTheory.Poinc.Sep.Spz.spread₂_surjective <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_spread_lattice_map_commutes_endomorphisms : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (Fm : H ⟶ H) (E₁ : EndU U₁.toUnifPre) (E₂ : EndU U₂.toUnifPre), E₁.aG.left ≫ β₁ = β₁ ≫ Fm.left → E₂.aG.left ≫ β₂ = β₂ ≫ Fm.left → ∀ y, ρ (E₂.h y) = E₁.h (ρ y) := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.spread₂_endU_comm | exact GlobalTheory.Poinc.Sep.Spz.spread₂_endU_comm | (intros; apply GlobalTheory.Poinc.Sep.Spz.spread₂_endU_comm <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toric_torsion_point_of_lattice_character : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ) (z : F), 1 ≤ k → z ^ k = 1 → ∀ c : D.toPre.X →+ ℤ, ∃ x : TFK (R := V) F ⟶ A.A, TorAt U F k z c x := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_torAt | exact GlobalTheory.Poinc.Sep.Spz.exists_torAt | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_torAt <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section
namespace GlobalTheory.Poinc.Sep.Spz
open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

theorem isPrimitiveRoot_map_of_isUnit_order {o K : Type} [CommRing o] [IsDomain o] [CommRing K] [IsDomain K] (φ : o →+* K)
    {m : ℕ} (hm : 0 < m) {q : o} (hq : IsPrimitiveRoot q m) (hu : IsUnit (m : o)) : IsPrimitiveRoot (φ q) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine IsPrimitiveRoot.mk_of_lt _ hm (by rw [← map_pow, hq.pow_eq_one, map_one]) fun l hl hlt h1 => ?_
  have hp := congrArg φ hq.prod_one_sub_pow_eq_order
  rw [map_prod] at hp
  have hz : ∏ k ∈ Finset.range n, φ (1 - q ^ (k + 1)) = 0 := by
    refine Finset.prod_eq_zero (i := l - 1) (Finset.mem_range.2 (by omega)) ?_
    rw [map_sub, map_one, map_pow, Nat.sub_add_cancel hl, h1, sub_self]
  rw [hz] at hp
  have hu' : IsUnit (φ ((n : o) + 1)) := by
    have := hu.map φ; simpa using this
  exact hu'.ne_zero hp.symm

theorem intCast_eq_of_zpow_eq {K : Type} [Field K] {m : ℕ} [NeZero m] {z : K} (hz : IsPrimitiveRoot z m) {a : ℤ}
    {b : ZMod m} (h : z ^ a = z ^ (b.val : ℤ)) : (a : ZMod m) = b := by
  have hz0 : z ≠ 0 := hz.ne_zero (NeZero.ne m)
  have h1 : z ^ (a - (b.val : ℤ)) = 1 := by rw [zpow_sub₀ hz0, h, div_self (zpow_ne_zero _ hz0)]
  have h2 := (hz.zpow_eq_one_iff_dvd _).1 h1
  have h3 : ((a - (b.val : ℤ) : ℤ) : ZMod m) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h2
  rw [Int.cast_sub, sub_eq_zero, Int.cast_natCast, ZMod.natCast_zmod_val] at h3
  exact h3

theorem torAt_char_eq_weil : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (c : 𝔪.D.toPre.X →+ ℤ) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), TorAt 𝔪.U (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) c x → x.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt τ).left → ∀ a mu, 𝔪.YY a mu → ((c (𝔪.e₈ mu) : ℤ) : ZMod (X₁.S.r * X₁.S.N)) = ((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a := by
  intro g n F W Z i X₁ z₁ act
  refine ⟨1, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 τ c x hT hxo a mu hY
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  obtain ⟨τ', q, hτv, hqy, hqt, hqx⟩ := hT
  obtain ⟨p', x', hp'y, hp'x, hx'o⟩ := hY
  have W₁ := weilQkIs_tor hG q p' hqy hqt
  have W₂ := (GlobalTheory.UT.weilQkIs_iff_weilIs hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk q p' x x' hqx hp'x (τ' (Multiplicative.ofAdd p'.y))).1 W₁
  have := X₁.ρ.P.isAb.comm
  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := (spMap_comp _ _).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := hy
  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
    X₁.S.prim.pow (pow_pos hk 2) (pow_two _)
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit (by omega)).unit
  have w := GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h
    (X₁.ρ.weil τ a (c₀ ^ (eStd X₁.S.g _ τ a).val) (by rw [pow_mul, map_pow]; rfl))
  have W₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩
    (TFK (R := V) (AlgebraicClosure (FractionRing V))) _
    x x' (h ≫ X₁.ρ.pt τ) (h ≫ X₁.ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB W₂ W₃)
    rw [hp'y] at e
    have e' := congrArg Units.val e
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.coe_comp, Function.comp_apply, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec] at e'
    rw [hτv] at e'
    rw [Units.val_one, one_smul]
    haveI : IsDomain X₁.o₁ := X₁.ar.ded.toIsDomain
    haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨by omega⟩
    have hzp := isPrimitiveRoot_map_of_isUnit_order ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (𝔪.yK.comp (algebraMap X₁.o₁ X₁.S.R))) (by omega) hζ X₁.S.unit
    refine intCast_eq_of_zpow_eq hzp ?_
    rw [zpow_natCast]
    simp only [RingHom.coe_comp, Function.comp_apply, map_pow] at e' ⊢
    exact e'
  · show h.left ≫ (X₁.ρ.pt τ).left = _
    rw [hh, hxo]
  · show h.left ≫ (X₁.ρ.pt a).left = _
    rw [hx'o, hh]

end GlobalTheory.Poinc.Sep.Spz
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsionPoint_character_eq_weilPairing_label : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (c : 𝔪.D.toPre.X →+ ℤ) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), TorAt 𝔪.U (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) c x → x.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt τ).left → ∀ a mu, 𝔪.YY a mu → ((c (𝔪.e₈ mu) : ℤ) : ZMod (X₁.S.r * X₁.S.N)) = ((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a := by
  atlas_forward_decl GlobalTheory.Poinc.Sep.Spz.torAt_char_eq_weil
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_pullback_semiAbelian_over_normalDomain : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Algebra O Ω] [IsFractionRing O Ω] (x : Sp O ⟶ M.Z) (u : S.R →+* O), spMap (algebraMap O Ω) ≫ x = M.pt → (algebraMap O Ω).comp u = S.R.val.toRingHom → ∃ gm : ((Over.pullback (spMap u)).obj ρ.P.A).left ⟶ FinalForm.G.left, Link FinalForm x (spMap u) ((Over.pullback (spMap u)).obj ρ.P.A) (pullback.fst ρ.P.A.hom (spMap u)) gm := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.link_of_normal | exact GlobalTheory.Poinc.Sep.Spz.link_of_normal | (intros; apply GlobalTheory.Poinc.Sep.Spz.link_of_normal <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalNoetherianStalk_factor_of_fieldPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), IsNormalScheme M.Z → ∀ (R : Subalgebra o Ω) (K : Type) [Field K] (x : Sp K ⟶ M.Z) (yK : R →+* K), (∀ a ∈ R, a ∈ M.O (x (closedPoint K))) → (∀ a : R, yK a = M.val x a) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsNoetherianRing O) (_ : IsIntegrallyClosed O) (_ : Algebra O Ω) (_ : IsFractionRing O Ω) (xO : Sp O ⟶ M.Z) (u : R →+* O) (v : O →+* K), spMap (algebraMap O Ω) ≫ xO = M.pt ∧ (algebraMap O Ω).comp u = R.val.toRingHom ∧ spMap v ≫ xO = x ∧ v.comp u = yK := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_stalk_factor | exact GlobalTheory.Poinc.Sep.Spz.exists_stalk_factor | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_stalk_factor <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpPullback_uniformisingGroup_sameGenericFibre : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (gm : A.A.left ⟶ H.left), IsGrpPullback A.A H (jK V ≫ ξ) gm → ∃ β : G.left ⟶ H.left, IsGrpPullback G H ξ β ∧ genMap U ≫ β = gm ∧ ∀ (E : EndU U.toUnifPre) (Fm : H ⟶ H), E.aA.left ≫ gm = gm ≫ Fm.left → E.aG.left ≫ β = β ≫ Fm.left := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.exists_ext | exact GlobalTheory.Poinc.Sep.Spz.exists_ext | (intros; apply GlobalTheory.Poinc.Sep.Spz.exists_ext <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianEnd_extending_abelianSchemeEnd : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ f : ρ.P.A ⟶ ρ.P.A, IsMonHom f → ∃ Fm : FinalForm.G ⟶ FinalForm.G, EndOn FinalForm f Fm := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.endOn_exists | exact GlobalTheory.Poinc.Sep.Spz.endOn_exists | (intros; apply GlobalTheory.Poinc.Sep.Spz.endOn_exists <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem exists_eq_nsmul_of_forall_dvd {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (L : ℕ) (x : X)
    (h : ∀ c : X →+ ℤ, (L : ℤ) ∣ c x) : ∃ w, x = L • w := by
  let b := Module.Free.chooseBasis ℤ X
  choose w hw using fun k => h (b.coord k).toAddMonoidHom
  refine ⟨∑ k, w k • b k, ?_⟩
  rw [Finset.smul_sum, ← b.sum_repr x]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : b.repr x k = L * w k := hw k
  rw [this, mul_smul, natCast_zsmul]

theorem injective_of_ker_le {X Y : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup Y]
    [Module.Free ℤ Y] (ρ : X →+ Y) (L : ℕ) (hL : 2 ≤ L) (h : ∀ x, ρ x = 0 → ∃ w, x = L • w) : Function.Injective ρ := by
  refine (injective_iff_map_eq_zero ρ).2 fun x hx => ?_
  have key : ∀ k : ℕ, ∃ w, ρ w = 0 ∧ x = L ^ k • w := by
    intro k
    induction k with
    | zero => exact ⟨x, hx, by simp⟩
    | succ k ih =>
      obtain ⟨w, hw, rfl⟩ := ih
      obtain ⟨w', rfl⟩ := h w hw
      refine ⟨w', ?_, by rw [smul_smul, pow_succ]⟩
      rw [map_nsmul, ← natCast_zsmul] at hw
      exact (smul_eq_zero.1 hw).resolve_left (by omega)
  let b := Module.Free.chooseBasis ℤ X
  refine b.repr.injective (Finsupp.ext fun k => ?_)
  obtain ⟨w, -, hw⟩ := key (b.repr x k).natAbs
  rw [map_zero, Finsupp.zero_apply]
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := ((L ^ (b.repr x k).natAbs : ℕ) : ℤ)) ⟨b.repr w k, ?_⟩ ?_
  · conv_lhs => rw [hw]
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  · rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega)

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {Y : RatModel X₁.o₁ X₁.Ω₁} {πY : Y.Z ⟶ X₁.M.Z} {U₀ : Y.Z.Opens} {EE : Y.Lat X₁.S.J} (FinalForm : ZHOut X₁.ρ Y U₀ EE)
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
  (𝔫 : UMem X₁ z₁ act V ev X t δ) {ξ : Sp V ⟶ Y.Z}

include 𝔫 in

theorem base_of_uMem : GlobalTheory.Mum.Base V :=
  ⟨⟨𝔫.cn.1, inferInstance, 𝔫.cn.2.1, 𝔫.cn.2.2.1⟩, 𝔫.cn.2.2.2⟩

theorem exists_link (hO : X₁.S.Over₀ Y U₀) (hπ : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY)
    (hξ : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) :
    ∃ β : 𝔫.G.left ⟶ FinalForm.G.left, IsGrpPullback 𝔫.G FinalForm.G ξ β ∧
      Link FinalForm (jK V ≫ ξ) (spMap 𝔫.yK) 𝔫.A.A 𝔫.φ (genMap 𝔫.U ≫ β) ∧
      ∀ (f : X₁.ρ.P.A ⟶ X₁.ρ.P.A) (Fm : FinalForm.G ⟶ FinalForm.G), EndOn FinalForm f Fm → ∀ E : EndU 𝔫.U.toUnifPre,
        E.aA.left ≫ 𝔫.φ = 𝔫.φ ≫ f.left → E.aG.left ≫ β = β ≫ Fm.left := by
  have e : (jK V ≫ ξ) ≫ πY = jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ := by rw [Category.assoc, hξ]
  have hreg : ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (πY ((jK V ≫ ξ) (closedPoint (FractionRing V)))) := fun a ha => by
    have := 𝔫.reg a ha
    rw [← e] at this
    exact this
  obtain ⟨O, _, _, _, _, _, _, xO, u, v, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.exists_normalNoetherianStalk_factor_of_fieldPoint X₁.o₁ X₁.Ω₁ Y hO.normal X₁.S.R (FractionRing V)
    (jK V ≫ ξ) 𝔫.yK (fun a ha => hπ.map_mem_O (hreg a ha)) (fun a => by
      rw [𝔫.yK_eq, ← e]
      exact hπ.val_comp _ _ (hreg a a.2))
  obtain ⟨gm, hgm⟩ := GlobalTheory.T.abelianScheme_pullback_semiAbelian_over_normalDomain X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ Y U₀ EE FinalForm hO.ne O xO u h₁ h₂
  have e₂ : spMap v ≫ spMap u = spMap 𝔫.yK := (GlobalTheory.SpreadTrait.spMap_comp' u v).trans (congrArg spMap h₄)
  obtain ⟨w, hw, hwφ⟩ := GlobalTheory.SpreadTrait.pull_cancel (isGrpPullback_pullback X₁.ρ.P.A (spMap u)) (spMap v)
    (𝔫.cart.congr e₂.symm rfl)
  have hl := hgm.pull FinalForm hw
  rw [h₃, e₂, hwφ] at hl
  obtain ⟨β, hβ, hβg, hE⟩ := GlobalTheory.T.exists_grpPullback_uniformisingGroup_sameGenericFibre Y.Z FinalForm.G FinalForm.semi V (base_of_uMem 𝔫) 𝔫.G 𝔫.semi 𝔫.D 𝔫.A 𝔫.U ξ _ hl.1
  refine ⟨β, hβ, hβg ▸ hl, fun f Fm hf E h => hE E Fm ?_⟩
  have := hl.2.1 f Fm hf _ (𝟙 _) E.aA.left ((Over.w E.aA).trans (Category.id_comp _).symm)
    (h.trans (Category.id_comp _).symm)
  exact this.trans (Category.id_comp _)

theorem yK_algebraMap (hπ : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY)
    (hξ : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) :
    ∃ oV : X₁.o₁ →+* V, ξ ≫ Y.s = spMap oV ∧
      ∀ a, 𝔫.yK (algebraMap X₁.o₁ X₁.S.R a) = algebraMap V (FractionRing V) (oV a) := by
  have h : ξ ≫ Y.s = spMap (Spec.preimage (ξ ≫ Y.s)).hom := (Spec.map_preimage _).symm
  refine ⟨_, h, fun a => ?_⟩
  rw [𝔫.yK_eq, ← hξ]
  refine RatModel.val_algebraMap (σ := (algebraMap V (FractionRing V)).comp (Spec.preimage (ξ ≫ Y.s)).hom) ?_ a
  rw [Category.assoc, Category.assoc, hπ.inducedModelMorphism_comp_structureMap]
  exact (congrArg (jK V ≫ ·) h).trans (GlobalTheory.SpreadTrait.spMap_comp' _ _)

theorem pow_eq_one_of_qkToAkU {K : Type} [Field K] [Algebra (FractionRing V) K] {k : ℕ} {q : QkPt 𝔫.D.toPre K k}
    {x : TFK (R := V) K ⟶ 𝔫.A.A} (h : QkToAkU 𝔫.U.toUnifPre K k q x) : x ^ k = 1 := by
  obtain ⟨w, hw⟩ := 𝔫.U.ext
  exact (h w hw).1

theorem pt_eq_sec {β : 𝔫.G.left ⟶ FinalForm.G.left}
    (hl : Link FinalForm (jK V ≫ ξ) (spMap 𝔫.yK) 𝔫.A.A 𝔫.φ (genMap 𝔫.U ≫ β)) {a : X₁.S.Gam} {Wo : Y.Z.Opens}
    {h : Wo.toScheme ⟶ FinalForm.G.left} (hs : SecOn FinalForm a Wo h) {ξ' : Sp V ⟶ Wo.toScheme} (hξ' : ξ' ≫ Wo.ι = ξ)
    (K : Type) [Field K] [Algebra (FractionRing V) K] (x : TFK (R := V) K ⟶ 𝔫.A.A)
    (hx : x.left ≫ 𝔫.φ = spMap ((algebraMap (FractionRing V) K).comp 𝔫.yK) ≫ (X₁.ρ.pt a).left) :
    x.left ≫ genMap 𝔫.U ≫ β = spMap (algebraMap (FractionRing V) K) ≫ jK V ≫ ξ' ≫ h := by
  have e : x.left ≫ 𝔫.A.A.hom = spMap (algebraMap (FractionRing V) K) := Over.w x
  have := hl.2.2 a Wo h hs _ x.left (spMap (algebraMap (FractionRing V) K) ≫ jK V ≫ ξ') (by
    rw [reassoc_of% e]
    simp only [Category.assoc, hξ']) (by
    rw [reassoc_of% e, hx, ← GlobalTheory.SpreadTrait.spMap_comp', Category.assoc])
  simpa only [Category.assoc] using this

end GlobalTheory.Poinc.Sep.Spz

theorem GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] [IsDiscreteValuationRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (X₀ : Type) [AddCommGroup X₀] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ X₀) (𝔫₁ : UMem X₁ z₁ act V₁ ev₁ X₀ t₁ δ₁) (ξ₁ : Sp V₁ ⟶ Y.Z) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] [IsDiscreteValuationRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (X : Type) [AddCommGroup X] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ X) (𝔫₂ : UMem X₁ z₁ act V₂ ev₂ X t₂ δ₂) (ξ₂ : Sp V₂ ⟶ Y.Z), ξ₁ ≫ πY = spMap ev₁ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₂ ≫ πY = spMap ev₂ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → Cmp.LatTo 𝔫₁ 𝔫₂ := by
  intro g n F W Z i X₁ z₁ act hact Y πY hZ V₁ _ _ _ _ ev₁ X₀ _ m₁ t₁ δ₁ 𝔫₁ ξ₁ V₂ _ _ _ _ ev₂ X _ m₂ t₂ δ₂ 𝔫₂ ξ₂ hξ₁ hξ₂ hsp
  obtain ⟨U₀, EE, ⟨FinalForm⟩, hO, -, hπ, -⟩ := hZ
  obtain ⟨β₁, hβ₁, hl₁, hE₁⟩ := exists_link FinalForm 𝔫₁ hO hπ hξ₁
  obtain ⟨β₂, hβ₂, hl₂, hE₂⟩ := exists_link FinalForm 𝔫₂ hO hπ hξ₂
  obtain ⟨o₁, ho₁, hy₁⟩ := yK_algebraMap 𝔫₁ hπ hξ₁
  obtain ⟨o₂, ho₂, hy₂⟩ := yK_algebraMap 𝔫₂ hπ hξ₂
  have b₁ := base_of_uMem 𝔫₁
  have b₂ := base_of_uMem 𝔫₂
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_torus_spread_over_trait_specialisation Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ inferInstance (by
      haveI := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
      haveI := Y.lft
      exact LocallyOfFiniteType.isLocallyNoetherian Y.s) hsp
  have onto := GlobalTheory.T.torus_spread_lattice_map_surjective Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ ρ hρ
  have eqv := GlobalTheory.T.torus_spread_lattice_map_commutes_endomorphisms Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ ρ hρ
  have tor := GlobalTheory.T.toricTorsionSection_of_spread_through_latticeMap Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ ρ hρ X₁.o₁ Y.s o₁ o₂ ho₁ ho₂
  obtain ⟨tot₁, sur₁, cong₁, -⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V₁ ev₁ X₀ m₁ t₁ δ₁ 𝔫₁
  obtain ⟨tot₂, sur₂, cong₂, -⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V₂ ev₂ X m₂ t₂ δ₂ 𝔫₂
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  have int₁ := GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hx₀ V₁ ev₁ X₀ m₁ t₁ δ₁ 𝔫₁
  have int₂ := GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hx₀ V₂ ev₂ X m₂ t₂ δ₂ 𝔫₂
  obtain ⟨sg, weil⟩ := GlobalTheory.T.toricTorsionPoint_character_eq_weilPairing_label g n F W Z i X₁ z₁ act
  have hL : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  have hζ : (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (X₁.S.r * X₁.S.N) = 1 := by
    rw [← pow_mul, ← sq]; exact X₁.S.prim.pow_eq_one

  have hy : πY (ξ₂ (closedPoint V₂)) = z₁ := by
    haveI := 𝔫₂.loc
    have : (ξ₂ ≫ πY) (closedPoint V₂) = z₁ := by
      rw [hξ₂]
      exact (congrArg (X₁.M.Z.fromSpecStalk z₁) (IsLocalRing.comap_closedPoint ev₂)).trans
        Scheme.fromSpecStalk_closedPoint
    exact this
  have hHH : X₁.S.HH X₁.M z₁ ≤ X₁.S.HH Y (ξ₂ (closedPoint V₂)) :=
    AddSubgroup.closure_mono fun a ha => hπ.div (t := X₁.S.th) (hy.symm ▸ ha)

  have lab : ∀ a mu₁ mu₂, 𝔫₁.YY a mu₁ → 𝔫₂.YY a mu₂ →
      ∃ w, 𝔫₁.e₈ mu₁ - ρ (𝔫₂.e₈ mu₂) = (X₁.S.r * X₁.S.N) • w := by
    intro a mu₁ mu₂ h₁ h₂
    refine exists_eq_nsmul_of_forall_dvd _ _ fun c => ?_
    obtain ⟨x₁, hx₁⟩ := GlobalTheory.T.exists_toric_torsion_point_of_lattice_character V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U (AlgebraicClosure (FractionRing V₁))
      (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V₁) _ (algebraMap V₁ _ (o₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) (by omega)
      (by rw [← map_pow, ← map_pow, ← map_pow, hζ, map_one, map_one, map_one]) c
    obtain ⟨τ', q, hτ', hq, hq', hQ⟩ := id hx₁
    obtain ⟨τ, hτ⟩ := GlobalTheory.Poinc.IntTerm.torsion_has_label g n F W Z i X₁ z₁ act V₁ ev₁ X₀ m₁ t₁ δ₁ 𝔫₁ x₁ (pow_eq_one_of_qkToAkU 𝔫₁ hQ)
    have hH : τ ∈ X₁.S.HH X₁.M z₁ := (int₁ τ).2 ⟨q, x₁, hq.trans (map_zero _).symm, hQ, hτ⟩
    obtain ⟨Wo, h, hW, hs⟩ := FinalForm.sec _ τ (hHH hH)
    have lift : ∀ {V : Type} [CommRing V] [IsLocalRing V] (ξ : Sp V ⟶ Y.Z), ξ (closedPoint V) ∈ Wo →
        ∃ ξ' : Sp V ⟶ Wo.toScheme, ξ' ≫ Wo.ι = ξ := fun ξ hξ =>
      ⟨IsOpenImmersion.lift Wo.ι ξ (by
        rintro _ ⟨w, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact ((IsLocalRing.specializes_closedPoint w).map ξ.continuous).mem_open Wo.isOpen hξ),
        IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨ξ₁', hξ₁'⟩ := lift ξ₁ (hsp.mem_open Wo.isOpen hW)
    obtain ⟨ξ₂', hξ₂'⟩ := lift ξ₂ hW
    obtain ⟨-, q₂, x₂, -, hQ₂, hx₂'⟩ := tot₂ τ
    have hx₂ := pow_eq_one_of_qkToAkU 𝔫₂ hQ₂
    have ht := tor _ _ (by omega) X₁.S.unit hζ Wo h ξ₁' ξ₂' hs.1 hξ₁' hξ₂' _ _ c x₁ x₂ hx₁
      (pt_eq_sec FinalForm 𝔫₁ hl₁ hs hξ₁' _ x₁ hτ) hx₂ (pt_eq_sec FinalForm 𝔫₂ hl₂ hs hξ₂' _ x₂ hx₂')
    rw [← hy₁] at hx₁
    rw [← hy₂] at ht
    have w₁ := weil V₁ ev₁ X₀ m₁ t₁ δ₁ 𝔫₁ τ c x₁ hx₁ hτ a mu₁ h₁
    have w₂ := weil V₂ ev₂ X m₂ t₂ δ₂ 𝔫₂ τ _ x₂ ht hx₂' a mu₂ h₂
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, map_sub, Int.cast_sub, w₁, sub_eq_zero]
    exact w₂.symm
  have vec : ∀ {X' : Type} [AddCommGroup X'] (mu mu' w : Fin 8 → X'), mu' = mu + (X₁.S.r * X₁.S.N) • w →
      ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu' v) (mu v) := fun mu mu' w h v => ⟨w v, congrFun h v⟩
  have inj : Function.Injective ρ := by
    refine injective_of_ker_le ρ _ hL fun y hy0 => ?_
    obtain ⟨mu, rfl⟩ := 𝔫₂.e₈.surjective y
    obtain ⟨a, ha⟩ := sur₂ mu
    obtain ⟨mu₁, h₁⟩ := tot₁ a
    obtain ⟨w, hw⟩ := lab a mu₁ mu h₁ ha
    have h0 : 𝔫₁.YY a 0 := (cong₁ a mu₁ 0 h₁).2 (vec _ _ (-𝔫₁.e₈.symm w) (𝔫₁.e₈.injective (by
      rw [hy0, sub_zero] at hw
      simp [hw])))
    have h0' := (cong₂ a 0 mu ((int₂ a).1 ((int₁ a).2 h0))).1 ha
    choose w' hw' using h0'
    exact ⟨𝔫₂.e₈ w', by rw [← map_nsmul]; exact congrArg _ (funext fun v => by simpa using hw' v)⟩
  let e := AddEquiv.ofBijective ρ ⟨inj, onto⟩
  let K : (Fin 8 → X₀) ≃+ (Fin 8 → X) := (𝔫₁.e₈.trans e.symm).trans 𝔫₂.e₈.symm
  have hK : ∀ mu, ρ (𝔫₂.e₈ (K mu)) = 𝔫₁.e₈ mu := fun mu => by
    simp only [K, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    exact e.apply_symm_apply _
  refine ⟨K, fun a' mu => ?_, fun a mu h₁ => ?_⟩
  · have hdet : (W + W.transpose).det = 1 := X₁.e8.2
    have ha : (W + W.transpose) * a' = ((W + W.transpose) * a' * (W + W.transpose).adjugate).transpose.transpose *
        (W + W.transpose) := by
      rw [Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.adjugate_mul, hdet, one_smul, Matrix.mul_one]
    obtain ⟨E₁, h₁, h₁'⟩ := 𝔫₁.equiv _ a' ha
    obtain ⟨E₂, h₂, h₂'⟩ := 𝔫₂.equiv _ a' ha
    obtain ⟨Fm, hF⟩ := GlobalTheory.T.exists_semiAbelianEnd_extending_abelianSchemeEnd X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ Y U₀ EE FinalForm hO.ne _ (hact.isMonHom _)
    apply 𝔫₂.e₈.injective
    apply inj
    rw [hK, ← h₂', eqv Fm E₁ E₂ (hE₁ _ Fm hF E₁ h₁) (hE₂ _ Fm hF E₂ h₂), hK, h₁']
  · obtain ⟨mu₂, h₂⟩ := tot₂ a
    obtain ⟨w, hw⟩ := lab a mu mu₂ h₁ h₂
    obtain ⟨w', rfl⟩ := onto w
    refine (cong₂ a mu₂ _ h₂).2 (vec _ _ (𝔫₂.e₈.symm w') (𝔫₂.e₈.injective (inj ?_)))
    rw [hK, map_add, map_add, map_nsmul, map_nsmul, AddEquiv.apply_symm_apply, ← hw, add_sub_cancel]
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberLattices_iso_of_specialising_closedPoints : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] [IsDiscreteValuationRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (X₀ : Type) [AddCommGroup X₀] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ X₀) (𝔫₁ : UMem X₁ z₁ act V₁ ev₁ X₀ t₁ δ₁) (ξ₁ : Sp V₁ ⟶ Y.Z) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] [IsDiscreteValuationRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (X : Type) [AddCommGroup X] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ X) (𝔫₂ : UMem X₁ z₁ act V₂ ev₂ X t₂ δ₂) (ξ₂ : Sp V₂ ⟶ Y.Z), ξ₁ ≫ πY = spMap ev₁ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₂ ≫ πY = spMap ev₂ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → Cmp.LatTo 𝔫₁ 𝔫₂ := by
  atlas_forward_decl GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes
end
