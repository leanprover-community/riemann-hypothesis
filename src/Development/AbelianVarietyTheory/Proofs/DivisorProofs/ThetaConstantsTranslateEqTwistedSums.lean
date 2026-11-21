import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusCharOfLabelOrthogonalDividing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedAdicSumTermsOfFractionFieldSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.YKThNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigTorsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
import Development.AbelianVarietyTheory.Definitions.Divisors.NotTwistSumZeroFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelKilledCharOfTorusLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFCompEquiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsFrameTwoLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusCharOfLabelOrthogonalDividingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusTranslationExponentAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermNonzeroIndexMemMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMemberPOfIsMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemThetaConstantNegEvenUpToRoot

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep

open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

theorem torusChar_eq_weil_gen : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) := by
  intro I X₁ z₁ act
  refine ⟨1, ?_⟩
  intro V _ _ _ ev X _ t δ 𝔪 τ χ hχ hpt a mu hY
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hK : KerPowSt := hL.1.kerPow
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p, x, hpy, hpg, hpx, hxo⟩ := hpt (torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ))
    ((isTor_iff _ _).2 (isTorusPtF_torusPt χ))
  obtain ⟨p', x', hp'y, hp'x, hx'o⟩ := hY
  set p₁ := qkExt hB (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) hf p with hp₁
  have hext : QkExt (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) p p₁ := (qkExt_iff hB _ hf p _).2 rfl
  set χ₁ : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ :=
    (Units.map (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).toMonoidHom).comp χ with hχ₁
  have hp₁g : p₁.g = torusPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (Additive.ofMul χ₁) := by
    show gtExt _ _ hf p.g = _
    rw [hpg]
    exact gtExt_torusPt _ hf χ
  have hp₁y : p₁.y = 0 := hpy
  have hτ₁ : IsTor χ₁ p₁.g := by rw [hp₁g]; exact (isTor_iff _ _).2 (isTorusPtF_torusPt χ₁)
  have W₁ := weilQkIs_tor hG p₁ p' hp₁y hτ₁
  have hx₁ := (qkToAkU_iff_of_algebra hG hK 𝔪.U hk hext x).1 hpx
  have W₂ := (GlobalTheory.UT.weilQkIs_iff_weilIs hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk p₁ p' _ x' hx₁ hp'x (χ₁ (Multiplicative.ofAdd p'.y))).1 W₁
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
    (fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x) x' (h ≫ X₁.ρ.pt τ) (h ≫ X₁.ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB W₂ W₃)
    rw [hp'y] at e
    have e' := congrArg Units.val e
    simp only [hχ₁, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.coe_comp, Function.comp_apply, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec] at e'
    rw [Units.val_one, one_smul]
    refine (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective ?_
    have hc : (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) ^ (eStd X₁.S.g _ τ a).val =
        algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ a).val)) := by
      simp only [pow_mul, map_pow]
    rw [e']
    exact congrArg (fun z => algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK z)) hc
  · show h.left ≫ (X₁.ρ.pt τ).left = _
    rw [Over.comp_left, Category.assoc, hxo]
    rfl
  · show h.left ≫ (X₁.ρ.pt a).left = _
    rw [hx'o, hh]

end GlobalTheory.GSep
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.GMem

theorem exists_yy : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (mu : X), ∃ a : X₁.S.Gam, 𝔪.YY a mu := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 mu
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    have hn := X₁.ρ.n_prime.pos
    rw [hj, X₁.ρ.N_eq]
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨h, hh⟩ := GlobalTheory.TorusExt.exists_iota (F := AlgebraicClosure (FractionRing V)) 𝔪.D.tau_bimult (𝔪.e₈ mu)
  obtain ⟨g', hg'⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D
    (AlgebraicClosure (FractionRing V))).2.1 _ hk h
  let p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) := ⟨𝔪.e₈ mu, g', h, hg', hh⟩
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk
  have hx := (hf p (f p)).2 rfl
  obtain ⟨w, hw⟩ := 𝔪.U.ext
  have hpow : f p ^ (X₁.S.r * X₁.S.N) = 1 := (hx w hw).1
  let z := pushHom 𝔪.cart (TFK (R := V) (AlgebraicClosure (FractionRing V))) (f p)
  have hz : z ^ (X₁.S.r * X₁.S.N) = 1 := by
    simp only [z]
    rw [← map_pow, hpow, map_one]
  obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ z hz
  refine ⟨a, p, f p, rfl, hx, ?_⟩
  have e := congrArg (fun q => q.left) ha
  simp only [Over.comp_left, Over.homMk_left] at e
  have e2 : spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ spMap 𝔪.yK := by
    simp [spMap, jFK, ← Spec.map_comp]
  rw [e2]
  exact e.symm

end GlobalTheory.GSep.GMem
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
open GlobalTheory.Poinc.Sep

noncomputable section

theorem GlobalTheory.GSep.twistAtEach_exists : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  intro I X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg⟩ := GlobalTheory.GSep.torusChar_eq_weil_gen I X₁ z₁ act
  refine ⟨sg, ?_, hsg⟩
  intro V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT c τ hτ
  obtain ⟨χ, hχN, hχo⟩ := GlobalTheory.GSep.TorPt.exists_torus_char I X₁ z₁ act V ev X t δ 𝔪 τ hτ
  obtain ⟨e, he⟩ := GlobalTheory.GSep.TwistTranslate.twistSum_translate I X₁ z₁ act V ev X t δ 𝔪 x₀ C lab hlab T hT c τ hτ χ hχN hχo
  exact ⟨e, GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF I X₁ z₁ act V ev X t δ 𝔪 x₀ C lab T sg c τ χ e
    (GlobalTheory.GSep.GMem.yK_th_ne_zero I X₁ z₁ act V ev X t δ 𝔪 x₀ hdiv)
    (GlobalTheory.GSep.GMem.exists_yy I X₁ z₁ act V ev X t δ 𝔪) (hsg V ev X t δ 𝔪 τ χ hχN hχo) he⟩
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_theta_sum_common_sign_member : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg ∧ (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) := by
  atlas_forward_decl GlobalTheory.GSep.twistAtEach_exists
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedAdicSum_terms_of_fractionField_sum : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V) (sg : ℤˣ) (c : C) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) (e : ℕ), 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 → (∀ mu, ∃ a : X₁.S.Gam, 𝔪.YY a mu) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) → SumF (maximalIdeal V) (FractionRing V) (fun mu : X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  first | exact @GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF | exact GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF | (intros; apply GlobalTheory.GSep.TwistSum₂.twistSum_of_sumF <;> assumption)
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
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.GSep.TermsExt
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue

theorem exists_frAt_ratio {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {K : Type} [Field K] [Algebra (FractionRing R) K] {x : TFK (R := R) K ⟶ A.A} {e e' : FrAt x} (he : e.IsGen)
    (he' : e'.IsGen) : ∃ c : K, c ≠ 0 ∧ ∀ z J, Good A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := R) K).left.presheaf.stalk z) (cstH (R := R) z c) * (val e (𝟙 _) z J).val := by
  obtain ⟨z⟩ : Nonempty (TFK (R := R) K).left := exists_pt (R := R) (F := K)
  obtain ⟨J', hJ'⟩ := exists_good' A.isLB z
  obtain ⟨c, hc⟩ := cstH_surj (R := R) (F := K) z (val e' (𝟙 _) z J' * (val e (𝟙 _) z J')⁻¹).val
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl : z = z' := pt_eq (R := R) (F := K) z z'
    rw [hc, val_tr he (𝟙 _) hJ hJ', val_tr he' (𝟙 _) hJ hJ']
    refine Eq.trans ?_ (Units.val_mul _ _)
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem over_scale {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}
    (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {w₀ : W0 𝔪.U.toUnifPre} {g' : GtPtF 𝔪.D.toPre (FractionRing V)}
    {w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b} (hw : w.IsGen) {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    {e e' : FrAt x} {c : FractionRing V} (hc : c ≠ 0)
    (he : ∀ z J, Good 𝔪.A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z c) * (val e (𝟙 _) z J).val)
    (hv : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w' (𝟙 _) z J).val = cst (FractionRing V) z c⁻¹ * (val w (𝟙 _) z J).val)
    (h : 𝔪.Over' w₀ g' w x e) : 𝔪.Over' w₀ g' w' x e' := by
  intro k hk wk' hwk' _ s s' v hs hval
  obtain ⟨wk, hwk, hwkv⟩ := exists_frm_pow w hw k
  have pf : ∀ (e : FrAt x) z J, val (powFrame 𝔪.A.A 𝔪.A.L x e (k : ℤ)) (𝟙 _) z J = val e (𝟙 _) z J ^ k :=
    fun e z J => (map_zpow _ _ _).trans (zpow_natCast _ _)
  have hval' : ValAt s x e (c ^ k * v) := fun z J hJ => by
    have cm : @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cst (R := V) (FractionRing V) z (c ^ k * v)) =
        @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z c) ^ k *
          @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cst (R := V) (FractionRing V) z v) :=
      (cst_eq (R := V) z _).trans ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (map_pow _ _ _) (cst_eq (R := V) z _).symm))
    rw [hval z J hJ, pf, pf, cm, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he z J hJ]
    ring
  have S := sumF_const_mul (c⁻¹ ^ k) (h k hk wk hwkv hwk s s' _ hs hval')
  have sc := coef_scale (w' := wk') hwk (c := c⁻¹ ^ k) (fun z J hJ => by
    rw [hwk' z J hJ, hwkv z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ, mul_pow,
      cst_eq, cst_eq, map_pow]) s'
  rw [← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hc, one_pow, _root_.one_mul] at S
  simpa only [← sc] using S

attribute [local instance] GlobalTheory.TorusExt.gtGroup in

theorem exists_terms_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ T' : X → Unit → V, 𝔪.Terms x₀ (fun _ : Unit => lab c + τ) T' := by
  intro I X₁ z₁ act x₀ _ V _ _ _ ev X _ t δ 𝔪 C lab _ T hT c τ hτ
  obtain ⟨χ, hχ, hyp⟩ := GlobalTheory.T.exists_torus_char_of_label_orthogonal_dividing I X₁ z₁ act V ev X t δ 𝔪 τ hτ
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hTc⟩ := hT
  obtain ⟨ρA, hρA, htors⟩ := GlobalTheory.GSep.TwistTranslate.exists_rig_torsFrame 𝔪 x fr hx hfr
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' c) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w'', hw''g, hw''v⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1 (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w''.IsGen ∧ ∀ z J, val w'' (𝟙 _) z J = val (w c) (𝟙 _) z J := by
    revert hb
    generalize (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w c, (hc c).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := GlobalTheory.GSep.TwistTranslate.over_translate 𝔪 w₀ hw₀ ρA hρA (x (lab c)) (fr (lab c)) (htors _)
    (g' c) (w c) (hc c).1 (hc c).2.1 (hc c).2.2 χ hχ _ hg₀ p xτ hpy hpg hq _ hadd w'' (fun z J _ => hw''v z J)
    (x (lab c + τ)) (GlobalTheory.GSep.TwistTranslate.x_add 𝔪 x hx (lab c) τ xτ hxτ)
  obtain ⟨u, hu, huv⟩ := exists_frAt_ratio he₂.2.1 (htors (lab c + τ)).2.1
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hu1 : u ^ ((X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2) = 1 := by
    obtain ⟨z⟩ : Nonempty (TFK (R := V) (FractionRing V)).left := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J, hJ⟩ := exists_good' 𝔪.A.isLB z
    have q := GlobalTheory.Poinc.DivDeep.torsFrame_two_levels 𝔪.A (htors (lab c + τ)) he₂ hJ
    rw [div_self', one_pow] at q
    have q' := congrArg Units.val q
    have e : (val (fr (lab c + τ)) (𝟙 _) z J / val e₂ (𝟙 _) z J).val =
        @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z u) := by
      rw [div_eq_mul_inv, Units.val_mul, huv z J hJ, Units.mul_inv_cancel_right]
    rw [Units.val_pow_eq_pow_val, e] at q'
    exact cstH_inj (R := V) z ((map_pow _ _ _).trans (q'.trans (map_one _).symm))
  obtain ⟨w₃, hw₃, hw₃v⟩ := exists_frm_scale w'' hw''g (inv_ne_zero hu)
  have hov' := over_scale 𝔪 hw''g hu huv hw₃v hov
  have hco : ∀ χ', coef s (g' c + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) w₃ χ' =
      u⁻¹ * ((χ (Multiplicative.ofAdd χ') : (FractionRing V)ˣ) : FractionRing V) * coef s (g' c) (w c) χ' := fun χ' =>
    GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd (hc c).2.1 (fun z J hJ => by rw [hw₃v z J hJ, hw''v, cst_eq]) s χ'
  haveI : IsIntegrallyClosed V := 𝔪.cn.2.1
  have hint : ∀ mu : X, ∃ a : V, algebraMap V (FractionRing V) a =
      u⁻¹ * ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) := fun mu => by
    refine IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.mul ?_ ?_)
    · refine IsIntegral.of_pow (n := (X₁.S.r * X₁.S.N) ^ 2 * (X₁.S.r * X₁.S.N) ^ 2) (by positivity) ?_
      rw [inv_pow, hu1, inv_one]
      exact isIntegral_one
    · refine IsIntegral.of_pow hk ?_
      rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχ, MonoidHom.one_apply, Units.val_one]
      exact isIntegral_one
  choose a ha using hint
  refine ⟨fun mu _ => a mu * T mu c, x, fr, th, w₀, s, fun _ => _, fun _ => w₃, hx, hfr, hth, hw₀, hs,
    fun _ => ⟨⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl⟩, hw₃, hov'⟩,
    fun mu _ => ?_⟩
  · obtain ⟨o, ho, ho'⟩ := (hc c).1
    rw [smul_add, ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho, (GlobalTheory.TorusExt.isZero_iff_eq _).1 ho', ← map_nsmul,
      ← ofMul_pow, hχ, ofMul_one, map_zero, add_zero]
  · rw [hco, map_mul, ha, ← hTc, _root_.mul_assoc]

end GlobalTheory.GSep.TermsExt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_exists_terms_torus_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ T' : X → Unit → V, 𝔪.Terms x₀ (fun _ : Unit => lab c + τ) T' := by
  atlas_forward_decl GlobalTheory.GSep.TermsExt.exists_terms_translate
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
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.GSep.TransTerms

theorem sum_terms {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X} (𝔪 : GMem X₁ z₁ act V ev X t δ)
    {C : Type} (lab : C → X₁.S.Gam) (T : X → C → V) (hT : 𝔪.Terms x₀ lab T) (c : C) :
    SumF (maximalIdeal V) (FractionRing V) (fun mu : X => algebraMap V (FractionRing V) (T mu c) *
      𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem (lab c)⟩) := by
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hexp, hg', hTe⟩ := hT
  have hO := (hg' c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hg' c).2.1 th s _ hexp (hth (lab c))
  have := sumF_comp_equiv 𝔪.e₈.toEquiv hO
  convert this using 1
  funext mu
  exact hTe mu c

theorem twistSum_of_transExp {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {x₀ : X₁.S.Gam} (hd : X₁.M.Div X₁.S.th x₀ z₁) (sg : ℤˣ)
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X} (𝔪 : GMem X₁ z₁ act V ev X t δ)
    (hW : ∀ (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), TorChar 𝔪 τ χ →
      ∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) =
        𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))
    {C : Type} (lab : C → X₁.S.Gam) (hlab : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁) (T : X → C → V)
    (hT : 𝔪.Terms x₀ lab T) (c : C) (τ : X₁.S.Gam) (hτ : τ ∈ X₁.S.TT X₁.M z₁) (e : ℕ)
    (hE : TransExp 𝔪 x₀ (lab c) τ e) : TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  obtain ⟨χ, hχ1, hχ2⟩ := GlobalTheory.T.exists_level_killed_char_of_torus_label I X₁ z₁ act V ev X t δ 𝔪 τ hτ
  obtain ⟨T', hT'⟩ := GlobalTheory.T.thetaMember_exists_terms_torus_translate I X₁ z₁ act x₀ hd V ev X t δ 𝔪 C lab hlab T hT c τ hτ
  have hprop := hE χ ⟨hχ1, hχ2⟩ C lab T hT c rfl Unit _ T' hT' () rfl
  have hsum := sumF_const_mul (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)))
    (sum_terms 𝔪 (fun _ : Unit => lab c + τ) T' hT' ())
  refine GlobalTheory.T.twistedAdicSum_terms_of_fractionField_sum I X₁ z₁ act V ev X t δ 𝔪 x₀ C lab T sg c τ χ e
    (GlobalTheory.GSep.TwistModel.yK_th_ne_zero 𝔪 hd) (GlobalTheory.GSep.TwistModel.exists_yy 𝔪) (hW τ χ ⟨hχ1, hχ2⟩) ?_
  convert hsum using 1
  funext mu
  rw [← _root_.mul_assoc, hprop mu, _root_.mul_assoc]

end GlobalTheory.GSep.TransTerms

namespace GlobalTheory.GSep
open GlobalTheory.GSep.TransTerms

theorem twistSum_exp_affine : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∃ ε1 ε2 : X₁.S.Gam → X₁.S.Gam → ℕ, (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ (ε1 (lab c) τ)) ∧ (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y2 → C → V2, 𝔪2.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪2 lab T sg c τ (ε2 (lab c) τ)) ∧ ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((ε1 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((ε2 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  intro I X₁ z₁ act x₀ hd sg _ hW V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ t2 δ2 𝔪2
  classical
  have hA := GlobalTheory.T.thetaMember_torus_translation_exponent_affine I X₁ z₁ act x₀ hd V1 ev1 Y1 t1 δ1 𝔪1 V2 ev2 Y2 t2 δ2 𝔪2
  choose! F1 F2 hF1 hF2 hAff using hA
  refine ⟨fun a τ => F1 τ a, fun a τ => F2 τ a, ?_, ?_, fun τ hτ => hAff τ hτ⟩
  · intro C lab hlab T hT c τ hτ
    exact twistSum_of_transExp hd sg 𝔪1 (fun τ χ hχ => hW V1 ev1 Y1 t1 δ1 𝔪1 τ χ hχ.1 hχ.2) lab hlab T hT c τ hτ _
      (hF1 τ hτ (lab c) (hlab c))
  · intro C lab hlab T hT c τ hτ
    exact twistSum_of_transExp hd sg 𝔪2 (fun τ χ hχ => hW V2 ev2 Y2 t2 δ2 𝔪2 τ χ hχ.1 hχ.2) lab hlab T hT c τ hτ _
      (hF2 τ hτ (lab c) (hlab c))

end GlobalTheory.GSep
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedSum_exponents_differ_affine_two_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (t2 : Y2 → V2) (δ2 : I → Y2 → Y2) (𝔪2 : GlobalTheory.GSep.GMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∃ ε1 ε2 : X₁.S.Gam → X₁.S.Gam → ℕ, (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ (ε1 (lab c) τ)) ∧ (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y2 → C → V2, 𝔪2.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪2 lab T sg c τ (ε2 (lab c) τ)) ∧ ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((ε1 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((ε2 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  atlas_forward_decl GlobalTheory.GSep.twistSum_exp_affine
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
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.WtWd

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qkSub {I : Type} (X₁ : GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y)
    (𝔪 : GMem X₁ z₁ act V ev Y t δ) (p p' : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N))
    (x x' : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A) (hp : p.y = p'.y)
    (hx : QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p x)
    (hx' : QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p' x') :
    ∃ q : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N), q.y = 0 ∧
      QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) q (x * x'⁻¹) := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    have hn := X₁.ρ.n_prime.pos
    rw [hj, X₁.ρ.N_eq]
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hB := 𝔪.D.tau_bimult
  obtain ⟨f, hto, -, -, hadd, -⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk
  have e := (hto p x).1 hx
  have e' := (hto p' x').1 hx'
  have h0 : f (GlobalTheory.TorusExt.qkZero hB _ _) = 1 := by
    have := hadd _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB (GlobalTheory.TorusExt.qkZero hB (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N))
      (GlobalTheory.TorusExt.qkZero hB _ _))
    rw [show GlobalTheory.TorusExt.qkAdd hB (GlobalTheory.TorusExt.qkZero hB (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N))
        (GlobalTheory.TorusExt.qkZero hB _ _) = GlobalTheory.TorusExt.qkZero hB _ _ from
      GlobalTheory.TorusExt.qk_ext (by simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkZero]) (by simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkZero])] at this
    exact left_eq_mul.1 this
  have hneg : f (GlobalTheory.TorusExt.qkNeg hB p') = (f p')⁻¹ := by
    have := hadd _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB p' (GlobalTheory.TorusExt.qkNeg hB p'))
    rw [show GlobalTheory.TorusExt.qkAdd hB p' (GlobalTheory.TorusExt.qkNeg hB p') = GlobalTheory.TorusExt.qkZero hB _ _ from
      GlobalTheory.TorusExt.qk_ext (by simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkNeg, GlobalTheory.TorusExt.qkZero])
        (by simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkNeg, GlobalTheory.TorusExt.qkZero]), h0] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  refine ⟨GlobalTheory.TorusExt.qkAdd hB p (GlobalTheory.TorusExt.qkNeg hB p'), ?_, ?_⟩
  · simp [GlobalTheory.TorusExt.qkAdd, GlobalTheory.TorusExt.qkNeg, hp]
  · rw [hto, hadd _ _ _ (GlobalTheory.TorusExt.qkAdd_qkAdd hB _ _), hneg, e, e']

section
variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {Y : Type} [AddCommGroup Y] {t : Y → V} {δ : I → Y → Y} (𝔪 : GMem X₁ z₁ act V ev Y t δ)

theorem yy_sub {a a' : X₁.S.Gam} {mu : Y} (h : 𝔪.YY a mu) (h' : 𝔪.YY a' mu) : 𝔪.YY (a - a') 0 := by
  obtain ⟨p, x, hp, hx, hxa⟩ := h
  obtain ⟨p', x', hp', hx', hxa'⟩ := h'
  obtain ⟨q, hq, hqx⟩ := qkSub X₁ z₁ act V ev Y t δ 𝔪 p p' x x' (hp.trans hp'.symm) hx hx'
  refine ⟨q, x * x'⁻¹, by rw [hq, map_zero], hqx, ?_⟩
  let T := TFK (R := V) (AlgebraicClosure (FractionRing V))
  have e2 : spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) =
      T.hom ≫ spMap 𝔪.yK := by
    simp [T, spMap, jFK, ← Spec.map_comp]
  let U : Over.mk (T.hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) := Over.homMk (T.hom ≫ spMap 𝔪.yK) (by simp)
  have hU : ∀ (b : X₁.S.Gam) (y : T ⟶ 𝔪.A.A),
      y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt b).left →
      pushHom 𝔪.cart T y = U ≫ X₁.ρ.pt b := fun b y hy => by
    apply Over.OverMorphism.ext
    show y.left ≫ 𝔪.φ = (U ≫ X₁.ρ.pt b).left
    rw [Over.comp_left, hy, e2]
    rfl
  have hpt : X₁.ρ.pt (a - a') = X₁.ρ.pt a * (X₁.ρ.pt a')⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← X₁.ρ.pt_add, sub_add_cancel]
  have key : pushHom 𝔪.cart T (x * x'⁻¹) = U ≫ X₁.ρ.pt (a - a') := by
    rw [map_mul, map_inv, hU a x hxa, hU a' x' hxa', hpt]
    show _ = preHom U _
    rw [map_mul, map_inv]
    rfl
  have e3 := congrArg (fun z => z.left) key
  rw [e2]
  exact e3.trans (Over.comp_left _ _ _ U _)

end

theorem wt_wd : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (sg : ℤˣ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ wt : Y1 → ZMod (X₁.S.r * X₁.S.N), ∀ a mu, 𝔪1.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
  intro I X₁ z₁ act x₀ hD V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 sg τ hτ
  classical
  refine ⟨fun mu => if h : ∃ a, 𝔪1.YY a mu then (sg : ℤ) • eStd X₁.S.g _ τ h.choose else 0, ?_⟩
  intro a mu hY
  have h : ∃ a, 𝔪1.YY a mu := ⟨a, hY⟩
  simp only [dif_pos h]
  congr 1
  have hd := yy_sub 𝔪1 h.choose_spec hY
  have hH : h.choose - a ∈ X₁.S.HH X₁.M z₁ :=
    (GlobalTheory.T.mem_dividingLabels_iff_class_zero I X₁ z₁ act x₀ hD V1 ev1 Y1 t1 δ1 𝔪1 _).2 hd
  have h0 : eStd X₁.S.g _ τ (h.choose - a) = 0 := hτ _ hH
  have hs : eStd X₁.S.g _ τ (h.choose - a) = eStd X₁.S.g _ τ h.choose - eStd X₁.S.g _ τ a := by
    simp only [eStd, Pi.sub_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hs, sub_eq_zero] at h0
  exact h0

end GlobalTheory.GSep.WtWd
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_twist_weight_wellDefined_lattice : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (sg : ℤˣ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ wt : Y1 → ZMod (X₁.S.r * X₁.S.N), ∀ a mu, 𝔪1.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
  atlas_forward_decl GlobalTheory.GSep.WtWd.wt_wd
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
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.ConstTerm

theorem sub_mem_of_sumI {V Ix : Type} [CommRing V] {I : Ideal V} {y : Ix → V} {v : V} (h : SumI I y v) (i₀ : Ix)
    (hy : ∀ j, j ≠ i₀ → y j ∈ I) : v - y i₀ ∈ I := by
  classical
  obtain ⟨N, -, -, -, hS⟩ := h
  obtain ⟨S, hS⟩ := hS 1
  have h1 := Submodule.smul_mono (le_refl (I ^ 1)) (le_top : N ≤ ⊤) (hS (insert i₀ S) (Finset.subset_insert _ _))
  rw [pow_one, smul_eq_mul, Ideal.mul_top, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S)] at h1
  have h2 : ∑ j ∈ (insert i₀ S).erase i₀, y j ∈ I :=
    Submodule.sum_mem _ fun j hj => hy j (Finset.ne_of_mem_erase hj)
  have := add_mem h1 h2
  convert this using 1
  ring

theorem const_term_sub_mem : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (r : X₁.M.Z.presheaf.stalk z₁), X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ → ev1 r - T 0 c ∈ maximalIdeal V1 := by
  intro I X₁ z₁ act x₀ hd V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT c r hr
  haveI : IsNoetherianRing V := 𝔪.cn.1
  haveI : IsLocalHom ev := 𝔪.loc
  have hθ : 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := GlobalTheory.GSep.TwistModel.yK_th_ne_zero 𝔪 hd
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (lab c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1, ← hr, GlobalTheory.GSep.TwistModel.val_stalkHom] at e
  have e' : 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ =
      algebraMap V (FractionRing V) (ev r) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    rw [𝔪.yK_eq, 𝔪.yK_eq]
    exact e
  have hS := GlobalTheory.GSep.MemberModel.terms_sum 𝔪 hT c
  rw [e'] at hS
  have hI := GlobalTheory.Poinc.TwistSum₂.sumI_of_sumF_mul (fun χ => T (𝔪.e₈.symm χ) c) (ev r) _ hθ hS
  have := sub_mem_of_sumI hI 0 fun j hj =>
    GlobalTheory.T.thetaMember_term_nonzero_index_mem_maximalIdeal I X₁ z₁ act x₀ hd V ev X t δ 𝔪 C lab hlab T hT c _ (𝔪.e₈.symm.map_ne_zero_iff.2 hj)
  simpa only [map_zero] using this

end GlobalTheory.GSep.ConstTerm
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_index_zero_term_eq_theta_ratio_mod : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (r : X₁.M.Z.presheaf.stalk z₁), X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ → ev1 r - T 0 c ∈ maximalIdeal V1 := by
  atlas_forward_decl GlobalTheory.GSep.ConstTerm.const_term_sub_mem
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
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.GSep.TwistResid

theorem twist_resid : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), lab c ∈ X₁.S.supI X₁.M z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ (sg : ℤˣ) (e : ℕ), GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ e → ∀ s u : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) → X₁.M.stalkHom z₁ u = X₁.S.th (lab c + τ) / X₁.S.th (lab c) → ev1 (s * u) - 1 ∈ maximalIdeal V1 := by
  classical
  intro I X₁ z₁ act x₀ hx₀ V _ _ _ ev Y _ t δ 𝔪 C lab hlab T hT c hc τ hτ sg e hTw s u hs hu
  have hcd : X₁.M.Div X₁.S.th (lab c) z₁ := hc
  have hqO : X₁.S.th (lab c) / X₁.S.th x₀ ∈ X₁.M.O z₁ := hx₀.2 (lab c)
  let r := (X₁.M.stalkEquiv z₁).symm ⟨_, hqO⟩
  have hr : X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ := by
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  have hrU : IsUnit r := ((RatModel.isUnit_O_iff (⟨_, hqO⟩ : X₁.M.O z₁)).2
    ⟨div_ne_zero hcd.1 hx₀.1, by rw [inv_div]; exact hcd.2 x₀⟩).map (X₁.M.stalkEquiv z₁).symm
  obtain ⟨zt, hzt⟩ : ∃ zt : X₁.M.Z.presheaf.stalk z₁,
      X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) := by
    obtain ⟨s', hs'⟩ := (X₁.M.stalkEquiv z₁).surjective
      ⟨algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)), Subalgebra.algebraMap_mem _ _⟩
    exact ⟨s', by rw [← RatModel.coe_stalkEquiv, hs']⟩
  obtain ⟨wt, hwt⟩ := GlobalTheory.T.thetaMember_twist_weight_wellDefined_lattice I X₁ z₁ act x₀ hx₀ V ev Y t δ 𝔪 sg τ hτ
  let wt' : Y → ZMod (X₁.S.r * X₁.S.N) := fun mu => if mu = 0 then 0 else wt mu
  have hwt' : ∀ a mu, 𝔪.YY a mu → wt' mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
    intro a mu h
    by_cases h0 : mu = 0
    · subst h0
      have ha : a ∈ X₁.S.HH X₁.M z₁ := (GlobalTheory.T.mem_dividingLabels_iff_class_zero I X₁ z₁ act x₀ hx₀ V ev Y t δ 𝔪 a).2 h
      have h1 : eStd X₁.S.g _ τ a = 0 := hτ a ha
      simp only [wt', if_pos rfl, h1, smul_zero]
    · simp only [wt', if_neg h0]
      exact hwt a mu h
  have hh : X₁.M.stalkHom z₁ (s * u * r) = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) * X₁.S.th (lab c + τ) / X₁.S.th x₀ := by
    rw [map_mul, map_mul, hs, hu, hr]
    field_simp [hcd.1, hx₀.1]
  obtain ⟨N, -, -, -, hN⟩ := hTw zt (s * u * r) hzt hh wt' hwt'
  obtain ⟨S, hS⟩ := hN 1
  have h1 := hS (insert 0 S) (Finset.subset_insert _ _)
  have hle : maximalIdeal V ^ 1 • N ≤ (maximalIdeal V : Submodule V V) :=
    Submodule.smul_le.2 fun a ha b _ => by
      rw [smul_eq_mul]; exact Ideal.mul_mem_right b _ (by simpa using ha)
  have h2 := hle h1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self 0 S)] at h2
  have h3 : ∑ mu ∈ (insert 0 S).erase 0, ev zt ^ (wt' mu).val * T mu c ∈ maximalIdeal V :=
    Ideal.sum_mem _ fun mu hmu => Ideal.mul_mem_left _ _
      (GlobalTheory.T.thetaMember_term_nonzero_index_mem_maximalIdeal I X₁ z₁ act x₀ hx₀ V ev Y t δ 𝔪 C lab hlab T hT c mu (Finset.ne_of_mem_erase hmu))
  have h0 : ev zt ^ (wt' 0).val * T 0 c = T 0 c := by simp [wt']
  rw [h0] at h2
  have h4 : ev (s * u * r) - T 0 c ∈ maximalIdeal V := by
    have := Ideal.add_mem _ h2 h3
    simpa [sub_add_eq_sub_sub, sub_add_cancel] using this
  have h5 := GlobalTheory.T.thetaMember_index_zero_term_eq_theta_ratio_mod I X₁ z₁ act x₀ hx₀ V ev Y t δ 𝔪 C lab hlab T hT c r hr
  have h6 : (ev (s * u) - 1) * ev r ∈ maximalIdeal V := by
    have := Ideal.sub_mem _ h4 h5
    rw [map_mul] at this
    convert this using 1; ring
  exact (Ideal.mul_unit_mem_iff_mem _ (hrU.map ev)).1 h6

end GlobalTheory.GSep.TwistResid
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), lab c ∈ X₁.S.supI X₁.M z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ (sg : ℤˣ) (e : ℕ), GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ e → ∀ s u : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) → X₁.M.stalkHom z₁ u = X₁.S.th (lab c + τ) / X₁.S.th (lab c) → ev1 (s * u) - 1 ∈ maximalIdeal V1 := by
  atlas_forward_decl GlobalTheory.GSep.TwistResid.twist_resid
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
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.SupISymm

theorem exists_unit_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    {c ε : Ω} (hc : c ^ 2 = 1) (hε : ε ^ ((S.r * S.N) ^ 2) = 1) : ∃ u : oˣ, c * ε = algebraMap o Ω (u : o) := by
  have hinj : Function.Injective (algebraMap o Ω) := ArithBase.inj
  have hp : IsPrimitiveRoot (algebraMap o Ω S.ζ) ((S.r * S.N) ^ 2) := S.prim.map_of_injective hinj
  have hpos : 0 < (S.r * S.N) ^ 2 := by
    have := S.N_ge; have := S.r_pos; positivity
  obtain ⟨k, -, hk⟩ := hp.eq_pow_of_pow_eq_one hε
  have hζu : IsUnit S.ζ := S.prim.isUnit hpos.ne'
  have hc' : c = 1 ∨ c = -1 := by
    have : c * c = 1 := by rw [← sq]; exact hc
    exact mul_self_eq_one_iff.1 this
  rcases hc' with rfl | rfl
  · exact ⟨(hζu.unit) ^ k, by simp [← hk, map_pow]⟩
  · exact ⟨-(hζu.unit) ^ k, by simp [← hk, map_pow]⟩

theorem exists_unit_th_neg {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a) (a : S.Gam) :
    ∃ u : oˣ, S.th (-a) = algebraMap o Ω (u : o) * S.th a := by
  obtain ⟨c, ε, hc, hε, h⟩ := H a
  obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one S hc hε
  exact ⟨u, by rw [h, hu]⟩

theorem neg_mem_supI_of_parity {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a)
    (z : M.Z) (a : S.Gam) (ha : a ∈ S.supI M z) : -a ∈ S.supI M z := by
  obtain ⟨hne, hdiv⟩ := ha
  obtain ⟨u, hu⟩ := exists_unit_th_neg S H a
  have hu0 : algebraMap o Ω (u : o) ≠ 0 := by
    intro h0
    have h1 : algebraMap o Ω ((u : o) * ((u⁻¹ : oˣ) : o)) = 1 := by simp
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨by rw [hu]; exact mul_ne_zero hu0 hne, fun j => ?_⟩
  obtain ⟨v, hv⟩ := exists_unit_th_neg S H (-j)
  rw [neg_neg] at hv
  have key : S.th j / S.th (-a) = algebraMap o Ω ((v : o) * ((u⁻¹ : oˣ) : o)) * (S.th (-j) / S.th a) := by
    have hi : algebraMap o Ω ((u⁻¹ : oˣ) : o) = (algebraMap o Ω (u : o))⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)
    rw [hv, hu, map_mul, hi]
    field_simp
  rw [key]
  exact (M.O z).mul_mem (Subalgebra.algebraMap_mem _ _) (hdiv (-j))

end GlobalTheory.GSep.SupISymm

open GlobalTheory.GSep.SupISymm in

theorem GlobalTheory.GSep.neg_mem_supI : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → -a ∈ X₁.S.supI X₁.M z₁ := by
  intro X₁ z₁ a ha
  exact neg_mem_supI_of_parity X₁.S X₁.M (fun a => GlobalTheory.ThetaParity.theta_neg X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ a) z₁ a ha
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_mem_dividingLabels_thetaSystem : ∀ (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → -a ∈ X₁.S.supI X₁.M z₁ := by
  atlas_forward_decl GlobalTheory.GSep.neg_mem_supI
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
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep.TwistIndep

theorem isUnit_one_sub_pow {o : Type} [CommRing o] [IsDomain o] {ζ : o} {M : ℕ} (hζ : IsPrimitiveRoot ζ M)
    (hM : IsUnit (M : o)) {d : ℕ} (hd : ζ ^ d ≠ 1) : IsUnit (1 - ζ ^ d) := by
  have hη : (ζ ^ d) ^ M = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hsum : ∑ k ∈ Finset.range M, (ζ ^ d) ^ k = 0 := by
    have h := mul_geom_sum (ζ ^ d) M
    rw [hη, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hd)
  have hdiv : (1 - ζ ^ d) ∣ (M : o) := by
    have h : (M : o) = ∑ k ∈ Finset.range M, (1 - (ζ ^ d) ^ k) := by
      rw [Finset.sum_sub_distrib, hsum]; simp
    rw [h]
    exact Finset.dvd_sum fun k _ => by simpa using sub_dvd_pow_sub_pow (1 : o) (ζ ^ d) k
  exact isUnit_of_dvd_unit hdiv hM

theorem mem_maximalIdeal_of_map {R V : Type} [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V]
    (ev : R →+* V) {x : R} (h : ev x ∈ maximalIdeal V) : x ∈ maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h ⊢
  exact fun hu => h (hu.map ev)

theorem stalk_of_base (X₁ : GSet) (z₁ : X₁.M.Z) (a : X₁.o₁) :
    ∃ s : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ a := by
  obtain ⟨s, hs⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨algebraMap X₁.o₁ X₁.Ω₁ a, Subalgebra.algebraMap_mem _ a⟩
  exact ⟨s, by rw [← RatModel.coe_stalkEquiv, hs]⟩

theorem stalk_isUnit (X₁ : GSet) (z₁ : X₁.M.Z) {s : X₁.M.Z.presheaf.stalk z₁} {x : X₁.o₁}
    (hs : X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ x) (hx : IsUnit x) : IsUnit s := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨t, ht⟩ := stalk_of_base X₁ z₁ y
  refine IsUnit.of_mul_eq_one t (X₁.M.stalkHom_injective z₁ ?_)
  rw [map_mul, hs, ht, ← map_mul, hy, map_one, map_one]

theorem pow_eq_of_sub_mem (X₁ : GSet) (z₁ : X₁.M.Z) {s₁ s₂ : X₁.M.Z.presheaf.stalk z₁} {e₁ e₂ : ℕ}
    (h₁ : X₁.M.stalkHom z₁ s₁ = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e₁))
    (h₂ : X₁.M.stalkHom z₁ s₂ = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e₂))
    (hm : s₁ - s₂ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁)) : X₁.S.ζ ^ e₁ = X₁.S.ζ ^ e₂ := by
  haveI : IsDomain X₁.o₁ := by haveI := X₁.ar.ded; infer_instance
  by_contra hne
  obtain ⟨M, hM⟩ : ∃ M, M = (X₁.S.r * X₁.S.N) ^ 2 := ⟨_, rfl⟩
  have hζ : IsPrimitiveRoot X₁.S.ζ M := hM ▸ X₁.S.prim
  have hM0 : M ≠ 0 := by
    rw [hM]; exact pow_ne_zero _ (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  have hMu : IsUnit (M : X₁.o₁) := by rw [hM, Nat.cast_pow]; exact X₁.S.unit.pow 2
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  have hd : X₁.S.ζ ^ e₂ * X₁.S.ζ ^ (e₁ + k * e₂) = X₁.S.ζ ^ e₁ := by
    have h1 : e₂ + (e₁ + k * e₂) = e₁ + M * e₂ := by rw [hk, Nat.succ_eq_add_one]; ring
    rw [← pow_add, h1, pow_add, pow_mul, hζ.pow_eq_one, one_pow, _root_.mul_one]
  have hd1 : X₁.S.ζ ^ (e₁ + k * e₂) ≠ 1 := fun h => hne (by rw [← hd, h, _root_.mul_one])
  have hu : IsUnit (X₁.S.ζ ^ e₁ - X₁.S.ζ ^ e₂) := by
    have h3 : X₁.S.ζ ^ e₁ - X₁.S.ζ ^ e₂ = -(X₁.S.ζ ^ e₂ * (1 - X₁.S.ζ ^ (e₁ + k * e₂))) := by
      rw [← hd]; ring
    rw [h3]
    exact ((((hζ.isUnit hM0).pow e₂).mul (isUnit_one_sub_pow hζ hMu hd1))).neg
  have hs : IsUnit (s₁ - s₂) := stalk_isUnit X₁ z₁ (by rw [map_sub, h₁, h₂, map_sub]) hu
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  exact hm hs

theorem pow_eq_iff_cast (X₁ : GSet) (a b : ℕ) :
    X₁.S.ζ ^ a = X₁.S.ζ ^ b ↔ (a : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = (b : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) := by
  have hpos : 0 < (X₁.S.r * X₁.S.N) ^ 2 :=
    pow_pos (Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)) 2
  have hord := X₁.S.prim.eq_orderOf
  rw [ZMod.natCast_eq_natCast_iff']
  constructor
  · intro h
    apply X₁.S.prim.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
    rw [hord, pow_mod_orderOf, pow_mod_orderOf]
    exact h
  · intro h
    calc X₁.S.ζ ^ a = X₁.S.ζ ^ (a % orderOf X₁.S.ζ) := (pow_mod_orderOf _ _).symm
      _ = X₁.S.ζ ^ (b % orderOf X₁.S.ζ) := by rw [← hord, h]
      _ = X₁.S.ζ ^ b := pow_mod_orderOf _ _

theorem affine_zero {G : Type} [AddCommGroup G] {M : ℕ} (hM : Odd M) (S : Set G) (hS : ∀ s ∈ S, -s ∈ S)
    (hne : S.Nonempty) (κ : ZMod M) (h : AddSubgroup.closure S →+ ZMod M)
    (hz : ∀ s (hs : s ∈ S), κ + h ⟨s, AddSubgroup.subset_closure hs⟩ = 0) :
    ∀ a (ha : a ∈ AddSubgroup.closure S), κ + h ⟨a, ha⟩ = 0 := by
  obtain ⟨s₀, hs₀⟩ := hne
  have h1 := hz s₀ hs₀
  have h2 := hz (-s₀) (hS s₀ hs₀)
  have hneg : (⟨-s₀, AddSubgroup.subset_closure (hS s₀ hs₀)⟩ : AddSubgroup.closure S) =
      -⟨s₀, AddSubgroup.subset_closure hs₀⟩ := rfl
  rw [hneg, map_neg] at h2
  have h2κ : (2 : ZMod M) * κ = 0 := by linear_combination h1 + h2
  have hcop : Nat.Coprime 2 M := (Nat.coprime_two_left).2 hM
  have hκ : κ = 0 := by
    have hu : IsUnit (2 : ZMod M) := by
      have := (ZMod.unitOfCoprime 2 hcop).isUnit
      rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
    exact hu.mul_right_eq_zero.1 h2κ
  subst hκ
  intro a ha
  rw [zero_add]
  refine AddSubgroup.closure_induction (p := fun x hx => h ⟨x, hx⟩ = 0) (fun x hx => ?_) ?_
    (fun x y hx hy h1 h2 => ?_) (fun x hx h1 => ?_) ha
  · simpa using hz x hx
  · exact map_zero h
  · have : (⟨x + y, add_mem hx hy⟩ : AddSubgroup.closure S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, h1, h2, add_zero]
  · have : (⟨-x, neg_mem hx⟩ : AddSubgroup.closure S) = -⟨x, hx⟩ := rfl
    rw [this, map_neg, h1, neg_zero]

end GlobalTheory.GSep.TwistIndep

namespace GlobalTheory.GSep
open GlobalTheory.GSep.TwistIndep

theorem twistSum_indep : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (Y₁ : Type) [AddCommGroup Y₁] (t₁ : Y₁ → V₁) (δ₁ : I → Y₁ → Y₁) (𝔪₁ : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁) (C₁ : Type) (lab₁ : C₁ → X₁.S.Gam), (∀ c, lab₁ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₁ : Y₁ → C₁ → V₁, 𝔪₁.Terms x₀ lab₁ T₁ → ∀ c₁ : C₁, ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (Y₂ : Type) [AddCommGroup Y₂] (t₂ : Y₂ → V₂) (δ₂ : I → Y₂ → Y₂) (𝔪₂ : GlobalTheory.GSep.GMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂) (C₂ : Type) (lab₂ : C₂ → X₁.S.Gam), (∀ c, lab₂ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₂ : Y₂ → C₂ → V₂, 𝔪₂.Terms x₀ lab₂ T₂ → ∀ c₂ : C₂, lab₁ c₁ = lab₂ c₂ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e₁ e₂ : ℕ, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₁ lab₁ T₁ sg c₁ τ e₁ → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₂ → (∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab₁ c₁ + τ) / X₁.S.th x₀ ∧ ev₁ r ≠ 0) → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₁ := by
  intro I X₁ z₁ act x₀ hdiv sg hsg hW V₁ _ _ _ ev₁ Y₁ _ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁
    V₂ _ _ _ ev₂ Y₂ _ t₂ δ₂ 𝔪₂ C₂ lab₂ hlab₂ T₂ hT₂ c₂ hlab τ hτ e₁ e₂ hS₁ _ hr'
  obtain ⟨r, hr, hr0⟩ := hr'
  obtain ⟨ε₁, ε₂, h1, h2, haff⟩ := GlobalTheory.T.twistedSum_exponents_differ_affine_two_members I X₁ z₁ act x₀ hdiv sg hsg hW V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ V₂ ev₂ Y₂ t₂ δ₂ 𝔪₂

  have hφ : ∀ b ∈ X₁.S.HH X₁.M z₁, X₁.S.ζ ^ ε₁ b τ = X₁.S.ζ ^ ε₂ b τ := by
    obtain ⟨κ, h, hκ⟩ := haff τ hτ
    have hsup : ∀ s (hs : s ∈ X₁.S.supI X₁.M z₁), κ + h ⟨s, AddSubgroup.subset_closure hs⟩ = 0 := by
      intro s hs
      have hsH : s ∈ X₁.S.HH X₁.M z₁ := AddSubgroup.subset_closure hs
      obtain ⟨U₁, hU₁⟩ := GlobalTheory.T.thetaMember_exists_terms_dividing_group_label I X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ s hsH
      obtain ⟨U₂, hU₂⟩ := GlobalTheory.T.thetaMember_exists_terms_dividing_group_label I X₁ z₁ act x₀ hdiv V₂ ev₂ Y₂ t₂ δ₂ 𝔪₂ s hsH
      have hw₁ := h1 Unit (fun _ => s) (fun _ => hsH) U₁ hU₁ () τ hτ
      have hw₂ := h2 Unit (fun _ => s) (fun _ => hsH) U₂ hU₂ () τ hτ
      obtain ⟨q₁, hq₁⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ ε₁ s τ)
      obtain ⟨q₂, hq₂⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ ε₂ s τ)
      obtain ⟨u, hu⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨_, hs.2 (s + τ)⟩
      have hu' : X₁.M.stalkHom z₁ u = X₁.S.th (s + τ) / X₁.S.th s := by rw [← RatModel.coe_stalkEquiv, hu]
      have r₁ := GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label I X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ Unit (fun _ => s) (fun _ => hsH) U₁ hU₁ ()
        hs τ hτ sg _ hw₁ q₁ u hq₁ hu'
      have r₂ := GlobalTheory.T.twistedSum_zeta_power_residue_dividing_label I X₁ z₁ act x₀ hdiv V₂ ev₂ Y₂ t₂ δ₂ 𝔪₂ Unit (fun _ => s) (fun _ => hsH) U₂ hU₂ ()
        hs τ hτ sg _ hw₂ q₂ u hq₂ hu'
      have m₁' : q₁ * u - 1 ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
        mem_maximalIdeal_of_map ev₁ (by rwa [map_sub, map_one])
      have m₂' : q₂ * u - 1 ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
        mem_maximalIdeal_of_map ev₂ (by rwa [map_sub, map_one])
      have hunit : IsUnit u := by
        have hqu : IsUnit (q₁ * u) := by
          by_contra hn
          have hmem : q₁ * u ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := (IsLocalRing.mem_maximalIdeal _).2 hn
          have h1m : (1 : X₁.M.Z.presheaf.stalk z₁) ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := by
            simpa using sub_mem hmem m₁'
          exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1m)
        exact isUnit_of_mul_isUnit_right hqu
      have hdiff : (q₁ - q₂) * u ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := by
        have h3 := sub_mem m₁' m₂'
        rwa [show q₁ * u - 1 - (q₂ * u - 1) = (q₁ - q₂) * u by ring] at h3
      have hq : q₁ - q₂ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := by
        obtain ⟨v, hv⟩ := hunit.exists_right_inv
        have h4 := Ideal.mul_mem_right v _ hdiff
        rwa [_root_.mul_assoc, hv, _root_.mul_one] at h4
      have heq := (pow_eq_iff_cast X₁ _ _).1 (pow_eq_of_sub_mem X₁ z₁ hq₁ hq₂ hq)
      rw [← hκ s hsH, heq, sub_self]
    have hodd : Odd ((X₁.S.r * X₁.S.N) ^ 2) := by
      have h5 : Odd (X₁.S.r * X₁.S.N) := by
        obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
        rw [hj, X₁.ρ.N_eq]
        exact X₁.ρ.n_odd.pow.mul X₁.ρ.n_odd.pow.pow
      exact h5.pow
    have hz := affine_zero hodd (X₁.S.supI X₁.M z₁) (GlobalTheory.T.neg_mem_dividingLabels_thetaSystem X₁ z₁) ⟨x₀, hdiv⟩ κ h hsup
    intro b hb
    rw [pow_eq_iff_cast, ← sub_eq_zero, hκ b hb]
    exact hz b hb

  obtain ⟨zt, hzt⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))
  obtain ⟨wt, hwt⟩ := GlobalTheory.T.thetaMember_twist_weight_wellDefined_lattice I X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ sg τ hτ
  obtain ⟨s₁, hs₁⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ e₁)
  obtain ⟨s₀, hs₀⟩ := stalk_of_base X₁ z₁ (X₁.S.ζ ^ ε₁ (lab₁ c₁) τ)
  have hA := hS₁ zt (s₁ * r) hzt (by rw [map_mul, hs₁, hr, mul_div_assoc]) wt hwt
  have hB := h1 C₁ lab₁ hlab₁ T₁ hT₁ c₁ τ hτ zt (s₀ * r) hzt (by rw [map_mul, hs₀, hr, mul_div_assoc]) wt hwt
  haveI : IsNoetherianRing V₁ := 𝔪₁.cn.1
  have hE := GlobalTheory.AdicSum.sumI_unique (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hA hB
  rw [map_mul, map_mul] at hE
  have hE' : ev₁ s₁ = ev₁ s₀ := mul_right_cancel₀ hr0 hE
  have hm : s₁ - s₀ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
    mem_maximalIdeal_of_map ev₁ (by rw [map_sub, hE', sub_self]; exact zero_mem _)
  have hpe : X₁.S.ζ ^ e₁ = X₁.S.ζ ^ ε₁ (lab₁ c₁) τ := pow_eq_of_sub_mem X₁ z₁ hs₁ hs₀ hm

  have hpe2 : X₁.S.ζ ^ ε₂ (lab₂ c₂) τ = X₁.S.ζ ^ e₁ := by
    rw [hpe, ← hlab]
    exact (hφ _ (hlab₁ c₁)).symm
  have hF := h2 C₂ lab₂ hlab₂ T₂ hT₂ c₂ τ hτ
  intro zt' h' hzt' hh' wt' hwt'
  exact hF zt' h' hzt' (by rw [hpe2]; exact hh') wt' hwt'

end GlobalTheory.GSep
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaSum_zeta_exponent_indep_of_member : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, GlobalTheory.GSep.TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (Y₁ : Type) [AddCommGroup Y₁] (t₁ : Y₁ → V₁) (δ₁ : I → Y₁ → Y₁) (𝔪₁ : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁) (C₁ : Type) (lab₁ : C₁ → X₁.S.Gam), (∀ c, lab₁ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₁ : Y₁ → C₁ → V₁, 𝔪₁.Terms x₀ lab₁ T₁ → ∀ c₁ : C₁, ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (Y₂ : Type) [AddCommGroup Y₂] (t₂ : Y₂ → V₂) (δ₂ : I → Y₂ → Y₂) (𝔪₂ : GlobalTheory.GSep.GMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂) (C₂ : Type) (lab₂ : C₂ → X₁.S.Gam), (∀ c, lab₂ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₂ : Y₂ → C₂ → V₂, 𝔪₂.Terms x₀ lab₂ T₂ → ∀ c₂ : C₂, lab₁ c₁ = lab₂ c₂ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e₁ e₂ : ℕ, GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₁ lab₁ T₁ sg c₁ τ e₁ → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₂ → (∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab₁ c₁ + τ) / X₁.S.th x₀ ∧ ev₁ r ≠ 0) → GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₁ := by
  atlas_forward_decl GlobalTheory.GSep.twistSum_indep
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

noncomputable section

theorem GlobalTheory.GSep.exists_stalk_zeta (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (a : X₁.o₁) :
    ∃ s : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ a := by
  obtain ⟨s, hs⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨algebraMap X₁.o₁ X₁.Ω₁ a, Subalgebra.algebraMap_mem _ a⟩
  exact ⟨s, by rw [← RatModel.coe_stalkEquiv, hs]⟩

theorem GlobalTheory.GSep.twistSum_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : X → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h) := by
  intro I X₁ z₁ act x₀ hdiv
  obtain ⟨sg, hsg, hweil⟩ := GlobalTheory.T.exists_twisted_theta_sum_common_sign_member I X₁ z₁ act x₀ hdiv
  classical
  let Wit : X₁.S.Gam → X₁.S.Gam → ℕ → Prop := fun a τ e =>
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V)
      (X : Type) (_ : AddCommGroup X) (t : X → V) (δ : I → X → X)
      (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (_ : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁)
      (T : X → C → V) (_ : 𝔪.Terms x₀ lab T) (c : C), lab c = a ∧
      GlobalTheory.GSep.TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e ∧
      ∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab c + τ) / X₁.S.th x₀ ∧ ev r ≠ 0
  refine ⟨sg, fun a τ => if h : ∃ e, Wit a τ e then h.choose else 0, ?_⟩
  intro V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT c τ hτ zt h hzt hh wt hwt
  obtain ⟨e₂, he₂⟩ := hsg V ev X t δ 𝔪 C lab hlab T hT c τ hτ
  by_cases hW : ∃ e, Wit (lab c) τ e
  · beta_reduce at hh
    rw [dif_pos hW] at hh
    obtain ⟨V₁, _, _, _, ev₁, Y₁, _, t₁, δ₁, 𝔪₁, C₁, lab₁, hlab₁, T₁, hT₁, c₁, hc₁, hts, r, hr, hr0⟩ := hW.choose_spec
    have key := GlobalTheory.T.twistedThetaSum_zeta_exponent_indep_of_member I X₁ z₁ act x₀ hdiv sg hsg hweil V₁ ev₁ Y₁ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁
      V ev X t δ 𝔪 C lab hlab T hT c hc₁ τ hτ _ e₂ hts he₂ ⟨r, hr, hr0⟩
    exact key zt h hzt hh wt hwt
  · beta_reduce at hh
    rw [dif_neg hW] at hh
    have hh' : X₁.M.stalkHom z₁ h = X₁.S.th (lab c + τ) / X₁.S.th x₀ := by rw [hh]; simp
    have hev : ev h = 0 := by
      by_contra hne
      exact hW ⟨e₂, V, inferInstance, inferInstance, inferInstance, ev, X, inferInstance, t, δ, 𝔪, C, lab, hlab, T, hT, c,
        rfl, he₂, h, hh', hne⟩
    obtain ⟨s, hs⟩ := GlobalTheory.GSep.exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ e₂)
    have := he₂ zt (s * h) hzt (by rw [map_mul, hs, hh', mul_div_assoc]) wt hwt
    rw [map_mul, hev, mul_zero] at this
    rwa [hev]
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
theorem _root_.GlobalTheory.T.thetaConstants_translate_eq_twisted_sums : (∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : X → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h)) := by
  atlas_forward_decl GlobalTheory.GSep.twistSum_translate
end
