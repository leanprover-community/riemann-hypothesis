import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelPersistsThetaSetupTower

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.DeepDiv

theorem yK_th_ne_zero {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
    (hd : X₁.M.Div X₁.S.th x₀ z₁) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V}
    {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ) :
    𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  obtain ⟨a, ha⟩ := GlobalTheory.ThetaGeneric.exists_th_ne_zero hL.1 hL.2.1 _ _ X₁.S X₁.ρ (FractionRing V) 𝔪.yK
  intro h0
  apply ha
  set y := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy
  have hs : y (closedPoint (FractionRing V)) ⤳ z₁ := by
    have : y (closedPoint (FractionRing V)) ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hw : ∀ w, y w ⤳ y (closedPoint (FractionRing V)) := fun w => by
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) w (closedPoint _)]
  have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hd.1).symm
  rw [𝔪.yK_eq] at h0 ⊢
  change X₁.M.val y (X₁.S.th a) = 0
  change X₁.M.val y (X₁.S.th x₀) = 0 at h0
  rw [e, RatModel.val_mul hw ((hd.of_specializes hs).2 a) (𝔪.reg _ (X₁.S.th_mem x₀)), h0, mul_zero]


end GlobalTheory.Poinc.Sep.DeepDiv

open GlobalTheory.Poinc.Sep

theorem GlobalTheory.Poinc.Sep.DeepDiv.div_lam : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ :=
  GlobalTheory.T.dividingLabel_persists_thetaSetupTower
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
theorem _root_.GlobalTheory.T.dividingLabel_stays_dividing_deeper_model : (∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂) := by
  atlas_forward_decl GlobalTheory.Poinc.Sep.DeepDiv.div_lam
