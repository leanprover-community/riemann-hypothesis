import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRigFr

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.RayHoriz
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayRos

section Series

variable {S : Type} [CommRing S] {ρ κ : Type}

def bil [Fintype ρ] (A : ρ → ρ → S) : MvPowerSeries (Fin 2 × ρ) S :=
  ∑ r, ∑ s, MvPowerSeries.C (A r s) * MvPowerSeries.X ((0 : Fin 2), r) * MvPowerSeries.X ((1 : Fin 2), s)

def quad [Fintype ρ] (B : ρ → ρ → S) : MvPowerSeries ρ S :=
  ∑ r, ∑ s, MvPowerSeries.C (B r s) * MvPowerSeries.X r * MvPowerSeries.X s

def qexp [Algebra ℚ S] (q : MvPowerSeries κ S) : MvPowerSeries κ S :=
  PowerSeries.subst q (PowerSeries.exp S)

end Series

section Ratio

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ] (L : LB G.left) {O : Type} [CommRing O]

def ratio6 (bar : O → O) (ch : ρ → O →+* S) {x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G} (e : Fr x0 L x) (c : O) (m : ℕ)
    (y : (overAt x0 (Jet S (Fin 2 × ρ) m)).left)
    (J : ((overAt x0 (Jet S (Fin 2 × ρ) m)).left ⟶ G.left) → L.ι) :
    ((overAt x0 (Jet S (Fin 2 × ρ) m)).left.presheaf.stalk y)ˣ :=
  ev x0 L e ![fun r => ch r c, fun _ => 1] m y J * (ev x0 L e ![fun r => ch r c, fun _ => 0] m y J)⁻¹ *
    (ev x0 L e ![fun _ => 0, fun _ => 1] m y J)⁻¹ * (ev x0 L e ![fun _ => 1, fun r => ch r (bar c)] m y J)⁻¹ *
    ev x0 L e ![fun _ => 1, fun _ => 0] m y J * ev x0 L e ![fun _ => 0, fun r => ch r (bar c)] m y J

def IsBilRatio [Algebra ℚ S] (a : OAct O G) (bar : O → O) (ch : ρ → O →+* S) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G)
    (e : Fr x0 L x) (c : O) (A : ρ → ρ → S)
    (w : LB.Gen (LB.LinComb L (rosatiφ G (a.act c) (a.act (bar c))) rosatiε)) : Prop :=
  w.IsGen ∧ (∀ y J, Good L y J → val w (zero2 G) y J = 1) ∧
    ∀ m y J, Good L y J → (val w (pt2 x0 x m).left y J).val * gs (𝟙 _) y ⊤ (toΓ _ (psJet m (qexp (bil A)))) =
      (ratio6 x0 L bar ch e c m y J).val

end Ratio

end GlobalTheory.RayRos
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.RayHoriz GlobalTheory.RayRos
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayRosEx

section Series

variable {S : Type} [CommRing S] {ρ : Type}

def ser3 (M : Fin 2 → Fin 3 → S) (F : MvPowerSeries (Fin 2 × ρ) S) : MvPowerSeries (Fin 3 × ρ) S :=
  MvPowerSeries.subst
    (fun p : Fin 2 × ρ => ∑ i : Fin 3, MvPowerSeries.C (M p.1 i) * MvPowerSeries.X (i, p.2)) F

def LawL (F : MvPowerSeries (Fin 2 × ρ) S) : Prop :=
  ser3 ![![1, 1, 0], ![0, 0, 1]] F = ser3 ![![1, 0, 0], ![0, 0, 1]] F * ser3 ![![0, 1, 0], ![0, 0, 1]] F

def LawR (F : MvPowerSeries (Fin 2 × ρ) S) : Prop :=
  ser3 ![![1, 0, 0], ![0, 1, 1]] F = ser3 ![![1, 0, 0], ![0, 1, 0]] F * ser3 ![![1, 0, 0], ![0, 0, 1]] F

end Series

section Ratio

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ] (L : LB G.left) {O : Type} [CommRing O]

def IsRatioSer (bar : O → O) (ch : ρ → O →+* S) {x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G} (e : Fr x0 L x) (c : O)
    {φ : Fin 6 → ((G ⊗ G).left ⟶ G.left)} (w : LB.Gen (LB.LinComb L φ rosatiε))
    (F : MvPowerSeries (Fin 2 × ρ) S) : Prop :=
  ∀ m y J, Good L y J → (val w (pt2 x0 x m).left y J).val * gs (𝟙 _) y ⊤ (toΓ _ (psJet m F)) =
    (ratio6 x0 L bar ch e c m y J).val

end Ratio

end GlobalTheory.RayRosEx
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.RayHoriz
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayRosEx

section Weights

variable {S : Type} [CommRing S] {ρ : Type}

def mixW (M : Fin 2 → Fin 3 → S) (W : Fin 2 → ρ → S) : Fin 3 → ρ → S := fun i r => ∑ k, M k i * W k r

def rat3 {U : Type} [CommGroup U] (E : (Fin 3 → ρ → S) → U) (α β : ρ → S) (M : Fin 2 → Fin 3 → S) : U :=
  E (mixW M ![α, fun _ => 1]) * (E (mixW M ![α, fun _ => 0]))⁻¹ * (E (mixW M ![fun _ => 0, fun _ => 1]))⁻¹ *
    (E (mixW M ![fun _ => 1, β]))⁻¹ * E (mixW M ![fun _ => 1, fun _ => 0]) * E (mixW M ![fun _ => 0, β])

def th3 {U : Type} [CommGroup U] (E : (Fin 3 → ρ → S) → U) (s : Fin 3 → ρ → S) : U :=
  ∏ I : Finset (Fin 3), E (fun i r => if i ∈ I then s i r else 0) ^ ((-1 : ℤ) ^ (3 - I.card))

def subL (M : Fin 2 → Fin 3 → S) (m : ℕ) : Jet S (Fin 2 × ρ) m →ₐ[S] Jet S (Fin 3 × ρ) m :=
  jetMap (fun p => ∑ i, MvPolynomial.C (M p.1 i) * MvPolynomial.X (i, p.2)) fun p =>
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (X_mem_orig (i, p.2))

def sc3 (s : Fin 3 → ρ → S) (m : ℕ) : Jet S (Fin 3 × ρ) m →ₐ[S] Jet S (Fin 3 × ρ) m :=
  jetScale fun p => s p.1 p.2

end Weights

end GlobalTheory.RayRosEx
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.RayHoriz GlobalTheory.RayRos GlobalTheory.RayRosEx
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayRosEx.ThetaPull

section Jets

variable {S : Type} [CommRing S] {ρ : Type}

end Jets

section Vals

theorem val_comp_stalkMap {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : W ⟶ Z) (r : Z ⟶ Y) {w : W} {J : (W ⟶ X) → L.ι} (hJ : Good L w J) :
    Units.map (κ.stalkMap w).hom.toMonoidHom (val t r (κ w) fun ψ => J (κ ≫ ψ)) = val t (κ ≫ r) w J := by
  rw [val_of t (κ ≫ r) w J (fun k => J (κ ≫ r ≫ φ k)) fun k => by rw [Category.assoc]]
  have h : r (κ w) ∈ LB.wchart L φ fun k => J (κ ≫ r ≫ φ k) := Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)
  exact Units.ext ((congrArg (κ.stalkMap w).hom (gm_val r (κ w) _ h _)).trans
    ((Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ (LB.wchart L φ fun k => J (κ ≫ r ≫ φ k))) w h _).trans
      (gm_val (κ ≫ r) w _ h _).symm))

end Vals

end GlobalTheory.RayRosEx.ThetaPull
end
end
