import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GrpPullbackSquareProductLift
import ReciprocityTheory.DualLattices.IsPairingValueAddRight
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MulEqZeroOfSqZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionSecondLawCommutativityValue
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCompatibleBasis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorsionInvariantDescendsFibre
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ProdCocycleMul
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NonemptyIsBiextOfCubeGen

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in

private theorem biextVal_pull {S : Scheme.{0}} {G : Over S} {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → ((G ⊗ G ⊗ G).left ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J : (T'.left ⟶ X) → L.ι} (hJ : Good L z J) (x x' y : T ⟶ G) :
    val (LB.pullGen L φ ε t (lift x (lift x' y)).left) ρ.left z J =
      val t (lift (ρ ≫ x) (lift (ρ ≫ x') (ρ ≫ y))).left z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift]

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem biext_val_axioms :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (T : Over S) (z : T.left)
    (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ t₁ t₂ : (T ⟶ G) → (T ⟶ G) → (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    (∀ x x' y, t₁ x x' y = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J) → (∀ x y y', t₂ x y y' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift y y')).left z J) →
    (∀ x x' x'' y, t₁ (x * x') x'' y * t₁ x x' y = t₁ x (x' * x'') y * t₁ x' x'' y) ∧ (∀ x x' y, t₁ x x' y = t₁ x' x y) ∧
    (∀ x y y' y'', t₂ x (y * y') y'' * t₂ x y y' = t₂ x y (y' * y'') * t₂ x y' y'') ∧ (∀ x y y', t₂ x y y' = t₂ x y' y) ∧
    (∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')) := by
  intro S G _ _ P β T z J hJ t₁ t₂ h₁ h₂
  have a₀ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 0 = a := fun a b c d => by simp [x4]
  have a₁ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 1 = b := fun a b c d => by simp [x4]
  have a₂ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 2 = c := fun a b c d => by simp [x4]
  have a₃ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ x4 G 3 = d := fun a b c d => by simp [x4]
  have b₀ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 0) (x4 G 1) = a * b :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
  have b₁ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 1) (x4 G 2) = b * c :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
  have b₂ : ∀ a b c d : T ⟶ G, lift a (lift b (lift c d)) ≫ padd G (x4 G 2) (x4 G 3) = c * d :=
    fun a b c d => (MonObj.comp_mul _ _ _).trans (by rw [a₂, a₃])
  have c₀ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 0 = a := fun a b c => by simp [x3]
  have c₁ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 1 = b := fun a b c => by simp [x3]
  have c₂ : ∀ a b c : T ⟶ G, lift a (lift b c) ≫ x3 G 2 = c := fun a b c => by simp [x3]
  simp only [h₁, h₂]
  refine ⟨fun x x' x'' y => ?_, fun x x' y => ?_, fun x y y' y'' => ?_, fun x y y' => ?_, fun x x' y y' => ?_⟩
  · have := val_corr hJ β.assoc1 (lift x (lift x' (lift x'' y))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _)
      (biextVal_pull _ _ hJ _ _ _))).symm.trans (this.trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₀, b₁, a₀, a₁, a₂, a₃] at e
  · have e := (val_corr hJ β.comm1 (lift x (lift x' y)).left).trans (biextVal_pull _ _ hJ _ _ _)
    rwa [c₀, c₁, c₂] at e
  · have := val_corr hJ β.assoc2 (lift x (lift y (lift y' y''))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _)
      (biextVal_pull _ _ hJ _ _ _))).symm.trans (this.trans ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₁, b₂, a₀, a₁, a₂, a₃] at e
  · have e := (val_corr hJ β.comm2 (lift x (lift y y')).left).trans (biextVal_pull _ _ hJ _ _ _)
    rwa [c₀, c₁, c₂] at e
  · have := val_corr hJ β.compat (lift x (lift x' (lift y y'))).left
    have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))) (biextVal_pull _ _ hJ _ _ _))).symm.trans
      (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (biextVal_pull _ _ hJ _ _ _) (biextVal_pull _ _ hJ _ _ _))) (biextVal_pull _ _ hJ _ _ _))))
    rwa [b₀, b₂, a₀, a₁, a₂, a₃] at e

end GlobalTheory
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section GroupIdentities
variable {M : Type} [CommGroup M]

private lemma mul_rearrange_five {u u' u'' a b c d : M} (h : b * a = d * c) :
    u * u' * a * u'' * b = u * (u' * u'' * c) * d := by
  calc _ = u * u' * u'' * (b * a) := by ac_rfl
    _ = u * u' * u'' * (d * c) := by rw [h]
    _ = _ := by ac_rfl

private lemma fs_zero {u a b : M} (h : b * a = b * b) : a⁻¹ * u * b = u := by
  rw [← mul_left_cancel h, mul_right_comm, inv_mul_cancel, _root_.one_mul]

private lemma fs_inter {u u' w w' a b c d e f : M} (h : a * b * c = d * e * f) :
    u * u' * e * (w * w' * f) * d = u * w * b * (u' * w' * c) * a := by
  calc _ = u * u' * w * w' * (d * e * f) := by ac_rfl
    _ = u * u' * w * w' * (a * b * c) := by rw [h]
    _ = _ := by ac_rfl

private lemma fs_nat {u u' a b c d e : M} (h : a * b = c * d * e) :
    u * u' * a * b = u * c * (u' * d) * e := by
  calc _ = u * u' * (a * b) := by ac_rfl
    _ = u * u' * (c * d * e) := by rw [h]
    _ = _ := by ac_rfl

private lemma fs_zero_nat {a b c : M} (h : a * b = b * b * c) : a⁻¹ * b = c⁻¹ := by
  have h' : a = b * c := by
    apply mul_right_cancel (b := b)
    rw [h]; ac_rfl
  rw [h', mul_inv, mul_right_comm, inv_mul_cancel, _root_.one_mul]

end GroupIdentities

private lemma fs_sigma_eq {A U : Type} {x x' y y' : A} {u u' : U} :
    (⟨x, y, u⟩ : Σ _ : A, Σ _ : A, U) = ⟨x', y', u'⟩ ↔ x = x' ∧ y = y' ∧ u = u' := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private lemma fs_units_fibre {R₀ : Type} [CommRing R₀] {F R₁ R₂ R : LAlg R₀} {p₁ : LHom F R₁}
    {p₂ : LHom F R₂} {f₁ : LHom R₁ R} {f₂ : LHom R₂ R} (h : IsFibreSq p₁ p₂ f₁ f₂)
    (a : (R₁ : Type)ˣ) (b : (R₂ : Type)ˣ)
    (hab : Units.map (f₁.1 : (R₁ : Type) →* (R : Type)) a =
      Units.map (f₂.1 : (R₂ : Type) →* (R : Type)) b) :
    ∃! c : (F : Type)ˣ, Units.map (p₁.1 : (F : Type) →* (R₁ : Type)) c = a ∧
      Units.map (p₂.1 : (F : Type) →* (R₂ : Type)) c = b := by
  obtain ⟨c, ⟨h1, h2⟩, hu⟩ := h.2.2.2 (a : R₁.carrier) (b : R₂.carrier) (congrArg Units.val hab)
  have hc : IsUnit c := p₁.2.map_nonunit c (by
    have : (p₁.1 : F.carrier →+* R₁.carrier) c = a := h1
    rw [this]; exact a.isUnit)
  refine ⟨hc.unit, ⟨Units.ext h1, Units.ext h2⟩, ?_⟩
  rintro c' ⟨e1, e2⟩
  exact Units.ext (hu c' ⟨congrArg Units.val e1, congrArg Units.val e2⟩)

theorem exists_BX_of_factorSystems :
  (∀ {R₀ : Type} [CommRing R₀] (B₀ : BX R₀) (δ : ∀ {R S : LAlg R₀}, LHom R S → B₀.G R → B₀.G R → (S : Type)ˣ)
    (t₁ t₂ : ∀ R : LAlg R₀, B₀.G R → B₀.G R → B₀.G R → (R : Type)ˣ) (w : ∀ R : LAlg R₀, B₀.G R → B₀.G R → (R : Type)ˣ),
    (∀ R x y, δ (LHom.id R) x y = 1) →
    (∀ {Q R S : LAlg R₀} (f : LHom Q R) (h : LHom R S) x y, δ (h.comp f) x y = Units.map (h.1 : (R : Type) →* (S : Type)) (δ f x y) * δ h (B₀.map f x) (B₀.map f y)) →
    (∀ R x x' x'' y, t₁ R (x + x') x'' y * t₁ R x x' y = t₁ R x (x' + x'') y * t₁ R x' x'' y) → (∀ R x x' y, t₁ R x x' y = t₁ R x' x y) →
    (∀ R x y y' y'', t₂ R x (y + y') y'' * t₂ R x y y' = t₂ R x y (y' + y'') * t₂ R x y' y'') → (∀ R x y y', t₂ R x y y' = t₂ R x y' y) →
    (∀ R x x' y y', t₁ R x x' (y + y') * t₂ R x y y' * t₂ R x' y y' = t₂ R (x + x') y y' * t₁ R x x' y * t₁ R x x' y') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x x' y, Units.map (f.1 : (R : Type) →* (S : Type)) (t₁ R x x' y) * δ f (x + x') y =
      δ f x y * δ f x' y * t₁ S (B₀.map f x) (B₀.map f x') (B₀.map f y)) →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y y', Units.map (f.1 : (R : Type) →* (S : Type)) (t₂ R x y y') * δ f x (y + y') =
      δ f x y * δ f x y' * t₂ S (B₀.map f x) (B₀.map f y) (B₀.map f y')) →
    (∀ R x y, w R x y * w R y x = 1) → (∀ R x x' y, t₁ R x x' y * w R (x + x') y = w R x y * w R x' y * t₂ R y x x') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y, Units.map (f.1 : (R : Type) →* (S : Type)) (w R x y) * δ f y x = δ f x y * w S (B₀.map f x) (B₀.map f y)) →
    ∃ (B : BX R₀) (κ : ∀ R, B.G R ≃+ B₀.G R) (b : ∀ R x y, B.P R x y),
      (∀ {R S : LAlg R₀} (f : LHom R S) x, κ S (B.map f x) = B₀.map f (κ R x)) ∧
      (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R (κ R x) (κ R x') (κ R y)) (b R (x + x') y)) ∧
      (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R (κ R x) (κ R y) (κ R y')) (b R x (y + y'))) ∧
      (∀ {R S : LAlg R₀} (f : LHom R S) x y, B.pmap f (b R x y) = B.smul (δ f (κ R x) (κ R y)) (b S (B.map f x) (B.map f y)))) := by
  intro R₀ _ B₀ δ t₁ t₂ w hid hcomp h1a h1c h2a h2c hint h1n h2n hww hw1 hwn
  let B : BX R₀ :=
    { B₀ with
      P := fun R _ _ => (R : Type)ˣ
      smul := fun l u => l * u
      one_smul := fun u => _root_.one_mul u
      mul_smul := fun l l' u => _root_.mul_assoc l l' u
      nonempty := fun _ _ _ => ⟨1⟩
      trans := fun u v => ⟨v * u⁻¹, by simp, fun l hl => by rw [← hl]; simp⟩
      pmap := fun {R S} f {x y} u => Units.map (f.1 : (R : Type) →* (S : Type)) u * δ f x y
      pmap_smul := fun f _ _ l u => by rw [map_mul, _root_.mul_assoc]
      pmap_id := fun {R x y} u => heq_of_eq (by rw [hid, _root_.mul_one]; rfl)
      pmap_comp := fun f g _ _ u => heq_of_eq (by rw [hcomp, map_mul, ← _root_.mul_assoc]; rfl)
      add1 := fun {R x x' y} u u' => u * u' * t₁ R x x' y
      add2 := fun {R x y y'} u u' => u * u' * t₂ R x y y'
      zero1 := fun {R} y => (t₁ R 0 0 y)⁻¹
      zero2 := fun {R} x => (t₂ R x 0 0)⁻¹
      addFst_assoc := fun u u' u'' => heq_of_eq (mul_rearrange_five (h1a _ _ _ _ _))
      addSnd_assoc := fun u u' u'' => heq_of_eq (mul_rearrange_five (h2a _ _ _ _ _))
      addFst_comm := fun u u' => heq_of_eq (by rw [h1c, _root_.mul_comm u])
      addSnd_comm := fun u u' => heq_of_eq (by rw [h2c, _root_.mul_comm u])
      zeroFst_add := fun {R x y} u => heq_of_eq (fs_zero (by
        simpa only [add_zero, zero_add] using h1a R 0 0 x y))
      zeroSnd_add := fun {R x y} u => heq_of_eq (fs_zero (by
        simpa only [add_zero, zero_add] using h2a R x 0 0 y))
      addFst_smul := fun l l' u u' => by ac_rfl
      addSnd_smul := fun l l' u u' => by ac_rfl
      interchange := fun u u' v v' => fs_inter (hint _ _ _ _ _)
      addFst_nat := fun f _ _ _ u u' => heq_of_eq (by
        rw [map_mul, map_mul]; exact fs_nat (h1n _ _ _ _))
      addSnd_nat := fun f _ _ _ u u' => heq_of_eq (by
        rw [map_mul, map_mul]; exact fs_nat (h2n _ _ _ _))
      zeroFst_nat := fun f y => heq_of_eq (by
        rw [map_inv]
        exact fs_zero_nat (by simpa only [add_zero, map_zero] using h1n f 0 0 y))
      zeroSnd_nat := fun f x => heq_of_eq (by
        rw [map_inv]
        exact fs_zero_nat (by simpa only [add_zero, map_zero] using h2n f x 0 0))
      sw := fun {R x y} u => u * w R x y
      sw_smul := fun l u => _root_.mul_assoc _ _ _
      sw_nat := fun f _ _ u => by rw [map_mul, _root_.mul_assoc, _root_.mul_assoc, hwn]
      swap_addFst := fun u u' => fs_nat (hw1 _ _ _ _)
      sw_sw := fun u => by rw [_root_.mul_assoc, hww, _root_.mul_one]
      fibre_P := by
        intro F R₁ R₂ R p₁ p₂ f₁ f₂ h
        rintro ⟨x₁, y₁, u₁⟩ ⟨x₂, y₂, u₂⟩ e
        obtain ⟨ex, ey, eu⟩ := fs_sigma_eq.1 e
        obtain ⟨x, ⟨rfl, rfl⟩, hx⟩ := B₀.fibre_G p₁ p₂ f₁ f₂ h x₁ x₂ ex
        obtain ⟨y, ⟨rfl, rfl⟩, hy⟩ := B₀.fibre_G p₁ p₂ f₁ f₂ h y₁ y₂ ey
        have hsq : f₁.comp p₁ = f₂.comp p₂ := Subtype.ext h.1
        have hδ := (hcomp p₁ f₁ x y).symm.trans (hsq ▸ hcomp p₂ f₂ x y)
        obtain ⟨u, ⟨hu1, hu2⟩, hu⟩ := fs_units_fibre h (u₁ / δ p₁ x y) (u₂ / δ p₂ x y) (by
          rw [map_div, map_div, div_eq_div_iff_mul_eq_mul]
          apply mul_right_cancel (b := δ f₁ (B₀.map p₁ x) (B₀.map p₁ y) *
            δ f₂ (B₀.map p₂ x) (B₀.map p₂ y))
          dsimp only at eu
          calc _ = (Units.map (f₁.1 : (R₁ : Type) →* (R : Type)) u₁ *
                δ f₁ (B₀.map p₁ x) (B₀.map p₁ y)) *
                (Units.map (f₂.1 : (R₂ : Type) →* (R : Type)) (δ p₂ x y) *
                δ f₂ (B₀.map p₂ x) (B₀.map p₂ y)) := by ac_rfl
            _ = _ := by rw [eu, ← hδ]; ac_rfl)
        refine ⟨⟨x, y, u⟩, ⟨fs_sigma_eq.2 ⟨rfl, rfl, ?_⟩, fs_sigma_eq.2 ⟨rfl, rfl, ?_⟩⟩, ?_⟩
        · dsimp only
          rw [hu1, div_mul_cancel]
        · dsimp only
          rw [hu2, div_mul_cancel]
        · rintro ⟨x', y', u'⟩ ⟨e1, e2⟩
          obtain ⟨a1, b1, c1⟩ := fs_sigma_eq.1 e1
          obtain ⟨a2, b2, c2⟩ := fs_sigma_eq.1 e2
          obtain rfl := hx x' ⟨a1, a2⟩
          obtain rfl := hy y' ⟨b1, b2⟩
          exact fs_sigma_eq.2 ⟨rfl, rfl, hu u' ⟨eq_div_iff_mul_eq'.2 c1, eq_div_iff_mul_eq'.2 c2⟩⟩ }
  refine ⟨B, fun R => AddEquiv.refl _, fun R _ _ => (1 : (R : Type)ˣ), fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro R x x' y
    exact show (1 : (R : Type)ˣ) * 1 * t₁ R x x' y = t₁ R x x' y * 1 by simp
  · intro R x y y'
    exact show (1 : (R : Type)ˣ) * 1 * t₂ R x y y' = t₂ R x y y' * 1 by simp
  · intro R S f x y
    exact show Units.map (f.1 : (R : Type) →* (S : Type)) 1 * δ f x y = δ f x y * 1 by simp

end GlobalTheory
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem bxFibre_exists_chart {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {P : Type}
    [CommRing P] [IsLocalRing P] (x : Spec (CommRingCat.of P) ⟶ Y)
    (h : x (closedPoint P) ∈ U) :
    ∃ φ : Γ(Y, U) →+* P, x = Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec := by
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
    have hsp : (p : PrimeSpectrum P) ⤳ closedPoint P :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum P).isPrime.ne_top)
    exact hsp.mem_open (x ⁻¹ᵁ U).isOpen h
  refine ⟨(x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU
    (isAffineOpen_top (Spec (CommRingCat.of P))) hx
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem bxFibre_closed {Y : Scheme.{0}} {P Q : Type} [CommRing P] [IsLocalRing P] [CommRing Q]
    [IsLocalRing Q] (f : P →+* Q) [IsLocalHom f] (x : Spec (CommRingCat.of P) ⟶ Y) :
    (Spec.map (CommRingCat.ofHom f) ≫ x) (closedPoint Q) = x (closedPoint P) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun y => x y) ?_)
  exact IsLocalRing.comap_closedPoint f

theorem bxFibre_comp {Y : Scheme.{0}} {A P Q : Type} [CommRing A] [CommRing P] [CommRing Q]
    (φ : A →+* P) (f : P →+* Q) (g : Spec (CommRingCat.of A) ⟶ Y) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom φ) ≫ g =
      Spec.map (CommRingCat.ofHom (f.comp φ)) ≫ g := by
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem bxFibre_inj {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {P : Type}
    [CommRing P] {φ ψ : Γ(Y, U) →+* P}
    (h : Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) : φ = ψ := by
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem bxFibre_affine {Y : Scheme.{0}} (y : Y) : ∃ U : Y.Opens, IsAffineOpen U ∧ y ∈ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  exact ⟨U, hU, hmem⟩

theorem bxFibre_unique {Y : Scheme.{0}} {F P Q : Type} [CommRing F] [IsLocalRing F] [CommRing P]
    [IsLocalRing P] [CommRing Q] (p : F →+* P) [IsLocalHom p] (q : F →+* Q)
    (hinj : ∀ s t, p s = p t → q s = q t → s = t) (c c' : Spec (CommRingCat.of F) ⟶ Y)
    (hp : Spec.map (CommRingCat.ofHom p) ≫ c = Spec.map (CommRingCat.ofHom p) ≫ c')
    (hq : Spec.map (CommRingCat.ofHom q) ≫ c = Spec.map (CommRingCat.ofHom q) ≫ c') :
    c = c' := by
  obtain ⟨U, hU, hmem⟩ := bxFibre_affine (c (closedPoint F))
  have hmem' : c' (closedPoint F) ∈ U := by
    rw [← bxFibre_closed p c', ← hp, bxFibre_closed p c]
    exact hmem
  obtain ⟨φ, hφ⟩ := bxFibre_exists_chart hU c hmem
  obtain ⟨ψ, hψ⟩ := bxFibre_exists_chart hU c' hmem'
  rw [hφ, hψ] at hp hq ⊢
  have h1 : p.comp φ = p.comp ψ := bxFibre_inj hU
    ((bxFibre_comp φ p hU.fromSpec).symm.trans (hp.trans (bxFibre_comp ψ p hU.fromSpec)))
  have h2 : q.comp φ = q.comp ψ := bxFibre_inj hU
    ((bxFibre_comp φ q hU.fromSpec).symm.trans (hq.trans (bxFibre_comp ψ q hU.fromSpec)))
  have : φ = ψ := RingHom.ext fun s =>
    hinj _ _ (RingHom.congr_fun h1 s) (RingHom.congr_fun h2 s)
  rw [this]

theorem bxFibre_exists {Y : Scheme.{0}} {F P Q R : Type} [CommRing F] [CommRing P]
    [IsLocalRing P] [CommRing Q] [IsLocalRing Q] [CommRing R] [IsLocalRing R]
    (p : F →+* P) (q : F →+* Q) (f : P →+* R) [IsLocalHom f] (g : Q →+* R) [IsLocalHom g]
    (hex : ∀ a b, f a = g b → ∃! c, p c = a ∧ q c = b)
    (hinj : ∀ s t, p s = p t → q s = q t → s = t)
    (a : Spec (CommRingCat.of P) ⟶ Y) (b : Spec (CommRingCat.of Q) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom f) ≫ a = Spec.map (CommRingCat.ofHom g) ≫ b) :
    ∃ c : Spec (CommRingCat.of F) ⟶ Y, Spec.map (CommRingCat.ofHom p) ≫ c = a ∧
      Spec.map (CommRingCat.ofHom q) ≫ c = b := by
  obtain ⟨U, hU, hmem⟩ := bxFibre_affine (a (closedPoint P))
  have hmem' : b (closedPoint Q) ∈ U := by
    rw [← bxFibre_closed g b, ← h, bxFibre_closed f a]
    exact hmem
  obtain ⟨φ, hφ⟩ := bxFibre_exists_chart hU a hmem
  obtain ⟨ψ, hψ⟩ := bxFibre_exists_chart hU b hmem'
  rw [hφ, hψ] at h ⊢
  erw [bxFibre_comp, bxFibre_comp] at h
  have h1 := bxFibre_inj hU h
  have h2 : ∀ s, ∃ c, p c = φ s ∧ q c = ψ s := fun s =>
    (hex _ _ (RingHom.congr_fun h1 s)).exists
  choose k hk hk' using h2
  let χ : Γ(Y, U) →+* F :=
    { toFun := k
      map_one' := hinj _ _ (by simp [hk]) (by simp [hk'])
      map_mul' := fun s t => hinj _ _ (by simp [hk]) (by simp [hk'])
      map_zero' := hinj _ _ (by simp [hk]) (by simp [hk'])
      map_add' := fun s t => hinj _ _ (by simp [hk]) (by simp [hk']) }
  refine ⟨Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec, ?_, ?_⟩
  · erw [bxFibre_comp]
    have : p.comp χ = φ := RingHom.ext hk
    rw [this]
  · erw [bxFibre_comp]
    have : q.comp χ = ψ := RingHom.ext hk'
    rw [this]

theorem points_fibre_product :
  (∀ {R₀ : Type} [CommRing R₀] (X : Over (Spec (CommRingCat.of R₀))) {F R₁ R₂ R : LAlg R₀} (p₁ : LHom F R₁) (p₂ : LHom F R₂) (f₁ : LHom R₁ R) (f₂ : LHom R₂ R),
    IsFibreSq p₁ p₂ f₁ f₂ → ∀ (a : sp (R₀ := R₀) (R₁ : Type) ⟶ X) (b : sp (R₀ := R₀) (R₂ : Type) ⟶ X), spMap f₁.1 ≫ a = spMap f₂.1 ≫ b →
    ∃! c : sp (R₀ := R₀) (F : Type) ⟶ X, spMap p₁.1 ≫ c = a ∧ spMap p₂.1 ≫ c = b) := by
  intro R₀ _ X F R₁ R₂ R p₁ p₂ f₁ f₂ hsq a b hab
  obtain ⟨hc, -, -, hex⟩ := hsq
  haveI : IsLocalHom p₁.1.toRingHom := p₁.2
  haveI : IsLocalHom f₁.1.toRingHom := f₁.2
  haveI : IsLocalHom f₂.1.toRingHom := f₂.2
  have hinj : ∀ s t, p₁.1.toRingHom s = p₁.1.toRingHom t → p₂.1.toRingHom s = p₂.1.toRingHom t →
      s = t := fun s t h1 h2 =>
    (hex (p₁.1 t) (p₂.1 t) (AlgHom.congr_fun hc t)).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩
  obtain ⟨c, h1, h2⟩ := bxFibre_exists (Y := X.left) p₁.1.toRingHom p₂.1.toRingHom
    f₁.1.toRingHom f₂.1.toRingHom hex hinj a.left b.left (congrArg (·.left) hab)
  have hw : c ≫ X.hom = (sp (R₀ := R₀) (F : Type)).hom := by
    refine bxFibre_unique p₁.1.toRingHom p₂.1.toRingHom hinj _ _ ?_ ?_
    · rw [← Category.assoc, h1]
      exact (Over.w a).trans (Over.w (spMap p₁.1)).symm
    · rw [← Category.assoc, h2]
      exact (Over.w b).trans (Over.w (spMap p₂.1)).symm
  refine ⟨Over.homMk c hw, ⟨Over.OverMorphism.ext h1, Over.OverMorphism.ext h2⟩, ?_⟩
  rintro c' ⟨k1, k2⟩
  apply Over.OverMorphism.ext
  exact bxFibre_unique (Y := X.left) p₁.1.toRingHom p₂.1.toRingHom hinj _ _
    ((congrArg (·.left) k1).trans h1.symm) ((congrArg (·.left) k2).trans h2.symm)

end GlobalTheory
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section
variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}

private lemma smul_inj {x y : B.G R} (w : B.P R x y) {l l' : (R : Type)ˣ}
    (h : B.smul l w = B.smul l' w) : l = l' :=
  (B.trans w (B.smul l' w)).unique h rfl

private lemma transport_left_smul_frame (b : ∀ x y, B.P R x y) {x x' y : B.G R} (h : x = x') (l : (R : Type)ˣ) :
    B.tr1 h (B.smul l (b x y)) = B.smul l (b x' y) := by
  subst h; rfl

private lemma transport_right_smul_frame (b : ∀ x y, B.P R x y) {x y y' : B.G R} (h : y = y') (l : (R : Type)ˣ) :
    B.tr2 h (B.smul l (b x y)) = B.smul l (b x y') := by
  subst h; rfl

private lemma transport_left_of_heq {x x' y : B.G R} (h : x = x') {u : B.P R x y} {w : B.P R x' y}
    (e : HEq u w) : B.tr1 h u = w := by
  subst h; exact eq_of_heq e

private lemma transport_right_of_heq {x y y' : B.G R} (h : y = y') {u : B.P R x y} {w : B.P R x y'}
    (e : HEq u w) : B.tr2 h u = w := by
  subst h; exact eq_of_heq e

private lemma heq_transport_left {x x' y : B.G R} (h : x = x') (u : B.P R x y) : HEq (B.tr1 h u) u := by
  subst h; rfl

private lemma heq_transport_right {x y y' : B.G R} (h : y = y') (u : B.P R x y) : HEq (B.tr2 h u) u := by
  subst h; rfl

private lemma add_left_transport_heq {x x' x'' y : B.G R} (h : x = x') (u : B.P R x y) (w : B.P R x'' y) :
    HEq (B.add1 (B.tr1 h u) w) (B.add1 u w) := by
  subst h; rfl

private lemma add_right_transport_heq {x y y' y'' : B.G R} (h : y = y') (u : B.P R x y) (w : B.P R x y'') :
    HEq (B.add2 (B.tr2 h u) w) (B.add2 u w) := by
  subst h; rfl

private lemma frame_zero1 (b : ∀ x y, B.P R x y) (t : B.G R → B.G R → B.G R → (R : Type)ˣ)
    (h : ∀ x x' y, B.add1 (b x y) (b x' y) = B.smul (t x x' y) (b (x + x') y)) (y : B.G R) :
    b 0 y = B.smul (t 0 0 y) (B.zero1 y) := by
  obtain ⟨l, hl, -⟩ := B.trans (b 0 y) (B.zero1 y)
  have h1 := transport_left_of_heq B (zero_add (0 : B.G R)) (B.zeroFst_add (B.zero1 y))
  rw [← hl, B.addFst_smul, h, ← B.mul_smul, transport_left_smul_frame] at h1
  have h2 := smul_inj B _ h1
  have h3 : t 0 0 y * l = 1 := by
    rw [_root_.mul_assoc, mul_eq_left] at h2
    rw [mul_comm, h2]
  rw [← hl, ← B.mul_smul, h3, B.one_smul]

private lemma frame_zero2 (b : ∀ x y, B.P R x y) (t : B.G R → B.G R → B.G R → (R : Type)ˣ)
    (h : ∀ x y y', B.add2 (b x y) (b x y') = B.smul (t x y y') (b x (y + y'))) (x : B.G R) :
    b x 0 = B.smul (t x 0 0) (B.zero2 x) := by
  obtain ⟨l, hl, -⟩ := B.trans (b x 0) (B.zero2 x)
  have h1 := transport_right_of_heq B (zero_add (0 : B.G R)) (B.zeroSnd_add (B.zero2 x))
  rw [← hl, B.addSnd_smul, h, ← B.mul_smul, transport_right_smul_frame] at h1
  have h2 := smul_inj B _ h1
  have h3 : t x 0 0 * l = 1 := by
    rw [_root_.mul_assoc, mul_eq_left] at h2
    rw [mul_comm, h2]
  rw [← hl, ← B.mul_smul, h3, B.one_smul]

private lemma frame_nsmul1 (b : ∀ x y, B.P R x y) (t : B.G R → B.G R → B.G R → (R : Type)ˣ)
    (h : ∀ x x' y, B.add1 (b x y) (b x' y) = B.smul (t x x' y) (b (x + x') y)) (x y : B.G R)
    (N : ℕ) : B.nsmul1 (b x y) (N + 1) =
      B.smul (∏ k ∈ Finset.range N, t ((k + 1) • x) x y) (b ((N + 1) • x) y) := by
  induction N with
  | zero =>
    rw [Finset.prod_range_zero, ← transport_left_smul_frame B b (show x = (0 + 1) • x by simp), B.one_smul]
    apply eq_of_heq
    unfold BX.nsmul1 BX.nsmul1
    exact (heq_transport_left B _ _).trans ((add_left_transport_heq B _ _ _).trans
      ((B.zeroFst_add _).trans (heq_transport_left B _ _).symm))
  | succ N ih =>
    rw [BX.nsmul1, ih, Finset.prod_range_succ]
    conv_lhs => rw [← B.one_smul (b x y), B.addFst_smul, h, ← B.mul_smul, transport_left_smul_frame, _root_.mul_one]

private lemma frame_nsmul2 (b : ∀ x y, B.P R x y) (t : B.G R → B.G R → B.G R → (R : Type)ˣ)
    (h : ∀ x y y', B.add2 (b x y) (b x y') = B.smul (t x y y') (b x (y + y'))) (x y : B.G R)
    (N : ℕ) : B.nsmul2 (b x y) (N + 1) =
      B.smul (∏ k ∈ Finset.range N, t x ((k + 1) • y) y) (b x ((N + 1) • y)) := by
  induction N with
  | zero =>
    rw [Finset.prod_range_zero, ← transport_right_smul_frame B b (show y = (0 + 1) • y by simp), B.one_smul]
    apply eq_of_heq
    unfold BX.nsmul2 BX.nsmul2
    exact (heq_transport_right B _ _).trans ((add_right_transport_heq B _ _ _).trans
      ((B.zeroSnd_add _).trans (heq_transport_right B _ _).symm))
  | succ N ih =>
    rw [BX.nsmul2, ih, Finset.prod_range_succ]
    conv_lhs => rw [← B.one_smul (b x y), B.addSnd_smul, h, ← B.mul_smul, transport_right_smul_frame, _root_.mul_one]

private lemma coboundary_rearrange {G : Type*} [CommGroup G] (m m' p q r s t : G) (h : r * s = t * (p * q)) :
    m * m' * t * r⁻¹ = m * m' * (p⁻¹ * q⁻¹) * s := by
  rw [← eq_inv_mul_iff_mul_eq] at h
  rw [h, ← mul_inv, ← _root_.mul_assoc r⁻¹, _root_.mul_assoc (m * m') (p * q)⁻¹,
    mul_comm (p * q)⁻¹, mul_inv_cancel_right, _root_.mul_assoc (m * m'), mul_comm t]

private noncomputable def frameEquiv {x y : B.G R} (w : B.P R x y) : (R : Type)ˣ ≃ B.P R x y :=
  Equiv.ofBijective (fun l => B.smul l w)
    ⟨fun _ _ h => smul_inj B w h, fun v => (B.trans w v).exists⟩

private lemma frameEquiv_trans {x y x' y' : B.G R} (w : B.P R x y) (w' : B.P R x' y')
    (l : (R : Type)ˣ) :
    ((frameEquiv B w).symm.trans (frameEquiv B w')) (B.smul l w) = B.smul l w' := by
  have : B.smul l w = frameEquiv B w l := rfl
  rw [this, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

end

theorem bx_frame_pairing_adj :
  (∀ {R₀ : Type} [CommRing R₀] (B : BX R₀) (b : ∀ R x y, B.P R x y) (t₁ t₂ : ∀ R : LAlg R₀, B.G R → B.G R → B.G R → (R : Type)ˣ),
    (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R x x' y) (b R (x + x') y)) →
    (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R x y y') (b R x (y + y'))) →
    (∀ R (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ), B.IsPairing (N + 1) x y z ↔ (N + 1) • x = 0 ∧ (N + 1) • y = 0 ∧
      z = (t₁ R 0 0 y * ∏ k ∈ Finset.range N, t₁ R ((k + 1) • x) x y) / (t₂ R x 0 0 * ∏ k ∈ Finset.range N, t₂ R x ((k + 1) • y) y)) ∧
    ∀ (O : LAlg R₀) (a a' : OEnd B O) (u : ∀ {R : LAlg R₀}, LHom O R → B.G R → B.G R → (R : Type)ˣ),
      (∀ {R : LAlg R₀} (s : LHom O R) x x' y, u s (x + x') y * t₁ R x x' (a'.f s y) = t₁ R (a.f s x) (a.f s x') y * (u s x y * u s x' y)) →
      (∀ {R : LAlg R₀} (s : LHom O R) x y y', u s x (y + y') * t₂ R x (a'.f s y) (a'.f s y') = t₂ R (a.f s x) y y' * (u s x y * u s x y')) →
      ∃ A : OAdj B O, A.a = a ∧ A.ab = a') := by
  intro R₀ _ B b t₁ t₂ h₁ h₂
  refine ⟨fun R N x y z => ?_, fun O a a' u hu₁ hu₂ => ?_⟩
  · have key : ∀ (hx : (N + 1) • x = 0) (hy : (N + 1) • y = 0), B.IsPairing (N + 1) x y
        ((t₁ R 0 0 y * ∏ k ∈ Finset.range N, t₁ R ((k + 1) • x) x y) /
          (t₂ R x 0 0 * ∏ k ∈ Finset.range N, t₂ R x ((k + 1) • y) y)) := by
      intro hx hy
      refine ⟨hx, hy, b R x y, _, _, ?_, ?_, rfl⟩
      · rw [frame_nsmul1 B (b R) (t₁ R) (h₁ R), transport_left_smul_frame, frame_zero1 B (b R) (t₁ R) (h₁ R),
          ← B.mul_smul, mul_comm]
      · rw [frame_nsmul2 B (b R) (t₂ R) (h₂ R), transport_right_smul_frame, frame_zero2 B (b R) (t₂ R) (h₂ R),
          ← B.mul_smul, mul_comm]
    constructor
    · intro h
      exact ⟨h.1, h.2.1, B.pairing_unique _ _ _ _ _ h (key h.1 h.2.1)⟩
    · rintro ⟨hx, hy, rfl⟩
      exact key hx hy
  · refine ⟨⟨a, a', fun {R} s x z => (frameEquiv B (b R (a.f s x) z)).symm.trans
      (frameEquiv B (B.smul (u s x z)⁻¹ (b R x (a'.f s z)))), ?_, ?_, ?_⟩, rfl, rfl⟩
    · intro R s x z l v
      obtain ⟨m, rfl, -⟩ := B.trans (b R (a.f s x) z) v
      rw [← B.mul_smul, frameEquiv_trans, frameEquiv_trans, B.mul_smul]
    · intro R s x x' z v v'
      obtain ⟨m, rfl, -⟩ := B.trans (b R (a.f s x) z) v
      obtain ⟨m', rfl, -⟩ := B.trans (b R (a.f s x') z) v'
      rw [B.addFst_smul, h₁, ← B.mul_smul, transport_left_smul_frame, frameEquiv_trans, frameEquiv_trans,
        frameEquiv_trans, B.addFst_smul, B.addFst_smul, h₁, ← B.mul_smul, ← B.mul_smul, ← B.mul_smul]
      congr 1
      have := hu₁ s x x' z
      exact coboundary_rearrange _ _ _ _ _ _ _ this
    · intro R s x z z' v v'
      obtain ⟨m, rfl, -⟩ := B.trans (b R (a.f s x) z) v
      obtain ⟨m', rfl, -⟩ := B.trans (b R (a.f s x) z') v'
      rw [B.addSnd_smul, h₂, ← B.mul_smul, frameEquiv_trans, frameEquiv_trans,
        frameEquiv_trans, B.addSnd_smul, B.addSnd_smul, h₂, ← B.mul_smul, ← B.mul_smul, ← B.mul_smul,
        transport_right_smul_frame]
      congr 1
      have := hu₂ s x z z'
      exact coboundary_rearrange _ _ _ _ _ _ _ this

end GlobalTheory
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BiextSym

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_gen_of_iso {X : Scheme.{0}} {L : LB X} {F : X ⟶ X} (h : LBIso L (L.pull F)) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![F, 𝟙 X] ![1, -1]), s.IsGen := by
  obtain ⟨w, hw⟩ := h
  have hp := (isGen_iff w).1 hw
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![F, 𝟙 X] j ≤ (L.pull F).U (fun _ => j 0) ⊓ L.U (j 1) :=
    fun j x hx => ⟨mem_pull.2 (Set.mem_iInter.1 hx 0), Set.mem_iInter.1 hx 1⟩
  refine ⟨⟨fun j => res (le j) (w.s (fun _ => j 0, j 1))⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have a := hp _ (𝟙 X) y (j 0) (j' 0) (j 1) (j' 1) (mem_pull.1 (le j hy.1).1) (mem_pull.1 (le j' hy.2).1)
    (le j hy.1).2 (le j' hy.2).2
  refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 X) y (le j) hy.1 _)).trans (a.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 X) y j j' hy.1 hy.2).trans ?_)
    ((gm_res _ y _ hy _).trans (gm_res (𝟙 X) y (le j') hy.2 _)))
  rw [Fin.prod_univ_two]
  show gm (𝟙 X ≫ F) y _ (L.g (j 0) (j' 0)) ^ (1 : ℤ) * gm (𝟙 X ≫ 𝟙 X) y _ (L.g (j 1) (j' 1)) ^ (-1 : ℤ) = _
  rw [_root_.zpow_neg, _root_.zpow_one, _root_.zpow_one, Category.id_comp (𝟙 X)]

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

omit [GrpObj A] [IsCommMonObj A] in
theorem prod_sym {T : Over S} (x y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i : Fin 2, h ((lift x y).left ≫ ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] i) ^ (![1, -1] i : ℤ) =
      h (lift y x).left * (h (lift x y).left)⁻¹ := by
  have e : lift x y ≫ lift (snd A A) (fst A A) = lift y x := by rw [comp_lift, lift_fst, lift_snd]
  rw [Fin.prod_univ_two]
  show h (lift x y ≫ lift (snd A A) (fst A A)).left ^ (1 : ℤ) * h ((lift x y).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
  rw [e, Category.comp_id, _root_.zpow_neg, _root_.zpow_one, _root_.zpow_one]

theorem biextension_first_law_product {T : Over S} (x x' y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i, h ((lift x (lift x' y)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) i) ^ lawε i =
      h (lift (x * x') y).left * (h (lift x y).left)⁻¹ * (h (lift x' y).left)⁻¹ := by
  have a₀ : lift x (lift x' y) ≫ x3 A 0 = x := by simp [x3]
  have a₁ : lift x (lift x' y) ≫ x3 A 1 = x' := by simp [x3]
  have a₂ : lift x (lift x' y) ≫ x3 A 2 = y := by simp [x3]
  have b : lift x (lift x' y) ≫ padd A (x3 A 0) (x3 A 1) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift x' y)).left ≫ law1φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift x' y) ≫ lift (padd A (x3 A 0) (x3 A 1)) (x3 A 2)).left ^ (1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 A 1) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]

theorem biextension_second_law_product {T : Over S} (x y y' : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ (A ⊗ A).left) → U) :
    ∏ i, h ((lift x (lift y y')).left ≫ law2φ A (x3 A 0) (x3 A 1) (x3 A 2) i) ^ lawε i =
      h (lift x (y * y')).left * (h (lift x y).left)⁻¹ * (h (lift x y').left)⁻¹ := by
  have a₀ : lift x (lift y y') ≫ x3 A 0 = x := by simp [x3]
  have a₁ : lift x (lift y y') ≫ x3 A 1 = y := by simp [x3]
  have a₂ : lift x (lift y y') ≫ x3 A 2 = y' := by simp [x3]
  have b : lift x (lift y y') ≫ padd A (x3 A 1) (x3 A 2) = y * y' := (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift y y')).left ≫ law2φ A (x3 A 0) (x3 A 1) (x3 A 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift y y') ≫ lift (x3 A 0) (padd A (x3 A 1) (x3 A 2))).left ^ (1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 A 0) (x3 A 1)).left ^ (-1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 A 0) (x3 A 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]

theorem exists_norm {P : LB (A ⊗ A).left} (hP : P.IsLB) (h : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) :
    ∃ s : LB.Gen (LB.LinComb P (K := Fin 2) ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] ![1, -1]), s.IsGen ∧
      ∀ (T : Over S) (z : T.left) (J), Good P z J → val s (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  obtain ⟨t, ht⟩ := exists_gen_of_iso h
  obtain ⟨s, hs, hv⟩ := exists_gen hP (K' := Fin 2) (φ' := ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left])
    (ε' := ![1, -1]) (fun V _ k => by
      have p := prod_sym (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A) k
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _
        (c := ∏ i : Fin 2, k (![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] i) ^ (![1, -1] i : ℤ)) rfl
        (DVR.prod_neg _ _ p)) ?_
      rw [mul_inv_cancel, inv_one, _root_.mul_one])
    (LB.mulGen P _ _ _ _ t (LB.invGen P _ _ (LB.pullGen P _ _ t (lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨s, hs, fun T z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, ← Over.comp_left, comp_lift, MonObj.comp_one, mul_inv_cancel]

theorem val_pull₂ {X : Scheme.{0}} {P : LB X} {K : Type} [Fintype K] {B C : Over S} {φ : K → ((B ⊗ C).left ⟶ X)}
    {ε : K → ℤ} (u : LB.Gen (LB.LinComb P φ ε)) {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good P z J)
    (a : T ⟶ B) (b : T ⟶ C) :
    val (LB.pullGen P φ ε u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift]

theorem val_pull₃ {X : Scheme.{0}} {P : LB X} {K : Type} [Fintype K] {B C D : Over S}
    {φ : K → ((B ⊗ C ⊗ D).left ⟶ X)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb P φ ε)) {T T' : Over S} (ρ : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good P z J) (a : T ⟶ B) (b : T ⟶ C) (c : T ⟶ D) :
    val (LB.pullGen P φ ε u (lift a (lift b c)).left) ρ.left z J =
      val u (lift (ρ ≫ a) (lift (ρ ≫ b) (ρ ≫ c))).left z J := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift, comp_lift]

theorem law_origin {P : LB (A ⊗ A).left} (β : IsBiext A P) {T : Over S} {z : T.left} {J} (hJ : Good P z J) :
    val β.law1 (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A))).left z J =
      val β.law2 (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A))).left z J := by
  let ρ := lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (lift (1 : T ⟶ A) (1 : T ⟶ A)))
  have a₀ : ρ ≫ x4 A 0 = 1 := by simp [ρ, x4]
  have a₁ : ρ ≫ x4 A 1 = 1 := by simp [ρ, x4]
  have a₂ : ρ ≫ x4 A 2 = 1 := by simp [ρ, x4]
  have a₃ : ρ ≫ x4 A 3 = 1 := by simp [ρ, x4]
  have b₀ : ρ ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁, _root_.mul_one])
  have b₁ : ρ ≫ padd A (x4 A 2) (x4 A 3) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [a₂, a₃, _root_.mul_one])
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    (val_pull₃ β.law1 ρ hJ _ _ _) (val_pull₃ β.law2 ρ hJ _ _ _))) (val_pull₃ β.law2 ρ hJ _ _ _))).symm.trans
    ((val_corr hJ β.compat ρ.left).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull₃ β.law2 ρ hJ _ _ _) (val_pull₃ β.law1 ρ hJ _ _ _))) (val_pull₃ β.law1 ρ hJ _ _ _))))
  rw [b₀, b₁, a₀, a₁, a₂, a₃, mul_comm (val β.law2 _ z J) (val β.law1 _ z J)] at e
  exact (mul_left_cancel e).symm

theorem main :
  (ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme A →
    ∀ (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (A ⊗ A).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext A P),
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∃ s : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := Fin 2) ![(lift (snd A A) (fst A A)).left, 𝟙 (A ⊗ A).left] ![1, -1]), s.IsGen ∧ ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ (A ⊗ A).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ x x' y : T ⟶ A,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift y x).left z J = 1 ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift (x * x') y).left z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x' y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift y (lift x x')).left z J) := by
  intro hG S A _ _ hA P β hs
  obtain ⟨s, hs, h1⟩ := exists_norm β.isLB hs
  refine ⟨s, hs, fun T z J hJ x x' y => ⟨?_, ?_⟩⟩
  · have ev : ∀ {T' : Over S} (σ : T' ⟶ A ⊗ A) {z : T'.left} {J}, Good P z J →
        val (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ s (lift (fst A A) (snd A A)).left)
          (LB.pullGen P _ _ s (lift (snd A A) (fst A A)).left)) σ.left z J =
          val s (lift (σ ≫ fst A A) (σ ≫ snd A A)).left z J * val s (lift (σ ≫ snd A A) (σ ≫ fst A A)).left z J :=
      fun σ z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₂ s σ hJ _ _) (val_pull₂ s σ hJ _ _))
    let e : 𝟙_ (Over S) ⟶ A ⊗ A := lift 1 1
    have sj : Function.Surjective ((snd A A).left ≫ A.hom).appTop.hom := surj_comp (surj_snd hG hA _) (hG _ _ hA).2
    have he : e.left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by rw [Over.w]; exact Over.w e
    have key := gen_unique' β.isLB (u' := LB.oneGen P (Y := (A ⊗ A).left)) (fun V _ k => by
        refine (Fintype.prod_empty _).trans (Eq.symm ?_)
        refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym (fst A A) (snd A A) k)
          (prod_sym (snd A A) (fst A A) k)).trans ?_
        rw [_root_.mul_assoc, inv_mul_cancel_left, mul_inv_cancel]) _ e.left he sj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hs _) (DVR.pullGen_isGen _ _ _ _ hs _))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
      (fun y I hI => by
        refine (ev e hI).trans (Eq.trans ?_ (val_one _).symm)
        rw [lift_fst, lift_snd, h1 _ y I hI, _root_.mul_one]) _ (lift x y).left z J hJ
    have := (ev (lift x y) hJ).symm.trans (key.trans (val_one _))
    rwa [lift_fst, lift_snd] at this
  · let p₀ := x3 A 0
    let p₁ := x3 A 1
    let p₂ := x3 A 2
    have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 A) {z : T'.left} {J}, Good P z J →
        val (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ β.law1 (lift p₀ (lift p₁ p₂)).left)
          (LB.pullGen P _ _ s (lift (p₀ * p₁) p₂).left)) σ.left z J =
          val β.law1 (lift (σ ≫ p₀) (lift (σ ≫ p₁) (σ ≫ p₂))).left z J * val s (lift (σ ≫ (p₀ * p₁)) (σ ≫ p₂)).left z J ∧
        val (LB.mulGen P _ _ _ _ (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ s (lift p₀ p₂).left)
          (LB.pullGen P _ _ s (lift p₁ p₂).left)) (LB.pullGen P _ _ β.law2 (lift p₂ (lift p₀ p₁)).left)) σ.left z J =
          val s (lift (σ ≫ p₀) (σ ≫ p₂)).left z J * val s (lift (σ ≫ p₁) (σ ≫ p₂)).left z J *
            val β.law2 (lift (σ ≫ p₂) (lift (σ ≫ p₀) (σ ≫ p₁))).left z J := fun σ z J hJ =>
      ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull₃ β.law1 σ hJ _ _ _) (val_pull₂ s σ hJ _ _)),
        (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (val_pull₂ s σ hJ _ _) (val_pull₂ s σ hJ _ _))) (val_pull₃ β.law2 σ hJ _ _ _))⟩
    let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
    have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
    have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
    have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
    have sj : Function.Surjective ((snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom).appTop.hom :=
      surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
    have he : e.left ≫ (snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
      rw [Over.w, Over.w]; exact Over.w e
    let ρ : T ⟶ G3 A := lift x (lift x' y)
    have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
    have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
    have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
    have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
    have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
    have := (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' β.isLB (fun V _ k => by
        refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := ULift.{0} (Fin 3)) (U := V) _
          (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym p₀ p₂ k) (prod_sym p₁ p₂ k))
          (biextension_second_law_product p₂ p₀ p₁ k)).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := ULift.{0} (Fin 3)) (K' := Fin 2) (U := V) _
            (biextension_first_law_product p₀ p₁ p₂ k) (prod_sym (p₀ * p₁) p₂ k)).symm)
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) _ e.left he sj
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen1 _) (DVR.pullGen_isGen _ _ _ _ hs _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.pullGen_isGen _ _ _ _ hs _) (DVR.pullGen_isGen _ _ _ _ hs _)) (DVR.pullGen_isGen _ _ _ _ β.isGen2 _))
      (fun y I hI => by
        refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
        rw [o₁, e₀, e₁, e₂, h1 _ y I hI, law_origin β hI, _root_.mul_one, _root_.one_mul, _root_.one_mul])
      _ ρ.left z J hJ) (ev ρ hJ).2)
    rwa [s₁, r₀, r₁, r₂] at this

end GlobalTheory.BiextSym
end
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in

private theorem invGenDescent_gs_appLE {Y Y' : Scheme.{0}} (τ : Y' ⟶ Y) (W : Y.Opens) (W' : Y'.Opens)
    (h : W' ≤ τ ⁻¹ᵁ W) (a : Γ(Y, W)) (x : Y') (hx : x ∈ W') :
    gs (𝟙 Y') x W' ((τ.appLE W W' h).hom a) = gs τ x W a := by
  have e := (gs_res (𝟙 Y') x h hx ((τ.app W).hom a)).trans (gs_pull (𝟙 Y') τ x W (h hx) a)
  rw [Category.id_comp] at e
  exact e

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in

private theorem invariant_generator_descent {X Y Y' : Scheme.{0}} (m : Y' ⟶ Y) {T : Type} (τ : T → (Y' ⟶ Y'))
    (hτ : ∀ t, τ t ≫ m = m)
    (H : ∀ (V : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ V)),
      (∀ t, ∀ h : m ⁻¹ᵁ V ≤ τ t ⁻¹ᵁ (m ⁻¹ᵁ V), ((τ t).appLE _ _ h).hom a = a) →
      ∃! a' : Γ(Y, V), (m.app V).hom a' = a)
    (M : LB X) (hM : M.IsLB) (ψ : Y ⟶ X)
    (σ : LB.Gen (LB.LinComb M (K := PUnit) (fun _ => m ≫ ψ) (fun _ => 1))) (hσ : σ.IsGen)
    (inv : ∀ t (z : Y') (J : (Y' ⟶ X) → M.1), Good M z J → val σ (𝟙 Y' ≫ τ t) z J = val σ (𝟙 Y') z J) :
    ∃ t : (M.pull ψ).Gen, t.IsGen := by
  have inj : ∀ V : Y.Opens, Function.Injective (m.app V).hom := by
    intro V a b e
    obtain ⟨c, -, hc⟩ := H V ((m.app V).hom a) (fun t h => fn_ext fun x hx => by
      rw [invGenDescent_gs_appLE (τ t) _ _ h _ x hx, gs_pull (τ t) m x V (h hx), gs_pull (𝟙 Y') m x V hx, hτ,
        Category.id_comp])
    exact (hc a rfl).trans (hc b e.symm).symm
  have injU : ∀ V : Y.Opens, Function.Injective (pullU m V) := fun V a b e =>
    Units.ext (inj V (congrArg Units.val e))
  have descU : ∀ (V : Y.Opens) (u : Γ(Y', m ⁻¹ᵁ V)ˣ),
      (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) → ∃ v : Γ(Y, V)ˣ, pullU m V v = u := by
    intro V u hu
    have key : ∀ u : Γ(Y', m ⁻¹ᵁ V)ˣ, (∀ t x, x ∈ m ⁻¹ᵁ V → gm (τ t) x _ u = gm (𝟙 Y') x _ u) →
        ∃ a : Γ(Y, V), (m.app V).hom a = u.val := fun u hu =>
      (H V u.val (fun t h => fn_ext fun x hx => by
        rw [invGenDescent_gs_appLE (τ t) _ _ h _ x hx, gs_unit (τ t) x (m ⁻¹ᵁ V) (h hx),
          gs_unit (𝟙 Y') x (m ⁻¹ᵁ V) hx,
          hu t x hx])).exists
    obtain ⟨a, ha⟩ := key u hu
    obtain ⟨b, hb⟩ := key u⁻¹ (fun t x hx => by rw [map_inv, map_inv, hu t x hx])
    have e : a * b = 1 := inj V (by rw [map_mul, map_one, ha, hb]; exact u.mul_inv)
    exact ⟨⟨a, b, e, (mul_comm _ _).trans e⟩, Units.ext ha⟩
  have le : ∀ j : PUnit → M.ι, m ⁻¹ᵁ LB.wchart M (fun _ : PUnit => ψ) j ≤ LB.wchart M (fun _ : PUnit => m ≫ ψ) j :=
    fun j x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  have loc : ∀ j : PUnit → M.ι, ∃ v : Γ(Y, LB.wchart M (fun _ : PUnit => ψ) j)ˣ,
      pullU m _ v = res (le j) (σ.s j) := by
    intro j
    refine descU _ _ fun t x hx => ?_
    have hx' : τ t x ∈ m ⁻¹ᵁ LB.wchart M (fun _ : PUnit => ψ) j :=
      (congrArg (fun q : Y' ⟶ Y => q x ∈ LB.wchart M (fun _ : PUnit => ψ) j) (hτ t)).mpr hx
    obtain ⟨J, hJ, e⟩ := exists_good M hM x (fun _ : PUnit => m ≫ ψ) j (fun a b _ => rfl)
      (fun k => Set.mem_iInter.1 (le j hx) k)
    have := inv t x J hJ
    rw [val_of σ _ x J j (fun k => by rw [Category.id_comp, ← Category.assoc, hτ]; exact e k),
      val_of σ _ x J j (fun k => by rw [Category.id_comp]; exact e k), Category.id_comp] at this
    exact (gm_res (τ t) x (le j) hx' _).trans (this.trans (gm_res (𝟙 Y') x (le j) hx _).symm)
  choose v hv using loc
  refine ⟨⟨v⟩, fun i j => injU _ (unit_ext fun x hx => ?_)⟩
  have hv' : ∀ j : PUnit → M.ι, m x ∈ LB.wchart M (fun _ : PUnit => ψ) j →
      gm (𝟙 Y' ≫ m) x _ (v j) = gm (𝟙 Y') x (LB.wchart M (fun _ : PUnit => m ≫ ψ) j) (σ.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m x _ hj _).symm.trans ((congrArg (gm (𝟙 Y') x _) (hv j)).trans (gm_res (𝟙 Y') x (le j) hj _))
  have hx' : (𝟙 Y' ≫ m) x ∈ LB.wchart M (fun _ : PUnit => ψ) i ⊓ LB.wchart M (fun _ : PUnit => ψ) j := hx
  refine (gm_pull (𝟙 Y') m x _ hx _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m x _ hx _).symm)
  refine (gm_res _ x _ hx' _).trans ((hv' i hx.1).trans ((gen_trans hσ (𝟙 Y') x (le i hx.1) (le j hx.2)).trans
    (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_linComb M (fun _ : PUnit => ψ) (fun _ => 1) (𝟙 Y' ≫ m) x i j hx'.1 hx'.2).trans ?_)
      ((gm_res _ x _ hx' _).trans (hv' j hx.2)))))))
  simp only [trF, Category.assoc]

theorem invariantGenerator_descends_mulN :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (V : (G ⊗ Over.mk f).left.Opens) (a : Γ((G ⊗ Over.mk f).left, (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V)),
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ h : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V ≤ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left ⁻¹ᵁ ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V), ((lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left.appLE _ _ h).hom a = a) →
    ∃! a' : Γ((G ⊗ Over.mk f).left, V), ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left.app V).hom a' = a) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (X : Scheme.{0}) (M : ReciprocityTheory.ChartRestriction.G.Semi.LB X), M.IsLB → ∀ (ψ : (G ⊗ Over.mk f).left ⟶ X)
      (σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb M (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ ψ) (fun _ => 1))), σ.IsGen →
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ X) → M.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good M z J →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) → ∃ t : (M.pull ψ).Gen, t.IsGen) := by
  intro H S G _ _ K _ _ f N hN h₁ h₂ h₃ h₄ X M hM ψ σ hσ inv
  refine invariant_generator_descent (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left (T := {y : Over.mk f ⟶ G // y ^ N = 1})
    (fun y => (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y.1)) (snd G (Over.mk f))).left) (fun y => ?_)
    (fun V a ha => H S G K f N hN h₁ h₂ h₃ h₄ V a (fun y hy => ha ⟨y, hy⟩)) M hM ψ σ hσ
    (fun y z J hJ => inv y.1 y.2 _ (𝟙 _) z J hJ)
  rw [← Over.comp_left]
  congr 1
  ext1
  · rw [lift_whiskerRight, lift_fst, whiskerRight_fst, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
      Category.comp_id, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.mul_one]
  · simp

end GlobalTheory
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem biext_pairing_nondegenerate_geometric_fibre :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom → IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    ∀ (X : Scheme.{0}) (M : ReciprocityTheory.ChartRestriction.G.Semi.LB X), M.IsLB → ∀ (ψ : (G ⊗ Over.mk f).left ⟶ X)
      (σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb M (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ ψ) (fun _ => 1))), σ.IsGen →
    (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ X) → M.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good M z J →
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) → ∃ t : (M.pull ψ).Gen, t.IsGen) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ) (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (x : Over.mk f ⟶ G), x ^ N = 1 →
    ∃ σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left) (fun _ => 1)), σ.IsGen ∧
      ∀ y : Over.mk f ⟶ G, y ^ N = 1 → (∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
        ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom →
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    (∀ x : Over.mk f ⟶ G, (∃ t : (P.pull (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : Over.mk f ⟶ G, x ^ N = 1 → (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
      ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) → x = 1) := by
  intro hD hS S G _ _ P β K _ _ f N hN hsm hfin hfl hsur hpr x hx hxy
  obtain ⟨σ, hσ, hinv⟩ := hS S G K f N P β x hx
  exact hpr x (hD S G K f N hN hsm hfin hfl hsur _ P β.isLB _ σ hσ
    (fun y hy => hinv y hy (hxy y hy)))

end GlobalTheory
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section Transfer
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : LB (G ⊗ G).left} (β : IsBiext G P)

private theorem pfTie_prod1 {T : Over S} (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (CartesianMonoidalCategory.lift (x * x') y).left * (h (CartesianMonoidalCategory.lift x y).left)⁻¹ * (h (CartesianMonoidalCategory.lift x' y).left)⁻¹ := by
  have e₀ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2) = CartesianMonoidalCategory.lift (x * x') y := by
    rw [comp_lift]
    congr 1
    · exact (MonObj.comp_mul _ _ _).trans (by simp [x3])
    · simp [x3]
  have e₁ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2) = CartesianMonoidalCategory.lift x y := by rw [comp_lift]; simp [x3]
  have e₂ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 1) (x3 G 2) = CartesianMonoidalCategory.lift x' y := by rw [comp_lift]; simp [x3]
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun k => h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨k⟩) ^ lawε ⟨k⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2)).left ^ (1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift x' y) ≫ CartesianMonoidalCategory.lift (x3 G 1) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [e₀, e₁, e₂]
  simp only [_root_.zpow_neg, zpow_one]

private theorem pfTie_prod2 {T : Over S} (x y y' : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y')).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (CartesianMonoidalCategory.lift x (y * y')).left * (h (CartesianMonoidalCategory.lift x y).left)⁻¹ * (h (CartesianMonoidalCategory.lift x y').left)⁻¹ := by
  have e₀ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (padd G (x3 G 1) (x3 G 2)) = CartesianMonoidalCategory.lift x (y * y') := by
    rw [comp_lift]
    congr 1
    · simp [x3]
    · exact (MonObj.comp_mul _ _ _).trans (by simp [x3])
  have e₁ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 1) = CartesianMonoidalCategory.lift x y := by rw [comp_lift]; simp [x3]
  have e₂ : CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2) = CartesianMonoidalCategory.lift x y' := by rw [comp_lift]; simp [x3]
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _
    (fun k => h ((CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y')).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨k⟩) ^ lawε ⟨k⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (padd G (x3 G 1) (x3 G 2))).left ^ (1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 1)).left ^ (-1 : ℤ) *
    h (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift y y') ≫ CartesianMonoidalCategory.lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [e₀, e₁, e₂]
  simp only [_root_.zpow_neg, zpow_one]

private theorem pfTie_gen {T : Over S} (x y : T ⟶ G) (n : ℕ) :
    ∃ t : LB.Gen (LB.LinComb P (K := Fin 4) ![(CartesianMonoidalCategory.lift (x ^ n) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left, (CartesianMonoidalCategory.lift x (y ^ n)).left,
        (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left] ![1, -1, -1, 1]), t.IsGen ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P z J →
        val t ρ.left z J = (∏ k ∈ Finset.range n, val β.law1 (CartesianMonoidalCategory.lift ((ρ ≫ x) ^ k) (CartesianMonoidalCategory.lift (ρ ≫ x) (ρ ≫ y))).left z J) *
          (∏ k ∈ Finset.range n, val β.law2 (CartesianMonoidalCategory.lift (ρ ≫ x) (CartesianMonoidalCategory.lift ((ρ ≫ y) ^ k) (ρ ≫ y))).left z J)⁻¹ := by
  induction n with
  | zero =>
    obtain ⟨t, ht, hv⟩ := exists_gen β.isLB (φ' := ![(CartesianMonoidalCategory.lift (x ^ 0) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left, (CartesianMonoidalCategory.lift x (y ^ 0)).left,
        (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left]) (ε' := ![1, -1, -1, 1])
      (fun U _ h => by simp [Fin.prod_univ_succ]) (LB.oneGen P (Y := T.left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t, ht, fun T' ρ z J hJ => ((hv _ _ z J hJ).trans (val_one _)).trans (by simp)⟩
  | succ n ih =>
    obtain ⟨t, ht, hv⟩ := ih
    obtain ⟨t', ht', hv'⟩ := exists_gen β.isLB (φ' := ![(CartesianMonoidalCategory.lift (x ^ (n + 1)) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left,
        (CartesianMonoidalCategory.lift x (y ^ (n + 1))).left, (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left]) (ε' := ![1, -1, -1, 1]) (fun U _ h => by
        refine (DVR.prod_sum₂ (K := Fin 4) (K' := ULift.{0} (Fin 3) ⊕ ULift.{0} (Fin 3)) (U := U) _
          (c := ∏ i, h ((![(CartesianMonoidalCategory.lift (x ^ n) y).left, (CartesianMonoidalCategory.lift (1 : T ⟶ G) y).left, (CartesianMonoidalCategory.lift x (y ^ n)).left,
            (CartesianMonoidalCategory.lift x (1 : T ⟶ G)).left] : Fin 4 → _) i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i) rfl
          (DVR.prod_sum₂ (K := ULift.{0} (Fin 3)) (K' := ULift.{0} (Fin 3)) (U := U) _ (pfTie_prod1 (x ^ n) x y h)
            (DVR.prod_neg _ _ (pfTie_prod2 x (y ^ n) y h)))).trans ?_
        rw [pow_succ x, pow_succ y]
        apply Additive.ofMul.injective
        simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
        abel)
      (LB.mulGen P _ _ _ _ t (LB.mulGen P _ _ _ _ (LB.pullGen P _ _ β.law1 (CartesianMonoidalCategory.lift (x ^ n) (CartesianMonoidalCategory.lift x y)).left)
        (LB.invGen P _ _ (LB.pullGen P _ _ β.law2 (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift (y ^ n) y)).left))))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen1 _)
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen2 _))))
    refine ⟨t', ht', fun T' ρ z J hJ => ?_⟩
    have p₁ : ρ ≫ (x ^ n) = (ρ ≫ x) ^ n := map_pow (preHom ρ) _ _
    have p₂ : ρ ≫ (y ^ n) = (ρ ≫ y) ^ n := map_pow (preHom ρ) _ _
    have q₁ : ρ.left ≫ (CartesianMonoidalCategory.lift (x ^ n) (CartesianMonoidalCategory.lift x y)).left = (CartesianMonoidalCategory.lift ((ρ ≫ x) ^ n) (CartesianMonoidalCategory.lift (ρ ≫ x) (ρ ≫ y))).left := by
      rw [← Over.comp_left, comp_lift, comp_lift, p₁]
    have q₂ : ρ.left ≫ (CartesianMonoidalCategory.lift x (CartesianMonoidalCategory.lift (y ^ n) y)).left = (CartesianMonoidalCategory.lift (ρ ≫ x) (CartesianMonoidalCategory.lift ((ρ ≫ y) ^ n) (ρ ≫ y))).left := by
      rw [← Over.comp_left, comp_lift, comp_lift, p₂]
    refine ((hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv T' ρ z J hJ)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans (congrArg (val β.law1 · z J) q₁))
        ((val_inv _ _).trans (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans (congrArg (val β.law2 · z J) q₂))))))))).trans ?_
    rw [Finset.prod_range_succ, Finset.prod_range_succ, mul_inv, _root_.mul_mul_mul_comm]

private theorem pfTie_unit {T : Over S} (x y : T ⟶ G) (n : ℕ) (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P z J →
        gm ρ.left z ⊤ a = (∏ k ∈ Finset.range n, val β.law1 (CartesianMonoidalCategory.lift ((ρ ≫ x) ^ k) (CartesianMonoidalCategory.lift (ρ ≫ x) (ρ ≫ y))).left z J) *
          (∏ k ∈ Finset.range n, val β.law2 (CartesianMonoidalCategory.lift (ρ ≫ x) (CartesianMonoidalCategory.lift ((ρ ≫ y) ^ k) (ρ ≫ y))).left z J)⁻¹ := by
  obtain ⟨u, hu, hw⟩ := pfTie_gen β x y n
  obtain ⟨t, -, hv⟩ := exists_gen β.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine Eq.trans ?_ (Fintype.prod_empty _).symm
      rw [hx, hy]
      simp [Fin.prod_univ_succ]) u hu
  have le : (⊤ : T.left.Opens) ≤ LB.wchart P (PEmpty.elim : PEmpty → (T.left ⟶ (G ⊗ G).left)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun T' ρ z J hJ => ?_⟩
  rw [← hw T' ρ z J hJ, ← hv _ _ z J hJ, val_of t ρ.left z J PEmpty.elim (fun k => k.elim)]
  exact gm_res ρ.left z le trivial _

private theorem pfTie_local (R : Type) [CommRing R] [IsLocalRing R] (a : Γ(Spec (CommRingCat.of R), ⊤)ˣ)
    (h : gm (𝟙 (Spec (CommRingCat.of R))) (IsLocalRing.closedPoint R) ⊤ a = 1) : a = 1 := by
  apply Units.ext
  have e := congrArg (fun u => (stalkClosedPointIso (CommRingCat.of R)).hom.hom (Units.val u)) h
  have g := congrArg (fun q => q.hom a.val) (germ_stalkClosedPointIso_hom (CommRingCat.of R))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at g
  have e' : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a.val = 1 :=
    g.symm.trans ((congrArg (stalkClosedPointIso (CommRingCat.of R)).hom.hom (gm_val (𝟙 _) _ ⊤ trivial a)).symm.trans
      (e.trans (map_one _)))
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective (e'.trans (map_one _).symm)

end Transfer

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem pairing_nondegenerate_integral_torsion :
  (∀ {R₀ : Type} [CommRing R₀] (B : BX R₀) (b : ∀ R x y, B.P R x y) (t₁ t₂ : ∀ R : LAlg R₀, B.G R → B.G R → B.G R → (R : Type)ˣ),
    (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R x x' y) (b R (x + x') y)) →
    (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R x y y') (b R x (y + y'))) →
    (∀ R (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ), B.IsPairing (N + 1) x y z ↔ (N + 1) • x = 0 ∧ (N + 1) • y = 0 ∧
      z = (t₁ R 0 0 y * ∏ k ∈ Finset.range N, t₁ R ((k + 1) • x) x y) / (t₂ R x 0 0 * ∏ k ∈ Finset.range N, t₂ R x ((k + 1) • y) y)) ∧
    ∀ (O : LAlg R₀) (a a' : OEnd B O) (u : ∀ {R : LAlg R₀}, LHom O R → B.G R → B.G R → (R : Type)ˣ),
      (∀ {R : LAlg R₀} (s : LHom O R) x x' y, u s (x + x') y * t₁ R x x' (a'.f s y) = t₁ R (a.f s x) (a.f s x') y * (u s x y * u s x' y)) →
      (∀ {R : LAlg R₀} (s : LHom O R) x y y', u s x (y + y') * t₂ R x (a'.f s y) (a'.f s y') = t₂ R (a.f s x) y y' * (u s x y * u s x y')) →
      ∃ A : OAdj B O, A.a = a ∧ A.ab = a') →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ), (N : K) ≠ 0 → Smooth G.hom →
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left → Flat ((𝟙 G) ^ N : G ⟶ G).left → Surjective ((𝟙 G) ^ N : G ⟶ G).left →
    (∀ x : Over.mk f ⟶ G, (∃ t : (P.pull (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : Over.mk f ⟶ G, x ^ N = 1 → (∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
      ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) → x = 1) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), v.Integers (O : Type) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) (O : Type) ⟶ G, ∃ y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = x) ∧
    ∀ z : sp (R₀ := R₀) C ⟶ G, z ^ p = 1 → ∃! y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = 1 ∧ spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ y = z) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (T : Over S) (z : T.left)
    (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ t₁ t₂ : (T ⟶ G) → (T ⟶ G) → (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    (∀ x x' y, t₁ x x' y = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J) → (∀ x y y', t₂ x y y' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift y y')).left z J) →
    (∀ x x' x'' y, t₁ (x * x') x'' y * t₁ x x' y = t₁ x (x' * x'') y * t₁ x' x'' y) ∧ (∀ x x' y, t₁ x x' y = t₁ x' x y) ∧
    (∀ x y y' y'', t₂ x (y * y') y'' * t₂ x y y' = t₂ x y (y' * y'') * t₂ x y' y'') ∧ (∀ x y y', t₂ x y y' = t₂ x y' y) ∧
    (∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)) (b : ∀ R x y, B.P R x y)
    (J : ∀ R : LAlg R₀, ((sp (R₀ := R₀) (R : Type)).left ⟶ (G ⊗ G).left) → P.1),
    (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    (∀ R : LAlg R₀, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P (Z := (sp (R₀ := R₀) (R : Type)).left) (IsLocalRing.closedPoint (R : Type)) (J R)) →
    (∀ (R : LAlg R₀) x x' y, B.add1 (b R x y) (b R x' y) =
      B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (e R x) (lift (e R x') (e R y))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R (x + x') y)) →
    (∀ (R : LAlg R₀) x y y', B.add2 (b R x y) (b R x y') =
      B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift (e R x) (lift (e R y) (e R y'))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R x (y + y'))) →
    ∀ (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), p ≠ 0 → v.Integers (O : Type) → Smooth G.hom →
    IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) C ⟶ G, (∃ t : (P.pull (lift (snd G (sp (R₀ := R₀) C) ≫ x) (fst G (sp (R₀ := R₀) C))).left).Gen, t.IsGen) → x = 1) →
    ∀ x : B.G O, p • x = 0 → (∀ y : B.G O, p • y = 0 → B.IsPairing p x y 1) → x = 0) := by
  intro FRM PFF TORS BIV R₀ _ G _ _ P β B e b J hb hadd _ hJ h1 h2 O C _ _ _ v _ _ _ p hp hv hsm hfin hfl hsurj hnd x hx H
  obtain ⟨N, rfl⟩ : ∃ N, p = N + 1 := Nat.exists_eq_succ_of_ne_zero hp
  have e0 : e O 0 = 1 := by
    have := hadd O 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have en : ∀ (k : ℕ) (w : B.G O), e O (k • w) = e O w ^ k := fun k w => by
    induction k with
    | zero => rw [zero_nsmul, pow_zero, e0]
    | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]
  obtain ⟨j, hj⟩ : ∃ j : sp (R₀ := R₀) C ⟶ sp (R₀ := R₀) (O : Type), j = spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) :=
    ⟨_, rfl⟩
  have T := (TORS G O C v (N + 1) hv hfin hsurj).2
  rw [← hj] at T
  have hxp : e O x ^ (N + 1) = 1 := by rw [← en, hx, e0]
  have j1 : j ≫ (1 : sp (R₀ := R₀) (O : Type) ⟶ G) = 1 := map_one (preHom j)
  have key : j ≫ e O x = 1 := by
    refine PFF _ G P β C (Spec.map (CommRingCat.ofHom (algebraMap R₀ C))) (N + 1) (Nat.cast_ne_zero.2 hp) hsm hfin hfl
      hsurj hnd (j ≫ e O x) ((map_pow (preHom j) _ _).symm.trans ((congrArg (j ≫ ·) hxp).trans j1))
      (fun y hy z Jc hJc => ?_)
    obtain ⟨y₀, ⟨hy₀, rfl⟩, -⟩ := T y hy
    obtain ⟨y', rfl⟩ := (hb O).2 y₀
    have hy' : (N + 1) • y' = 0 := (hb O).1 (by rw [en, hy₀, e0])
    have F := (((FRM B b _ _ h1 h2).1 O N x y' 1).1 (H y' hy')).2.2
    obtain ⟨a₁, -, a₂, -, -⟩ := BIV _ G P β (sp (R₀ := R₀) (O : Type)) (IsLocalRing.closedPoint (O : Type)) (J O) (hJ O)
      _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    have b₁ := a₁ 1 1 (e O x) (e O y')
    have b₂ := a₂ (e O x) 1 1 (e O y')
    simp only [_root_.one_mul] at b₁ b₂
    have c₁ := mul_left_cancel b₁
    have c₂ := mul_left_cancel b₂
    obtain ⟨a, ha⟩ := pfTie_unit β (e O x) (e O y') (N + 1) hxp hy₀
    have a1 : a = 1 := by
      apply pfTie_local (O : Type) a
      have g := ha _ (𝟙 _) (IsLocalRing.closedPoint (O : Type)) (J O) (hJ O)
      refine Eq.trans g ?_
      simp only [Category.id_comp]
      rw [Finset.prod_range_succ', Finset.prod_range_succ', pow_zero, pow_zero, ← c₁, ← c₂, mul_inv_eq_one]
      simp only [en, e0] at F
      rw [← map_prod, ← map_prod, ← map_mul, ← map_mul, eq_comm, div_eq_one] at F
      have inj := Units.map_injective (f := (stalkClosedPointIso (CommRingCat.of (O : Type))).hom.hom.toMonoidHom)
        (stalkClosedPointIso (CommRingCat.of (O : Type))).commRingCatIsoToRingEquiv.injective F
      exact (mul_comm _ _).trans (inj.trans (mul_comm _ _))
    have g := ha _ j z Jc hJc
    rw [a1, map_one, eq_comm, mul_inv_eq_one] at g
    exact g
  obtain ⟨w, -, hw⟩ := T 1 (one_pow _)
  exact (hb O).1 (((hw _ ⟨hxp, key⟩).trans (hw 1 ⟨one_pow _, j1⟩).symm).trans e0.symm)

end GlobalTheory
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem torsVal_valuationRing {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C]
    {v : Valuation C NNReal} (hv : v.Integers O) : ValuationRing O := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hv h
    exact ⟨c, Or.inr hc.symm⟩
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hv h
    exact ⟨c, Or.inl hc.symm⟩

private theorem torsVal_exists_point {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P A : Scheme.{0}}
    (ψ : P ⟶ A) [LocallyOfFiniteType ψ] [Surjective ψ] (x : Spec (CommRingCat.of Ω) ⟶ A) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ P, p ≫ ψ = x := by
  have hJ : JacobsonSpace ↥(Limits.pullback ψ x) :=
    LocallyOfFiniteType.jacobsonSpace (Limits.pullback.snd ψ x)
  obtain ⟨w⟩ : Nonempty ↥(Spec (CommRingCat.of Ω)) := inferInstance
  obtain ⟨z₀, -⟩ := (Limits.pullback.snd ψ x).surjective w
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(Limits.pullback ψ x)))
    ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed
  replace hz : IsClosed {z} := hz
  refine ⟨pointOfClosedPoint (Limits.pullback.snd ψ x) z hz ≫ Limits.pullback.fst _ _, ?_⟩
  rw [Category.assoc, Limits.pullback.condition, pointOfClosedPoint_comp_assoc]

private theorem torsVal_lift {R₀ : Type} [CommRing R₀] {X Y : Over (Spec (CommRingCat.of R₀))}
    (m : X ⟶ Y) [IsFinite m.left] {O C : Type} [CommRing O] [Field C] [Algebra R₀ O] [Algebra O C]
    [Algebra R₀ C] [IsScalarTower R₀ O C] {v : Valuation C NNReal} (hv : v.Integers O)
    (x : sp (R₀ := R₀) O ⟶ Y) (z : sp (R₀ := R₀) C ⟶ X)
    (h : z ≫ m = spMap (IsScalarTower.toAlgHom R₀ O C) ≫ x) :
    ∃! y : sp (R₀ := R₀) O ⟶ X, y ≫ m = x ∧ spMap (IsScalarTower.toAlgHom R₀ O C) ≫ y = z := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := torsVal_valuationRing hv
  haveI : IsFractionRing O C := hv.isFractionRing
  have hE : ValuativeCriterion.Existence m.left := by
    have h : UniversallyClosed m.left := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hU : ValuativeCriterion.Uniqueness m.left := IsSeparated.valuativeCriterion m.left
  let S : ValuativeCommSq m.left :=
    { R := O, K := C, i₁ := z.left, i₂ := x.left, commSq := ⟨congrArg Over.Hom.left h⟩ }
  obtain ⟨⟨l, h1, h2⟩⟩ := hE S
  have hw : l ≫ X.hom = (sp (R₀ := R₀) O).hom := by
    rw [← Over.w m, ← Category.assoc, h2]
    exact Over.w x
  refine ⟨Over.homMk l hw, ⟨Over.OverMorphism.ext h2, Over.OverMorphism.ext h1⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  have := (hU S).elim ⟨y.left, congrArg Over.Hom.left hy2, congrArg Over.Hom.left hy1⟩ ⟨l, h1, h2⟩
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)

private theorem torsVal_comp_pow {R₀ : Type} [CommRing R₀] {G T : Over (Spec (CommRingCat.of R₀))}
    [GrpObj G] (y : T ⟶ G) (p : ℕ) : y ≫ ((𝟙 G) ^ p : G ⟶ G) = y ^ p := by
  rw [MonObj.comp_pow, Category.comp_id]

theorem points_divisible_and_torsion_of_valuation_integers :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), v.Integers (O : Type) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) (O : Type) ⟶ G, ∃ y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = x) ∧
    ∀ z : sp (R₀ := R₀) C ⟶ G, z ^ p = 1 → ∃! y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = 1 ∧ spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ y = z) := by
  intro R₀ _ G _ _ O C _ _ _ v _ _ _ p hv hfin hsurj
  refine ⟨fun x => ?_, fun z hz => ?_⟩
  · obtain ⟨w, hw⟩ := torsVal_exists_point ((𝟙 G) ^ p : G ⟶ G).left
      (spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ x).left
    have hw' : w ≫ G.hom = (sp (R₀ := R₀) C).hom := by
      rw [← Over.w ((𝟙 G) ^ p : G ⟶ G), ← Category.assoc, hw]
      exact Over.w _
    obtain ⟨y, ⟨hy, -⟩, -⟩ := torsVal_lift ((𝟙 G) ^ p : G ⟶ G) hv x (Over.homMk w hw')
      (Over.OverMorphism.ext hw)
    exact ⟨y, by rw [← torsVal_comp_pow, hy]⟩
  · have := torsVal_lift ((𝟙 G) ^ p : G ⟶ G) hv 1 z
      (by rw [torsVal_comp_pow, hz, MonObj.comp_one])
    simpa only [torsVal_comp_pow] using this

end GlobalTheory
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianPeriodDatum

section SlopeTestRemainingChoices

variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {B : BX R₀}
  {e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)}

private theorem e_zero (hm : ∀ R x y, e R (x + y) = e R x * e R y) (R : LAlg R₀) : e R 0 = 1 := by
  have h := hm R 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

private theorem e_nsmul (hm : ∀ R x y, e R (x + y) = e R x * e R y) (R : LAlg R₀) (n : ℕ) (x : B.G R) :
    e R (n • x) = e R x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, e_zero hm]
  | succ n ih => rw [succ_nsmul, hm, ih, pow_succ]

private theorem divisible_and_card [IsCommMonObj G] (hb : ∀ R, Function.Bijective (e R))
    (hm : ∀ R x y, e R (x + y) = e R x * e R y) (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ)
    (hv : v.Integers (O : Type)) (hf : IsFinite ((𝟙 G) ^ p : G ⟶ G).left) (hs : Surjective ((𝟙 G) ^ p : G ⟶ G).left) :
    (∀ x : B.G O, ∃ y, p • y = x) ∧
      Nat.card {x : B.G O // p • x = 0} = Nat.card {z : sp (R₀ := R₀) C ⟶ G // z ^ p = 1} := by
  obtain ⟨h₁, h₂⟩ := GlobalTheory.points_divisible_and_torsion_of_valuation_integers G O C v p hv hf hs
  have tors : ∀ x : B.G O, p • x = 0 ↔ e O x ^ p = 1 := fun x => by
    rw [← e_nsmul hm, ← e_zero hm O]
    exact (hb O).1.eq_iff.symm
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := h₁ (e O x)
    obtain ⟨y, rfl⟩ := (hb O).2 y
    exact ⟨y, (hb O).1 ((e_nsmul hm O p y).trans hy)⟩
  · refine Nat.card_congr (Equiv.ofBijective
      (fun x => ⟨spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ e O x.1, ?_⟩) ⟨fun x y hxy => ?_, fun z => ?_⟩)
    · rw [← MonObj.comp_pow, (tors _).1 x.2, MonObj.comp_one]
    · have hxy' : spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ e O x.1 =
          spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ e O y.1 := congrArg Subtype.val hxy
      have hz : (spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ e O y.1) ^ p = 1 := by
        rw [← MonObj.comp_pow, (tors _).1 y.2, MonObj.comp_one]
      exact Subtype.ext ((hb O).1 ((h₂ _ hz).unique ⟨(tors _).1 x.2, hxy'⟩ ⟨(tors _).1 y.2, rfl⟩))
    · obtain ⟨y, ⟨hy, hy'⟩, -⟩ := h₂ z.1 z.2
      obtain ⟨y, rfl⟩ := (hb O).2 y
      exact ⟨⟨y, (tors y).2 hy⟩, Subtype.ext hy'⟩

private theorem ring_laws (hb : ∀ R, Function.Bijective (e R))
    (hm : ∀ R x y, e R (x + y) = e R x * e R y) (O : LAlg R₀)
    (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left)
    (gp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ)
    (O₀ : Type) [CommRing O₀] (cj : O₀ → O₀) (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct G' O₀) (Ad : O₀ → OAdj B O)
    (ha : ∀ a {R : LAlg R₀} (s : LHom O R) (x : B.G R)
      (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ ρ.act a).left ≫ φ = (e R ((Ad a).a.f s x)).left)
    (hab : ∀ a {R : LAlg R₀} (s : LHom O R) (x : B.G R)
      (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'),
      x'.left ≫ φ = (e R x).left → (x' ≫ ρ.act (cj a)).left ≫ φ = (e R ((Ad a).ab.f s x)).left) :
    (∀ a, (Ad a).ab = (Ad (cj a)).a) ∧
    (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (Ad 1).a.f s x = x ∧
      ∀ a b, (Ad (a + b)).a.f s x = (Ad a).a.f s x + (Ad b).a.f s x ∧
        (Ad (a * b)).a.f s x = (Ad a).a.f s ((Ad b).a.f s x)) := by
  choose E hE using fun (R : LAlg R₀) (s : LHom O R) => GlobalTheory.adjPoints gp _ _ (GlobalTheory.adjBase s)
  have hl : ∀ R s x, ((E R s).symm (e R x)).left ≫ φ = (e R x).left := fun R s x =>
    (hE R s _).symm.trans (congrArg (fun q => q.left) ((E R s).apply_symm_apply _))
  have inj : ∀ R (x y : B.G R), (e R x).left = (e R y).left → x = y := fun R x y h =>
    (hb R).1 (Over.OverMorphism.ext h)
  refine ⟨fun a => ?_, fun {R} s x => ⟨?_, fun a b => ⟨?_, ?_⟩⟩⟩
  · have h : ∀ {R : LAlg R₀} (s : LHom O R), (Ad a).ab.f s = (Ad (cj a)).a.f s := fun {R} s =>
      AddMonoidHom.ext fun x => inj R _ _ ((hab a s x _ (hl R s x)).symm.trans (ha (cj a) s x _ (hl R s x)))
    generalize (Ad a).ab = u at h
    generalize (Ad (cj a)).a = w at h
    obtain ⟨u, hu⟩ := u
    obtain ⟨w, hw⟩ := w
    obtain rfl : @u = @w := funext fun R => funext fun s => h s
    rfl
  · refine inj R _ _ ((ha 1 s x _ (hl R s x)).symm.trans ?_)
    rw [ρ.map_one, Category.comp_id]
    exact hl R s x
  · refine inj R _ _ ((ha (a + b) s x _ (hl R s x)).symm.trans ?_)
    have h₁ : e R ((Ad a).a.f s x) = E R s ((E R s).symm (e R x) ≫ ρ.act a) :=
      Over.OverMorphism.ext ((ha a s x _ (hl R s x)).symm.trans (hE R s _).symm)
    have h₂ : e R ((Ad b).a.f s x) = E R s ((E R s).symm (e R x) ≫ ρ.act b) :=
      Over.OverMorphism.ext ((ha b s x _ (hl R s x)).symm.trans (hE R s _).symm)
    have h₃ : (E R s).symm (e R x) ≫ ρ.act (a + b) =
        ((E R s).symm (e R x) ≫ ρ.act a) * ((E R s).symm (e R x) ≫ ρ.act b) := by
      rw [ρ.map_add]
      exact MonObj.comp_mul _ _ _
    rw [hm, h₁, h₂, h₃]
    exact (hE R s _).symm.trans (congrArg (fun q => q.left) (map_mul (E R s) _ _))
  · refine inj R _ _ ((ha (a * b) s x _ (hl R s x)).symm.trans ?_)
    rw [ρ.map_mul, ← Category.assoc]
    exact ha a s _ _ (ha b s x _ (hl R s x))

end SlopeTestRemainingChoices

theorem main : (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (g : ℕ) (G : Over (Spec (CommRingCat.of (Ainf.R0 p O ε)))) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left), ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → P.IsLB → (∃ θ : LB.Gen (Theta (G ⊗ G) P), θ.IsGen) → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso P (P.pull (lift (snd G G) (fst G G)).left) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left → ∀ [Algebra ((Ainf.ainfTowerL p O hv ε hε).O : Type) C] [Algebra (Ainf.R0 p O ε) C] [IsScalarTower (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type) C], v.Integers ((Ainf.ainfTowerL p O hv ε hε).O : Type) → (∀ x : sp (R₀ := (Ainf.R0 p O ε)) C ⟶ G, (∃ t : (P.pull (lift (snd G (sp (R₀ := (Ainf.R0 p O ε)) C) ≫ x) (fst G (sp (R₀ := (Ainf.R0 p O ε)) C))).left).Gen, t.IsGen) → x = 1) → Nat.card {z : sp (R₀ := (Ainf.R0 p O ε)) C ⟶ G // z ^ p = 1} = p ^ (2 * g) → ∀ (G' : Over (Spec (CommRingCat.of ((Ainf.ainfTowerL p O hv ε hε).O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left), ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme G' → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type)))) φ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ φ₂ → ∀ [Algebra ℤ_[p] ((Ainf.ainfTowerL p O hv ε hε).O : Type)] (O₀ : Type) [CommRing O₀] (cj : O₀ ≃ₐ[ℤ] O₀) (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct G' O₀), (∀ a, cj (cj a) = a) → (∀ a, (∃ t : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := Fin 2) ![(lift (fst G' G' ≫ ρ.act a) (snd G' G')).left ≫ φ₂, (lift (fst G' G') (snd G' G' ≫ ρ.act (cj a))).left ≫ φ₂] ![1, -1]), t.IsGen)) → ∃ (B : BX (Ainf.R0 p O ε)) (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)) (Ad : O₀ → OAdj B (Ainf.ainfTowerL p O hv ε hε).O), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧ (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) ∧ (∀ a, (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ ρ.act a).left ≫ φ = (e R ((Ad a).a.f s x)).left)) ∧ ∃ (Dt : DualTower (Ainf.ainfTowerL p O hv ε hε)) (D : Dat p g B (Ainf.ainfTowerL p O hv ε hε) Dt (ℤ_[p] ⊗[ℤ] O₀) (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) (Ainf.ainfTowerL p O hv ε hε).c), D.H.P = 0 ∧ D.H.PL = 0 ∧ (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) → (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧ ∀ a j n, (Ad a).a.f (LHom.id (Ainf.ainfTowerL p O hv ε hε).O) (D.L.τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k n) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε g G _ _ P hA hsm hP hθ h1 h2 hsym hf hfl hsu _ _ _ hvi hnd hcard
    G' _ _ φ φ₂ hA' gp sq _ O₀ _ cj ρ hcj hros
  haveI : IsLocalRing (Ainf.R0 p O ε) := GlobalTheory.WdAinf.ainf_thetaQuotRing_isLocalRing p O hv ε hε
  obtain ⟨β⟩ := GlobalTheory.nonempty_isBiext_of_cube_gen _ G hA P hP hθ h1 h2
  obtain ⟨s, hs⟩ := GlobalTheory.BiextSym.main GlobalTheory.globalFns_holds _ G hA P β hsym
  obtain ⟨B, e, hb, hm, hn, b, J, hJ, ha1, ha2⟩ := @GlobalTheory.BXOf.main
    (@GlobalTheory.GroupPointsBX.main (@GlobalTheory.NilCoord.nilpotent_coordinates) (@GlobalTheory.points_fibre_product))
    (@GlobalTheory.exists_BX_of_factorSystems) _ _ G _ _ _ g hsm P β s hs
  have hAd := fun a : O₀ => @GlobalTheory.exists_oAdj_of_rosatiAdjoint (@GlobalTheory.bx_frame_pairing_adj) GlobalTheory.biext_val_axioms
    GlobalTheory.globalFns_holds _ _ G _ _ P β B e b J hb hm hn hJ ha1 ha2 (Ainf.ainfTowerL p O hv ε hε).O G' _ _ φ φ₂ hA' gp sq
    (ρ.act a) (ρ.act (cj a)) (ρ.hom a) (ρ.hom (cj a)) (hros a)
  choose Ad ha hab using hAd
  obtain ⟨hadj, hring⟩ := ring_laws hb hm _ G' φ gp O₀ cj ρ Ad ha hab
  obtain ⟨hdiv, hc⟩ := divisible_and_card hb hm (Ainf.ainfTowerL p O hv ε hε).O C v p hvi hf hsu
  have hsmooth : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  have hpair := @GlobalTheory.pairing_nondegenerate_integral_torsion (@GlobalTheory.bx_frame_pairing_adj)
    (GlobalTheory.biext_pairing_nondegenerate_geometric_fibre
      (GlobalTheory.invariantGenerator_descends_mulN GlobalTheory.torsion_invariant_descends_fibre)
      (GlobalTheory.TorsionGen.main GlobalTheory.biext_val_axioms))
    (@GlobalTheory.points_divisible_and_torsion_of_valuation_integers) GlobalTheory.biext_val_axioms
    _ _ G _ _ P β B e b J hb hm hn hJ ha1 ha2 (Ainf.ainfTowerL p O hv ε hε).O C _ _ _ v _ _ _ p
    (Fact.out : p.Prime).ne_zero hvi hsmooth hf hfl hsu hnd
  exact ⟨B, e, Ad, hb, hm, hn, ha, GlobalTheory.PeriodDatum.main p O hv ε hε g G B e hb hm hn hsm hf hfl hdiv
    (hc.trans hcard) hpair O₀ cj Ad hadj hcj hring⟩

end GlobalTheory.AbelianPeriodDatum
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodTowerDatum_of_abelianScheme_symmetricBundle : (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (g : ℕ) (G : Over (Spec (CommRingCat.of (Ainf.R0 p O ε)))) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left), ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → P.IsLB → (∃ θ : LB.Gen (Theta (G ⊗ G) P), θ.IsGen) → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso P (P.pull (lift (snd G G) (fst G G)).left) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left → ∀ [Algebra ((Ainf.ainfTowerL p O hv ε hε).O : Type) C] [Algebra (Ainf.R0 p O ε) C] [IsScalarTower (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type) C], v.Integers ((Ainf.ainfTowerL p O hv ε hε).O : Type) → (∀ x : sp (R₀ := (Ainf.R0 p O ε)) C ⟶ G, (∃ t : (P.pull (lift (snd G (sp (R₀ := (Ainf.R0 p O ε)) C) ≫ x) (fst G (sp (R₀ := (Ainf.R0 p O ε)) C))).left).Gen, t.IsGen) → x = 1) → Nat.card {z : sp (R₀ := (Ainf.R0 p O ε)) C ⟶ G // z ^ p = 1} = p ^ (2 * g) → ∀ (G' : Over (Spec (CommRingCat.of ((Ainf.ainfTowerL p O hv ε hε).O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left), ReciprocityTheory.ChartRestriction.G.Semi.IsAbelianScheme G' → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap (Ainf.R0 p O ε) ((Ainf.ainfTowerL p O hv ε hε).O : Type)))) φ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSquare φ φ₂ → ∀ [Algebra ℤ_[p] ((Ainf.ainfTowerL p O hv ε hε).O : Type)] (O₀ : Type) [CommRing O₀] (cj : O₀ ≃ₐ[ℤ] O₀) (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct G' O₀), (∀ a, cj (cj a) = a) → (∀ a, (∃ t : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := Fin 2) ![(lift (fst G' G' ≫ ρ.act a) (snd G' G')).left ≫ φ₂, (lift (fst G' G') (snd G' G' ≫ ρ.act (cj a))).left ≫ φ₂] ![1, -1]), t.IsGen)) → ∃ (B : BX (Ainf.R0 p O ε)) (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)) (Ad : O₀ → OAdj B (Ainf.ainfTowerL p O hv ε hε).O), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧ (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) ∧ (∀ a, (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ ρ.act a).left ≫ φ = (e R ((Ad a).a.f s x)).left)) ∧ ∃ (Dt : DualTower (Ainf.ainfTowerL p O hv ε hε)) (D : Dat p g B (Ainf.ainfTowerL p O hv ε hε) Dt (ℤ_[p] ⊗[ℤ] O₀) (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) (Ainf.ainfTowerL p O hv ε hε).c), D.H.P = 0 ∧ D.H.PL = 0 ∧ (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) → (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧ ∀ a j n, (Ad a).a.f (LHom.id (Ainf.ainfTowerL p O hv ε hε).O) (D.L.τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k n) := by
  atlas_forward_decl GlobalTheory.AbelianPeriodDatum.main
end
