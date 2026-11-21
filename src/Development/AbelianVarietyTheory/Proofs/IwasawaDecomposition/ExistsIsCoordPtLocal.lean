import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeffSpecAlgebraMapOfNeg
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM GlobalTheory.LocM.FJ GlobalTheory.Toroidal GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Ex.NumD

variable {O : Type} [CommRing O] (N : NumD O)

def resc (h : N.X → Oˣ) (t : N.X → N.X → Oˣ) (h_add : ∀ x y, h (x + y) = h x * h y * t x y) (h_neg : ∀ x, h (-x) = h x)
    (t_add : ∀ x x' y, t (x + x') y = t x y * t x' y) : NumD O :=
  { N with ψ := fun χ => N.ψ χ * h χ
           even := fun χ => by rw [h_neg, mul_right_comm, N.even χ]
           bimult := fun a a' b => by
             have e : ∀ x y : N.X, N.ψ (x + y) * h (x + y) / (N.ψ x * h x) / (N.ψ y * h y) =
                 N.ψ (x + y) / N.ψ x / N.ψ y * t x y := fun x y => by
               rw [h_add]
               apply Additive.ofMul.injective
               simp only [ofMul_mul, ofMul_div]; abel
             rw [e, e, e, mul_right_comm, N.bimult a a' b, t_add]
             exact mul_mul_mul_comm _ _ _ _ }

end GlobalTheory.Ex.NumD

namespace GlobalTheory.LocM.MultiPt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Terms

variable {R : Type} [CommRing R] [IsDomain R] {C : Type} [Field C] [Algebra (FractionRing R) C] (A : ArcF D R C)

def vec (m : ℕ) (x : D.La) (χ : A.N.X) : A.D₀.X := A.ν.eX ((A.q (m ^ 2) x).1.1.toAdd + m • χ)

def txR (Q : ℕ → A.D₀.X → Cˣ) (m : ℕ) (x : D.La) (χ : A.N.X) : C :=
  (Q (m ^ 2) (vec A m x χ) : C) * A.N.txT m (A.q (m ^ 2) x) χ

def evR (Q : ℕ → A.D₀.X → Cˣ) (T : ℕ → A.D₀.X → A.D₀.X → Cˣ) (m j : ℕ) (z x : D.La) (χ : A.N.X) : C :=
  ((Q (m ^ 2) (vec A m x χ) * T j (A.ν.eX (A.q j z).1.1.toAdd) (vec A m x χ) : Cˣ) : C) *
    A.N.evT m (A.q (m ^ 2) x) (A.q j z).1.2 χ

end Terms

def GReal {R : Type} [CommRing R] [IsDomain R] {C : Type} [NormedField C] [Algebra (FractionRing R) C] (o : Full D C)
    (A : ArcF D R C) (Q : ℕ → A.D₀.X → Cˣ) (T : ℕ → A.D₀.X → A.D₀.X → Cˣ) : Prop :=
  o.ρ = A.ρ ∧ (∀ n, 0 < n → o.I.ζ n = A.I.ζ n) ∧ ∀ m, Odd m → o.Theta m (fun x => ∑' χ, txR A Q m x χ) ∧
    ∀ j, 0 < j → ∀ z, o.Coord m (o.I.ev j z) fun x => ∑' χ, evR A Q T m j z x χ

def mQ {X : Type} [AddCommGroup X] {C : Type} [Field C] {r : ℕ} (δ : Fin r → LinearMap.BilinForm ℤ X) (ρ : Fin r → ℕ → Cˣ)
    (n : ℕ) (w : X) : Cˣ := ∏ i, ρ i n ^ (δ i w w / 2)

def mT {X : Type} [AddCommGroup X] {C : Type} [Field C] {r : ℕ} (δ : Fin r → LinearMap.BilinForm ℤ X) (ρ : Fin r → ℕ → Cˣ)
    (n : ℕ) (y w : X) : Cˣ := ∏ i, ρ i n ^ δ i y w

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HasPt (Y : Model Xo c β) (m : ℕ) {κ : Type} [Field κ] (x : Sp κ ⟶ Xo.XF c) (ζ : κ) (v : D.La → κ)
    (w : D.La → D.La → κ) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (f : κ →+* Ω) (o : Full D Ω), FullAt Y (spMap f ≫ x) o ∧ (o.I.ζ (m ^ 2) : Ω) = f ζ ∧
    o.Theta m (fun a => f (v a)) ∧ ∀ z, o.Coord m (o.I.ev l.M' z) fun a => f (w z a)

def reform {A₀ : Type} [CommRing A₀] [IsDomain A₀] {b : O →+* A₀} {a : ArcIn D l β A₀ b} {F : Type} [Field F]
    [Algebra (FractionRing A₀) F] (A : Lift a F) (ga : levelForms H l.M' a.D₀.X) (h : ga ∈ admitted H l.M' a.D₀.X) :
    Lift (withForm a ga h) F :=
  { A with
    be := { be := ga.1.comp A.ν.eX.toIntLinearEquiv.toLinearMap A.ν.eX.toIntLinearEquiv.toLinearMap
            symm := fun _ _ => ga.2.1 _ _
            pos := fun y hy => h.1 _ ((map_ne_zero_iff _ A.ν.eX.injective).2 hy)
            dvd := fun _ _ => h.2 _ _ }
    be_eq := fun _ _ => rfl }

end GlobalTheory.LocM.MultiPt

end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM GlobalTheory.LocM.FJ GlobalTheory.Toroidal GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LocM.MultiPt
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.CoordReduce

open ReciprocityTheory.ChartRestriction.G.Out in

theorem exists_isCoordPt_local (h₁ : Laws) (h₂ : Laws2) {B : Scheme.{0}} [IsLocallyNoetherian B] (P : PolAV B)
    {R : Type} [CommRing R] [IsLocalRing R] (s : Sp R ⟶ B) {k : ℕ} (hk : Odd k) (hu : IsUnit (k : R)) {J : Type}
    (x : J → (Over.mk s ⟶ P.A)) (hx : ∀ i, x i ^ k ^ 2 = 1) (z : Over.mk s ⟶ P.A) :
    ∃ w : J → R, IsCoordPt P k x z fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w i) := by
  have hG := h₁.globalFns
  have hL := P.isLB
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  obtain ⟨V, hV, b, hb⟩ := h₂.secBaseChangeAny B P 1 le_rfl (s (IsLocalRing.closedPoint R))
  obtain ⟨t, rfl⟩ : ∃ t : Sp R ⟶ (overRes (T := baseOver B) V).left, t ≫ (overRes (T := baseOver B) V).hom = s :=
    ⟨IsOpenImmersion.lift V.ι s (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact (IsLocalRing.specializes_closedPoint (R := R) p).mem_open (s ⁻¹ᵁ V).isOpen hV),
      (congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩
  obtain ⟨-, hsp⟩ := hb _ t (fun i => VVRank.pullS P.A _ (homAt t) (b i)) fun i => VVRank.isPullSec_pullS _ _ _ _
  haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨th₀, hth₀⟩ := ThetaLocal.exists_generator _ hsp
  let T : Over B := baseAt t
  obtain ⟨th, hth⟩ := ThetaPtExist.exists_isGenSec_of_retract hL (𝟙 T) (𝟙 T) (Category.comp_id _) th₀ hth₀
  obtain ⟨α₀, hα₀⟩ := h₁.mulPull B P k
  obtain ⟨α, hα, -⟩ := VVRank.exists_gen_pullTo (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left]) α₀ hα₀
    (snd T P.A).left (fun i => by
      fin_cases i
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _)
    ((k : ℤ) ^ 2) 1 α hα th
  have hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ := fun i => by
    obtain ⟨U, hU, θ, hθ⟩ := (sym B P (k ^ 2) hk.pow T (x i) (hx i)).1 (IsLocalRing.closedPoint R)
    obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
    let h : T ⟶ overRes (T := T) ⊤ := Over.homMk (Sp R).topIso.inv (by
      show (Sp R).topIso.inv ≫ (⊤ : (Sp R).Opens).ι ≫ _ = _
      rw [Scheme.toIso_inv_ι_assoc])
    have hh : h ≫ overResι ⊤ = 𝟙 _ := Over.OverMorphism.ext (Scheme.toIso_inv_ι (Sp R))
    obtain ⟨θ', hθ'⟩ := GlobalLift.exists_symLift_pull P.isLB h hθ
    rw [← Category.assoc, hh, Category.id_comp] at hθ'
    rw [← Nat.cast_pow]
    exact ⟨θ', hθ'⟩
  choose U hU using hU
  choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull hL (translT P.A (U i).pt) (translPt P.A (U i).pt)
    (lift_snd _ _) ((k : ℤ) ^ 2) ((k : ℤ) ^ 2) (U i).φ (U i).isGen s₁
  obtain ⟨c, hc⟩ := Geo.Tor.exists_chart hL (z.left (IsLocalRing.closedPoint R))
  obtain ⟨τ, hτ⟩ := AbSquare.exists_gen_of_mem_chart hL (Y := T.left) (K := Fin 1) (fun _ => z.left)
    (fun _ => (k : ℤ) ^ 2) (fun _ => c) fun _ y =>
      ((IsLocalRing.specializes_closedPoint (R := R) y).map z.left.continuous).mem_open (P.L.U c).isOpen hc
  choose w hw using fun i => ThetaPtExist.exists_isValueAt hL (s₂ i) z τ hτ
  refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (w i), hk, ?_, th, s₁, α, τ, U, s₂, hth, hα, hτ, hs₁,
    hU, hs₂, fun i => ?_⟩
  · have := hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  · convert hw i using 1
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply (w i)

open ReciprocityTheory.ChartRestriction.G.Out in

theorem isCoordPt_map (h₂ : Laws2) {B : Scheme.{0}} (P : PolAV B) {R K : Type} [CommRing R] [CommRing K]
    (j : R →+* K) {s : Sp R ⟶ B} {x : Sp K ⟶ B} (hx : spMap j ≫ s = x) {k : ℕ} {J : Type}
    {p : J → (Over.mk s ⟶ P.A)} (hp : ∀ i, p i ^ k ^ 2 = 1) {z : Over.mk s ⟶ P.A} {w : J → R}
    (H : IsCoordPt P k p z fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w i)) :
    IsCoordPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i)
      ((Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ z)
      fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (j (w i)) := by
  have : IsAffine (Over.mk s).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  let jx : Over.mk x ⟶ Over.mk s := Over.homMk (spMap j) hx
  have Q := FullExtend.isCoordPt_move (f := 𝟙 B) (T := Over.mk x) (T₀ := Over.mk s) jx.left
    (ObjComp.isGrpPullback_id P.A) (DescendedPrincipal.lbIso_pull_id P.isLB).symm (B := Over.mk x) (𝟙 _) jx
    (Category.id_comp _) (hx.trans (Category.comp_id _).symm)
    (fun th₀ h => EmbPull.isGenSec_pullS P h₂.secBaseChangeAny jx h) (x := fun i => jx ≫ p i) (x₀ := p)
    (fun i => (Category.comp_id _).symm) (fun i => by rw [← MonObj.comp_pow, hp i, MonObj.comp_one])
    (z := jx ≫ z) (z₀ := z) (Category.comp_id _).symm H
  convert Q using 2 with a
  exact congrArg (fun q => q.hom (w a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))


end GlobalTheory.CoordReduce
end
end
