import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out.InhTate
open GlobalTheory.Toroidal GlobalTheory.ToricData

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigChart.Model

theorem gm_gv {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : r z ∈ V) (a : Γ(Y, ⊤)ˣ) :
    gm r z V (InhTate.gv a V) = gm (𝟙 Z) z ⊤ (pullTop r a) := by
  rw [InhTate.gv, gm_res r z _ h]
  have := gm_pull (𝟙 Z) r z ⊤ trivial a
  rw [Category.id_comp] at this
  exact this.symm

theorem val_const {W Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ W)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb (Inh.trivLB W) φ ε)} {a : Γ(Y, ⊤)ˣ} (h : IsConst t a) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ W) → (Inh.trivLB W).ι) : Geo.Tor.val t r z J = gm (𝟙 Z) z ⊤ (pullTop r a) := by
  have hm : r z ∈ LB.wchart (Inh.trivLB W) φ (fun k => J (r ≫ φ k)) := by rw [wchart_triv]; trivial
  exact (congrArg (gm r z _) (h _)).trans (gm_gv r z _ hm a)


theorem good_triv {W Z : Scheme.{0}} (z : Z) : Good (Inh.trivLB W) z (fun _ => PUnit.unit) := fun _ => trivial

theorem gm_eq_of_top {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {V : Y.Opens} (hV : V = ⊤) (a : Γ(Y, V)ˣ) :
    gm r z V a = gm (𝟙 Z) z ⊤ (pullTop r (res hV.ge a)) := by
  subst hV
  rw [← gm_gv r z (⊤ : Y.Opens) (show r z ∈ (⊤ : Y.Opens) from trivial), InhTate.gv, res_self, res_self]

theorem one_isGen {W Y : Scheme.{0}} (f g : Y ⟶ W) :
    LB.Gen.IsGen (⟨fun _ => 1⟩ : LB.Iso ((Inh.trivLB W).pull f) ((Inh.trivLB W).pull g)) := by
  intro i j
  have hg : (LB.div ((Inh.trivLB W).pull g) ((Inh.trivLB W).pull f)).g i j = 1 := by
    have h₁ := Inh.linComb_triv_g (fun _ : PUnit => f) (fun _ => 1) i.2 j.2
    have h₂ := Inh.linComb_triv_g (fun _ : PUnit => g) (fun _ => 1) i.1 j.1
    unfold LB.div
    dsimp only
    rw [h₁, h₂, map_one, map_one, inv_one, _root_.mul_one]
  rw [hg, _root_.one_mul]
  rfl

theorem constHom_apply {R k : Type} [CommRing R] [Field k] (ρ : R →+* DualNumber k) (r : R) :
    constHom ρ r = TrivSqZeroExt.inl (ρ r).fst := rfl


variable {R : Type} [CommRing R] [IsDomain R] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (q : X → (FractionRing R)ˣ) {m : ℕ} (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ X)



abbrev A : Type := PowerSeries (PowerSeries ℚ)

abbrev tt : A := PowerSeries.X

abbrev ss : A := PowerSeries.C PowerSeries.X

theorem ss_mem : ss ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C,
    PowerSeries.isUnit_iff_constantCoeff]
  simp

theorem isUnit_one_add {x : A} (h : x ∈ maximalIdeal A) : IsUnit (1 + x) := by
  have := isUnit_one_sub_self_of_mem_nonunits (-x) ((mem_maximalIdeal _).1 (neg_mem h))
  simpa using this

def frm : LinearMap.BilinForm ℤ (ℤ × ℤ) := LinearMap.mk₂ ℤ (fun y z => 2 * (y.1 * z.1 + y.2 * z.2))
  (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

def nrm (y : ℤ × ℤ) : ℕ := (y.1 * y.1 + y.2 * y.2).toNat


def per (v : Aˣ) (b : ℤ × ℤ → ℤ) (y : ℤ × ℤ) : (FractionRing A)ˣ :=
  Units.mk0 (algebraMap A _ (tt ^ nrm y * (v ^ b y : Aˣ)))
    ((map_ne_zero_iff _ (IsFractionRing.injective A _)).2
      (mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (Units.ne_zero _)))




def tang : A →+* DualNumber ℚ := RingHom.comp
  { toFun := fun f : PowerSeries ℚ => TrivSqZeroExt.inl (PowerSeries.constantCoeff f) + TrivSqZeroExt.inr (PowerSeries.coeff 1 f)
    map_one' := by ext <;> simp [PowerSeries.coeff_one]
    map_mul' := fun f g => by
      ext
      · simp
      · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl,
          TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, PowerSeries.coeff_mul]
        rw [Finset.Nat.antidiagonal_succ]
        first
          | (simp [PowerSeries.coeff_zero_eq_constantCoeff]; done)
          | (simp [PowerSeries.coeff_zero_eq_constantCoeff]; ring)
    map_zero' := by ext <;> simp
    map_add' := fun f g => by ext <;> simp [add_add_add_comm] } PowerSeries.constantCoeff





def vs : Aˣ := (isUnit_one_add ss_mem).unit

def vts : Aˣ := (isUnit_one_add (Ideal.mul_mem_left _ tt ss_mem)).unit






theorem isConstAlong_const (Q : DegPre R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X) {k : Type} [Field k]
    (ρ : R →+* DualNumber k) (hρ : constHom ρ = ρ) : IsConstAlong Q t gam ρ 0 := by
  unfold IsConstAlong
  rw [hρ]
  have hL : (Q.P.L.pull (pullback.fst Q.P.A.hom (spMap ρ))).IsLB := LB.isLB_linComb Q.P.isLB _ _
  have hw : ∀ y, (spMap ρ ≫ (Q.c y).left) ≫ Q.P.A.hom = 𝟙 _ ≫ spMap ρ := fun y => by
    rw [Category.assoc, Over.w (Q.c y)]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  refine ⟨(Over.pullback (spMap ρ)).obj Q.P.A, inferInstance, pullback.fst _ _, pullback.fst _ _, idIso _,
    fun y => pullback.lift _ _ (hw y), isGrpPullback_pullback _ _, isGrpPullback_pullback _ _, fun _ _ _ _ => rfl,
    idIso_isGen hL, fun y => ⟨pullback.lift_snd _ _ _, pullback.lift_fst _ _ _, pullback.lift_fst _ _ _⟩,
    fun y z τ₀ _ e he x J hJ => ?_⟩
  obtain rfl : e = 1 := Units.ext (by simpa using he)
  have k : ∀ f : Sp (DualNumber k) ⟶ pullback Q.P.A.hom (spMap ρ),
      gm f x _ ((idIso (Q.P.L.pull (pullback.fst Q.P.A.hom (spMap ρ)))).s
        (fun _ => J (f ≫ pullback.fst Q.P.A.hom (spMap ρ)), fun _ => J (f ≫ pullback.fst Q.P.A.hom (spMap ρ)))) = 1 :=
    fun f => gm_self hL f x (mem_pull.2 (hJ (f ≫ _)))
  erw [k, k, k, k, unitOn_one, map_one]
  simp

theorem toroidalChartsForFan (h : RigidForFan) : GlobalTheory.Published.ToroidalChartsForFan := by
  intro E _ _ _ H Dw hr φ h₁ h₂ l Xo c
  obtain ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇, -⟩ := h E H Dw hr φ h₁ h₂ l Xo c
  exact ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩


end GlobalTheory.RigChart.Model
