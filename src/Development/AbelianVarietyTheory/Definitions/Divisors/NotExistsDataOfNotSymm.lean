import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.PerFactor

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.TautBaseModel





variable {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W)

theorem c₀_zero : T.c₀ 0 = 1 := mul_eq_left.1 ((T.c₀_add 0 0).symm.trans (by rw [add_zero]))

theorem val_τ₀_zero (a : Fin T.r → ℤ) (z J) (hJ : Good T.M.L z J) : val (T.τ₀ 0 a) (𝟙 _) z J = 1 := by
  have h := T.τ₀_add 0 0 a z J hJ
  have f : cubV T.cub z J (T.c₀ 0) (T.c₀ 0) (T.c₀ a) = 1 := by
    rw [c₀_zero]; exact (isCub_cubV T.cub hJ).face _ _
  rw [f, _root_.mul_one, add_zero] at h
  exact mul_eq_left.1 h.symm

theorem τ₀_add_right (a a' a'' : Fin T.r → ℤ) (z J) (hJ : Good T.M.L z J) :
    val (T.τ₀ a (a' + a'')) (𝟙 _) z J * cubV T.cub z J (T.c₀ a) (T.c₀ a') (T.c₀ a'') =
      val (T.τ₀ a a') (𝟙 _) z J * val (T.τ₀ a a'') (𝟙 _) z J := by
  have h := isCub_cubV T.cub hJ
  rw [T.τ₀_symm a _ z J hJ, T.τ₀_symm a a' z J hJ, T.τ₀_symm a a'' z J hJ, h.s01, h.s12]
  exact T.τ₀_add a' a'' a z J hJ


theorem val_τ₀_torus (b : o →+* W) (r : ℕ) (u : Γ((𝟙_ (Over (Sp W))).left, ⊤)ˣ)
    (β : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hβ : ∀ a a', β a a' = β a' a) (a a' : Fin r → ℤ) (z J)
    (hJ : Good (TautBase.torus b r u β hβ).M.L z J) :
    val ((TautBase.torus b r u β hβ).τ₀ a a') (𝟙 _) z J = gm (𝟙 _) z ⊤ (u ^ β a a') :=
  gm_res _ z _ (hJ.mem _ _) _

theorem prod_lamPts_symm {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {Z : Over S} (x y : Z ⟶ B) {U : Type}
    [CommGroup U] (h : (Z.left ⟶ B.left) → U) : ∏ i, h (lamPts x y i) ^ negε i = ∏ i, h (lamPts y x i) ^ negε i := by
  simp only [Fin.prod_univ_four]
  show h (x * y).left ^ (-1 : ℤ) * h x.left ^ (1 : ℤ) * h y.left ^ (1 : ℤ) * h (1 : Z ⟶ B).left ^ (-1 : ℤ) =
    h (y * x).left ^ (-1 : ℤ) * h y.left ^ (1 : ℤ) * h x.left ^ (1 : ℤ) * h (1 : Z ⟶ B).left ^ (-1 : ℤ)
  rw [mul_comm y x, mul_right_comm _ (h x.left ^ (1 : ℤ))]

open InhTate in

theorem tauCoord_symm {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (a b : Q.X)
    (k k' : (FractionRing R)ˣ) (h : Q.TauCoord a b k) (h' : Q.TauCoord b a k') :
    ∃ x x' : R, IsUnit x ∧ IsUnit x' ∧ (k : FractionRing R) * algebraMap R _ x = k' * algebraMap R _ x' := by
  obtain ⟨u, hu, e⟩ := h
  obtain ⟨u', hu', e'⟩ := h'
  obtain ⟨jj, hjj⟩ := GlobalTheory.TauLocal.exists_chart_all Q.M
  have key : ∀ (p q : 𝟙_ (Over (Sp R)) ⟶ Q.B) (t : LB.Gen (LB.LinComb Q.M.L (lamPts p q) negε)), t.IsGen →
      ∃ w : Γ(Sp R, ⊤)ˣ, ∀ z J, Good Q.M.L z J → val t (toUnit (TK R)).left z J =
        gm (𝟙 (TK R).left) z ⊤ (pullTop (jK R) w) * ∏ i, (fun ψ => gm ((toUnit (TK R)).left ≫ ψ) z _
          (Q.M.L.g (J ((toUnit (TK R)).left ≫ ψ)) (jj ψ))) (lamPts p q i) ^ negε i := by
    intro p q t ht
    have htop : (⊤ : (𝟙_ (Over (Sp R))).left.Opens) ≤ LB.wchart Q.M.L (lamPts p q) (fun i => jj (lamPts p q i)) :=
      fun y _ => Set.mem_iInter.2 fun i => hjj _ y
    refine ⟨res htop (t.s (fun i => jj (lamPts p q i))), fun z J hJ => ?_⟩
    refine (gen_trans ht _ z (hJ.mem _ _) (htop trivial)).trans ?_
    rw [mul_comm]
    refine congrArg₂ (· * ·) ?_ rfl
    refine (gm_res _ z htop trivial _).symm.trans (Eq.trans ?_ (gm_pull (𝟙 _) (jK R) z ⊤ trivial _).symm)
    rfl
  obtain ⟨w, hw⟩ := key _ _ u hu
  obtain ⟨w', hw'⟩ := key _ _ u' hu'
  have k₁ : unitOn k * pullTop (jK R) w = unitOn k' * pullTop (jK R) w' := GlobalTheory.TauLocal.eq_of_gm Q.M.isLB fun z J hJ => by
    have s := Q.tau_symm a b z J hJ
    rw [e z J hJ, e' z J hJ, hw z J hJ, hw' z J hJ, ← _root_.mul_assoc, ← _root_.mul_assoc] at s
    rw [map_mul, map_mul]
    refine mul_right_cancel (s.trans (congrArg₂ (· * ·) rfl ?_))
    exact prod_lamPts_symm (Q.c b) (Q.c a) (fun ψ => gm ((toUnit (TK R)).left ≫ ψ) z _
      (Q.M.L.g (J ((toUnit (TK R)).left ≫ ψ)) (jj ψ)))
  have nat := fun v : Γ(Sp R, ⊤)ˣ => congrArg (fun g => g.hom v.val)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  have e₂ := congrArg (fun v => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom v.val) k₁
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w'.val,
    w.isUnit.map _, w'.isUnit.map _, ?_⟩
  refine Eq.trans ?_ (e₂.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat w'))))
  · refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat w)))
    exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply k.val
  · exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply k'.val



end GlobalTheory.PolDeg.TautBaseModel
