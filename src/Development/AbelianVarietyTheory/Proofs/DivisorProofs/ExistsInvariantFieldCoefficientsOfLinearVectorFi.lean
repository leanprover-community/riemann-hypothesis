import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueAtInvariantFieldTranslateSqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLieBasisCoeffsOfDerivationAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TvELeft

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLieBasis_dualPoints_of_tangentModule_basis : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ} (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)), IsLieBasis (fun a => GlobalTheory.VertCoeffRing.tvE (v a)) := by
  first | exact @GlobalTheory.VertCoeffRing.isLieBasis_tvE | exact GlobalTheory.VertCoeffRing.isLieBasis_tvE | (intros; apply GlobalTheory.VertCoeffRing.isLieBasis_tvE <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_at_invariantField_translate_sqZero : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {u : TanM (𝟙 (Sp R)) G} {dd : Fld G.left}, IsInv G u dd → ∀ {B : Type} [CommRing B] [Algebra R B]
    (e : B) (he : e * e = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
    ∃ h' : ⊤ ≤ ((ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ GlobalTheory.VertCoeffRing.tvE u) * z).left ⁻¹ᵁ O, ∀ f,
      GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + e * GlobalTheory.TangentOrigin.evalPt z.left O h (dd O f) := by
  first | exact @GlobalTheory.VertCoeffRing.evalPt_tvE_mul | exact GlobalTheory.VertCoeffRing.evalPt_tvE_mul | (intros; apply GlobalTheory.VertCoeffRing.evalPt_tvE_mul <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_lieBasis_coeffs_of_derivation_affineOpen : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {n : ℕ} (v : Fin n → (epsR R ⟶ G)), IsLieBasis v → ∀ (dd : Fin n → Fld G.left),
    (∀ (B : Type) [CommRing B] [Algebra R B] (e : Fin n → B) (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
      ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp v e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
        GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + ∑ i, e i * GlobalTheory.TangentOrigin.evalPt z.left O h (dd i O f)) →
    ∀ (V V' : G.left.Opens), IsAffineOpen V → IsAffineOpen V' → V' ≤ V → ∀ (δ : Γ(G.left, V) → Γ(G.left, V')),
    (∀ f f', δ (f + f') = δ f + δ f') → (∀ f f', δ (f * f') = rsT f V' * δ f' + rsT f' V' * δ f) →
    (∀ r, δ (constFn G.hom V r) = 0) →
    ∃! c : Fin n → Γ(G.left, V'), ∀ f, δ f = ∑ a, c a * rsT (dd a V f) V' := by
  first | exact @GlobalTheory.VertCoeffRing.existsUnique_coeff_affine_ring | exact GlobalTheory.VertCoeffRing.existsUnique_coeff_affine_ring | (intros; apply GlobalTheory.VertCoeffRing.existsUnique_coeff_affine_ring <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.VertCoeffGlue

theorem affine_cover {X : Scheme.{0}} (O : X.Opens) :
    O ≤ ⨆ l : {V : X.Opens // IsAffineOpen V ∧ V ≤ O}, l.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (O : Set X) from hx) O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, fun y hy => hle hy⟩, hxU⟩

theorem exists_coeff : ∀ {X : Scheme.{0}} {n : ℕ} (W : X.Opens) (δ : Fld X) (dd : Fin n → Fld X), IsField W δ → (∀ a, IsField ⊤ (dd a)) →
    (∀ V V' : X.Opens, IsAffineOpen V → IsAffineOpen V' → V ≤ W → V' ≤ V →
      ∃! c : Fin n → Γ(X, V'), ∀ f : Γ(X, V), rsT (δ V f) V' = ∑ a, c a * rsT (dd a V f) V') →
    ∃ c : Fin n → Γ(X, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  intro X n W δ dd hδ hdd H
  let J : Type := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  choose c hc using fun j : J => (H j.1 j.1 j.2.1 j.2.1 j.2.2 le_rfl).exists
  have hl : ∀ (l : J) (O : X.Opens) (h : l.1 ≤ O), O ≤ W → ∀ f : Γ(X, O),
      rsT (δ O f) l.1 = ∑ a, c l a * rsT (dd a O f) l.1 := by
    intro l O h hO f
    have e1 := hδ.2.2 O l.1 h hO f
    have e2 := hc l (resG X h f)
    simp only [GlobalTheory.KS.rsT_self] at e2
    rw [GlobalTheory.KS.rsT_of_le h, ← e1, e2]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hdd a).2.2 O l.1 h le_top f, GlobalTheory.KS.rsT_of_le h]
  have sub : ∀ j l : J, l.1 ≤ j.1 → ∀ a, rsT (c j a) l.1 = c l a := by
    intro j l h a
    refine congrFun ((H j.1 l.1 j.2.1 l.2.1 j.2.2 h).unique (y₁ := fun a => rsT (c j a) l.1) (y₂ := c l) ?_ ?_) a
    · intro f
      have := hc j f
      simp only [GlobalTheory.KS.rsT_self] at this
      rw [this, GlobalTheory.KS.rsT_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [GlobalTheory.KS.rsT_mul]
    · exact hl l j.1 h j.2.2
  have glue : ∀ a, ∃ s : Γ(X, W), ∀ j : J, rsT s j.1 = c j a := fun a => by
    refine GlobalTheory.KS.exists_rsT_eq (fun j : J => j.1) (fun j => j.2.2) (affine_cover W) (fun j => c j a)
      fun j k => ?_
    refine GlobalTheory.KS.eq_of_rsT_eq (fun l : {V : X.Opens // IsAffineOpen V ∧ V ≤ j.1 ⊓ k.1} => l.1)
      (fun l => l.2.2) (affine_cover _) _ _ fun l => ?_
    have hj : l.1 ≤ j.1 := l.2.2.trans inf_le_left
    have hk : l.1 ≤ k.1 := l.2.2.trans inf_le_right
    rw [GlobalTheory.KS.rsT_rsT inf_le_left l.2.2, GlobalTheory.KS.rsT_rsT inf_le_right l.2.2,
      sub j ⟨l.1, l.2.1, hj.trans j.2.2⟩ hj, sub k ⟨l.1, l.2.1, hk.trans k.2.2⟩ hk]
  choose s hs using glue
  refine ⟨s, fun O hO f => ?_⟩
  refine GlobalTheory.KS.eq_of_rsT_eq (fun l : {V : X.Opens // IsAffineOpen V ∧ V ≤ O} => l.1) (fun l => l.2.2)
    (affine_cover O) _ _ fun l => ?_
  rw [hl ⟨l.1, l.2.1, l.2.2.trans hO⟩ O l.2.2 hO f, GlobalTheory.KS.rsT_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_rsT hO l.2.2, hs a ⟨l.1, l.2.1, l.2.2.trans hO⟩]

end GlobalTheory.VertCoeffGlue
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vectorField_coeffs_glued_from_affineOpens : ∀ {X : Scheme.{0}} {n : ℕ} (W : X.Opens) (δ : Fld X) (dd : Fin n → Fld X), IsField W δ → (∀ a, IsField ⊤ (dd a)) →
    (∀ V V' : X.Opens, IsAffineOpen V → IsAffineOpen V' → V ≤ W → V' ≤ V →
      ∃! c : Fin n → Γ(X, V'), ∀ f : Γ(X, V), rsT (δ V f) V' = ∑ a, c a * rsT (dd a V f) V') →
    ∃ c : Fin n → Γ(X, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  atlas_forward_decl GlobalTheory.VertCoeffGlue.exists_coeff
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VertCoeffRing
open GlobalTheory.TangentOrigin
open GlobalTheory.KS (rsT_add rsT_mul rsT_zero)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem evalPt_lieExp {m : ℕ} (u : Fin m → TanM (𝟙 (Sp R)) G) (dd : Fin m → Fld G.left)
    (hd : ∀ i, IsInv G (u i) (dd i)) (B : Type) [CommRing B] [Algebra R B] (e : Fin m → B)
    (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens)
    (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp (fun i => tvE (u i)) e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f) := by
  induction m with
  | zero =>
    have : GlobalTheory.SqZero.lieExp (fun i => tvE (u i)) e (fun i => he i i) * z = z := by
      simp [GlobalTheory.SqZero.lieExp]
    rw [this]
    exact ⟨h, fun f => by simp⟩
  | succ m ih =>
    obtain ⟨h₁, H₁⟩ := ih (fun i => u i.succ) (fun i => dd i.succ) (fun i => hd i.succ) (fun i => e i.succ)
      (fun i j => he _ _)
    obtain ⟨h₂, H₂⟩ := GlobalTheory.T.value_at_invariantField_translate_sqZero (hd 0) (e 0) (he 0 0) _ O h₁
    have : GlobalTheory.SqZero.lieExp (fun i => tvE (u i)) e (fun i => he i i) * z =
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R (e 0) (he 0 0)) ≫ tvE (u 0)) *
          (GlobalTheory.SqZero.lieExp (fun i => tvE (u i.succ)) (fun i => e i.succ) (fun i => he i.succ i.succ) * z) := by
      rw [GlobalTheory.SqZero.lieExp, GlobalTheory.SqZero.lieExp, Fin.prod_univ_succ, _root_.mul_assoc]
    rw [this]
    refine ⟨h₂, fun f => ?_⟩
    rw [H₂, H₁, H₁, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
    simp only [← _root_.mul_assoc, he, zero_mul, Finset.sum_const_zero]
    ring

theorem exists_coeff : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) →
    ∀ (W : G.left.Opens) (δ : Fld G.left), IsField W δ → (∀ O, O ≤ W → ∀ r, δ O (constFn G.hom O r) = 0) →
    ∃ c : Fin n → Γ(G.left, W), ∀ O, O ≤ W → ∀ f, δ O f = ∑ a, rsT (c a) O * dd a O f := by
  intro R _ G _ _ hs n v dd hd W δ hδ hc
  have hb := GlobalTheory.T.isLieBasis_dualPoints_of_tangentModule_basis v
  refine GlobalTheory.T.exists_vectorField_coeffs_glued_from_affineOpens W δ dd hδ (fun a => (hd a).1) fun V V' hV hV' hVW hV'V => ?_
  exact GlobalTheory.T.existsUnique_lieBasis_coeffs_of_derivation_affineOpen _ hb dd (fun B _ _ e he z O h => evalPt_lieExp v dd hd B e he z O h) V V' hV hV' hV'V
    (fun f => rsT (δ V f) V') (fun f f' => by simp only [hδ.1 V hVW, rsT_add])
    (fun f f' => by simp only [hδ.2.1 V hVW, rsT_add, rsT_mul])
    (fun r => by simp only [hc V hVW r, rsT_zero])

end GlobalTheory.VertCoeffRing
end
end
