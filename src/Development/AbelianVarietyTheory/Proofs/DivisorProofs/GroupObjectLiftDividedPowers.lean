import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleLiftOfNilpotentDividedPowersThickening
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LamIsoOfDoublingPullbackEqDiagonalSq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteClosedSubschemeRepresentsKernelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OActLift

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option autoImplicit false in

theorem _root_.GlobalTheory.OActLift.isMonHom_mul_of_comm {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (f g : G ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  rw [Hom.mul_def]
  infer_instance

theorem exists_oAct_lift : GlobalTheory.Published.GrothendieckDeformation → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I),
    IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
      (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (O : Type) [CommRing O] (a₀ : OAct O A₀), (∀ (x : O), ∀ d ∈ liftFil κ h, act κ (spMap π) a₀ x d ∈ liftFil κ h) →
      ∃ a : OAct O A, ∀ x, (a₀.act x).left ≫ i = i ≫ (a.act x).left := by
  intro GD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg O _ a₀ hfil
  have HL := (GD R I κ hκ R₀ π hπ hI).2.2
  haveI : IsCommMonObj A := hA.comm
  have key : ∀ x : O, ∃! f : A ⟶ A, IsMonHom f ∧ i ≫ f.left = (a₀.act x).left ≫ i := fun x ↦ by
    haveI := a₀.hom x
    exact HL g A₀ A i h hA hg g A₀ A i h hA hg (a₀.act x) (fun d hd ↦ hfil x d hd)
  choose f hf huniq using key
  refine ⟨⟨f, fun x ↦ (hf x).1, ?_, ?_, ?_⟩, fun x ↦ (hf x).2.symm⟩
  · refine (huniq 1 (𝟙 _) ⟨inferInstance, ?_⟩).symm
    rw [a₀.one]
    simp
  · intro x y
    haveI := (hf x).1
    haveI := (hf y).1
    refine (huniq (x * y) (f x ≫ f y) ⟨inferInstance, ?_⟩).symm
    rw [a₀.mul, Over.comp_left, Over.comp_left, ← Category.assoc, (hf x).2, Category.assoc, (hf y).2,
      Category.assoc]
  · intro x y
    haveI := (hf x).1
    haveI := (hf y).1
    refine (huniq (x + y) (f x * f y) ⟨isMonHom_mul_of_comm _ _, ?_⟩).symm
    rw [a₀.add]
    let j : Over.mk (A₀.hom ≫ spMap π) ⟶ A := Over.homMk i h.1.w
    have e := h.2 A₀ (a₀.act x) (a₀.act y) (j ≫ f x) (j ≫ f y) (hf x).2 (hf y).2
    rw [← MonObj.comp_mul] at e
    exact e

end GlobalTheory.OActLift
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_lift_crystalline_comparison : GlobalTheory.Published.GrothendieckDeformation → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I),
    IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
      (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (O : Type) [CommRing O] (a₀ : OAct O A₀), (∀ (x : O), ∀ d ∈ liftFil κ h, act κ (spMap π) a₀ x d ∈ liftFil κ h) →
      ∃ a : OAct O A, ∀ x, (a₀.act x).left ≫ i = i ≫ (a.act x).left := by
  atlas_forward_decl GlobalTheory.OActLift.exists_oAct_lift
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_lift_of_nilpotentDividedPowers_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (β : X₀.left ⟶ X.left), IsPullback β X₀.hom X.hom (spMap π) →
      LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L₀ : LB X₀.left), L.IsLB → L₀.IsLB → LBIso L₀ (L.pull β) →
      Out.RelAmple X₀ L₀ → Out.RelAmple X L := by
  first | exact @GlobalTheory.AmpleNilThickening.relAmple_of_isNilDP | exact GlobalTheory.AmpleNilThickening.relAmple_of_isNilDP | (intros; apply GlobalTheory.AmpleNilThickening.relAmple_of_isNilDP <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic

namespace GlobalTheory.BirigidLift

theorem symm_of_lift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (P₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) →
    ∀ (P : LB (A ⊗ A).left), P.IsLB → HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) →
      HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso (P.pull l) P₀ →
      LBIso P (P.pull (lift (snd A A) (fst A A)).left) := by
  intro HG HD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg l hl L hL aL P₀ hP₀ hsym P hP h₁ h₂ e
  obtain ⟨l₁, l₂⟩ := hl
  have hs : (P.pull (lift (snd A A) (fst A A)).left).IsLB := pull_isLB hP _
  have h₁' : Triv (ev (swap P) (1 : A ⟶ A) (𝟙 A)) := by
    rw [triv_ev_iff hs, evc_swap hP hs, ← triv_ev_iff hP]
    exact h₂
  have h₂' : Triv (ev (swap P) (𝟙 A) (1 : A ⟶ A)) := by
    rw [triv_ev_iff hs, evc_swap hP hs, ← triv_ev_iff hP]
    exact h₁
  have sq : l ≫ (lift (snd A A) (fst A A)).left = (lift (snd A₀ A₀) (fst A₀ A₀)).left ≫ l := by
    apply left_ext
    · rw [Category.assoc, Category.assoc, lift_left_fst, l₂, l₁, lift_left_fst_assoc]
    · rw [Category.assoc, Category.assoc, lift_left_snd, l₁, l₂, lift_left_snd_assoc]
  have hl0 := pull_isLB hP l
  have e' : LBIso ((swap P).pull l) P₀ := by
    refine (cls_eq_iff (pull_isLB hs l) hP₀).1 ?_
    rw [cls_pull hs l, cls_pull hP, ← pull_comp, sq, pull_comp, ← cls_pull hP l hl0,
      (cls_eq_iff hl0 hP₀).2 e, ← cls_pull hP₀ _ (pull_isLB hP₀ _)]
    exact ((cls_eq_iff hP₀ (pull_isLB hP₀ _)).2 hsym).symm
  exact lift_unique HG HD.1 hκ hπ hI hA hg hA hg h h l₁ l₂ hL aL hL aL hP₀ hP h₁ h₂ e hs h₁' h₂' e'

end GlobalTheory.BirigidLift
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birigidified_lift_symmetric_of_symmetric_reduction : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (P₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) →
    ∀ (P : LB (A ⊗ A).left), P.IsLB → HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) →
      HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso (P.pull l) P₀ →
      LBIso P (P.pull (lift (snd A A) (fst A A)).left) := by
  atlas_forward_decl GlobalTheory.BirigidLift.symm_of_lift
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.AbDual GlobalTheory.CechPic

namespace GlobalTheory.BirigidLift

theorem lift_div : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (P₀ Q₀ S₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → Q₀.IsLB → S₀.IsLB → LBIso Q₀ (LB.div S₀ P₀) →
    ∀ (P Q S : LB (A ⊗ A).left), P.IsLB → Q.IsLB → S.IsLB →
      HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (S.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (S.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      LBIso (P.pull l) P₀ → LBIso (Q.pull l) Q₀ → LBIso (S.pull l) S₀ → LBIso Q (LB.div S P) := by
  intro HG HD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg l hl L hL aL P₀ Q₀ S₀ hP₀ hQ₀ hS₀ eQ₀ P Q S hP hQ hS
    tP₁ tP₂ tQ₁ tQ₂ tS₁ tS₂ eP eQ eS
  have hd : (LB.div S P).IsLB := LB.isLB_div hS hP
  have triv : ∀ (a b : A ⟶ A), HasGen (S.pull (lift a b).left) → HasGen (P.pull (lift a b).left) →
      GlobalTheory.AbLaw.Triv (ev (LB.div S P) a b) := by
    intro a b t₁ t₂
    rw [triv_ev_iff hd, evc, cls_div hS hP hd, map_sub]
    have z₁ := (cls_eq_zero_iff (pull_isLB hS (lift a b).left)).2 t₁
    have z₂ := (cls_eq_zero_iff (pull_isLB hP (lift a b).left)).2 t₂
    rw [cls_pull hS] at z₁
    rw [cls_pull hP] at z₂
    rw [z₁, z₂, sub_zero]
  have red : LBIso ((LB.div S P).pull l) Q₀ := by
    refine (cls_eq_iff (pull_isLB hd l) hQ₀).1 ?_
    rw [cls_pull hd, cls_div hS hP hd, map_sub, ← cls_pull hS l (pull_isLB hS l), ← cls_pull hP l (pull_isLB hP l),
      (cls_eq_iff (pull_isLB hS l) hS₀).2 eS, (cls_eq_iff (pull_isLB hP l) hP₀).2 eP,
      (cls_eq_iff hQ₀ (LB.isLB_div hS₀ hP₀)).2 eQ₀, cls_div hS₀ hP₀]
  exact lift_unique HG HD.1 hκ hπ hI hA hg hA hg h h hl.1 hl.2 hL aL hL aL hQ₀ hQ tQ₁ tQ₂ eQ hd
    (triv _ _ tS₁ tP₁) (triv _ _ tS₂ tP₂) red

end GlobalTheory.BirigidLift
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_lift_de_rham_unique : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (P₀ Q₀ S₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → Q₀.IsLB → S₀.IsLB → LBIso Q₀ (LB.div S₀ P₀) →
    ∀ (P Q S : LB (A ⊗ A).left), P.IsLB → Q.IsLB → S.IsLB →
      HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (S.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (S.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      LBIso (P.pull l) P₀ → LBIso (Q.pull l) Q₀ → LBIso (S.pull l) S₀ → LBIso Q (LB.div S P) := by
  atlas_forward_decl GlobalTheory.BirigidLift.lift_div
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published

namespace GlobalTheory.BirigidLift

theorem pull_one_prod_of_lift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (u₀ : A₀ ⟶ A₀) (u : A ⟶ A) [IsMonHom u₀] [IsMonHom u], u₀.left ≫ i = i ≫ u.left →
    ∀ (P₀ Q₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → Q₀.IsLB → LBIso Q₀ (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ u₀)).left) →
    ∀ (P Q : LB (A ⊗ A).left), P.IsLB → Q.IsLB →
      HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      LBIso (P.pull l) P₀ → LBIso (Q.pull l) Q₀ → LBIso Q (P.pull (lift (fst A A) (snd A A ≫ u)).left) := by
  intro HG HD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg l hl L hL aL u₀ u _ _ hu P₀ Q₀ hP₀ hQ₀ eQ₀ P Q hP hQ
    p₁ p₂ q₁ q₂ eP eQ
  set m : (A ⊗ A).left ⟶ (A ⊗ A).left := (lift (fst A A) (snd A A ≫ u)).left with hm
  set m₀ : (A₀ ⊗ A₀).left ⟶ (A₀ ⊗ A₀).left := (lift (fst A₀ A₀) (snd A₀ A₀ ≫ u₀)).left with hm₀
  have hP' : (P.pull m).IsLB := pull_isLB hP m
  have hev : ∀ (a : A ⟶ A) (t : A ⟶ A), evc hP' a t = evc hP a (t ≫ u) := fun a t ↦ by
    have := evc_ev hP (fst A A) (snd A A ≫ u) hP' a t
    rw [this, lift_fst, lift_snd_assoc]
  have z₁ : evc hP (1 : A ⟶ A) (𝟙 A) = 0 := (triv_ev_iff hP _ _).1 p₁
  have z₂ : evc hP (𝟙 A) (1 : A ⟶ A) = 0 := (triv_ev_iff hP _ _).1 p₂
  have h₁' : Triv (ev (P.pull m) (1 : A ⟶ A) (𝟙 A)) := by
    rw [triv_ev_iff hP', hev, Category.id_comp]
    have := pull_evc hP u (1 : A ⟶ A) (𝟙 A)
    rw [z₁, map_zero, Category.comp_id, MonObj.comp_one] at this
    exact this.symm
  have h₂' : Triv (ev (P.pull m) (𝟙 A) (1 : A ⟶ A)) := by
    rw [triv_ev_iff hP', hev, MonObj.one_comp]
    exact z₂
  have sq : l ≫ m = m₀ ≫ l := by
    apply left_ext
    · rw [Category.assoc, Category.assoc, hm, hm₀, lift_left_fst, hl.1, lift_left_fst_assoc]
    · rw [Category.assoc, Category.assoc, hm, hm₀, lift_left_snd, hl.2, lift_left_snd_assoc, Over.comp_left,
        Over.comp_left, ← Category.assoc, hl.2, Category.assoc, Category.assoc, hu]
  have e' : LBIso ((P.pull m).pull l) Q₀ := by
    refine (cls_eq_iff (pull_isLB hP' l) hQ₀).1 ?_
    rw [cls_pull hP' l, cls_pull hP m, ← pull_comp, sq, pull_comp, ← cls_pull hP l (pull_isLB hP l),
      (cls_eq_iff (pull_isLB hP l) hP₀).2 eP, ← cls_pull hP₀ m₀ (pull_isLB hP₀ m₀),
      (cls_eq_iff hQ₀ (pull_isLB hP₀ m₀)).2 eQ₀]
  exact lift_unique HG HD.1 hκ hπ hI hA hg hA hg h h hl.1 hl.2 hL aL hL aL hQ₀ hQ q₁ q₂ eQ hP' h₁' h₂' e'

end GlobalTheory.BirigidLift
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birigidified_lift_pullback_one_prod_endomorphism : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (u₀ : A₀ ⟶ A₀) (u : A ⟶ A) [IsMonHom u₀] [IsMonHom u], u₀.left ≫ i = i ≫ u.left →
    ∀ (P₀ Q₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → Q₀.IsLB → LBIso Q₀ (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ u₀)).left) →
    ∀ (P Q : LB (A ⊗ A).left), P.IsLB → Q.IsLB →
      HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      LBIso (P.pull l) P₀ → LBIso (Q.pull l) Q₀ → LBIso Q (P.pull (lift (fst A A) (snd A A ≫ u)).left) := by
  first | exact @GlobalTheory.BirigidLift.pull_one_prod_of_lift | exact GlobalTheory.BirigidLift.pull_one_prod_of_lift | (intros; apply GlobalTheory.BirigidLift.pull_one_prod_of_lift <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PoincarePull

theorem exists_hom_triv_iff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (D : Over (Sp R)) [GrpObj D] (Q : LB (A ⊗ D).left), GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsDual D A (GlobalTheory.AbDual.swap Q) →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ P : LB (A ⊗ A).left, P.IsLB →
    HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
    ∃ x : A ⟶ D, IsMonHom x ∧ ∀ (T : Over (Sp R)) (y : T ⟶ A),
      (HasGen (P.pull (lift (fst A T) (snd A T ≫ y)).left) ↔ y ≫ x = 1) := by
  intro R _ A _ hA D _ Q q q' L hL aL P hP h₁ h₂
  obtain ⟨H, hH, aH⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod hA hA hL aL hL aL
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH aH hP h₁ h₂
  obtain ⟨x, hx, e⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP a₁ a₂
  refine ⟨x, hx, fun T y ↦ ?_⟩
  have k := GlobalTheory.AbDual.triv_ev_iff hP (fst A T) (snd A T ≫ y)
  rw [GlobalTheory.BirigidLift.evc_of_cls q.isLB hP e, Category.assoc, ← GlobalTheory.AbDual.triv_ev_iff q.isLB] at k
  refine k.trans ⟨fun h ↦ q.eq_one (y ≫ x) h, fun h ↦ ?_⟩
  rw [h, GlobalTheory.AbDual.triv_ev_iff q.isLB, MonObj.comp_one]
  exact GlobalTheory.AbDual.evc_one_right q.isLB q.zero _

end GlobalTheory.PoincarePull
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open scoped nonZeroDivisors

namespace GlobalTheory.PartitionFracId

theorem exists_partition (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) :
    ∃ (n : ℕ) (d : Fin n → 𝔠.elt) (a : Fin n → 𝓞 F),
    (∀ j (e : 𝔠.elt), ∃ b : 𝓞 F, a j • e = b • d j) ∧ ∑ j, a j = 1 := by
  set I : FractionalIdeal (𝓞 F)⁰ F := (𝔠 : FractionalIdeal (𝓞 F)⁰ F) with hI
  set J : FractionalIdeal (𝓞 F)⁰ F := ((𝔠⁻¹ : FracId F) : FractionalIdeal (𝓞 F)⁰ F) with hJ
  have hIJ : I * J = 1 := Units.mul_inv 𝔠
  have hJI : J * I = 1 := by rw [mul_comm]; exact hIJ
  have hmem : ∀ {u v : F}, u ∈ I → v ∈ J → ∃ r : 𝓞 F, (r : F) = u * v := by
    intro u v hu hv
    have h := FractionalIdeal.mul_mem_mul hu hv
    rw [hIJ] at h
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h
    exact ⟨r, hr⟩
  have hmem' : ∀ {u v : F}, v ∈ J → u ∈ I → ∃ r : 𝓞 F, (r : F) = v * u := by
    intro u v hv hu
    have h := FractionalIdeal.mul_mem_mul hv hu
    rw [hJI] at h
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h
    exact ⟨r, hr⟩
  let P : F → Prop := fun x => ∃ (n : ℕ) (d : Fin n → 𝔠.elt) (a : Fin n → 𝓞 F),
    (∀ j (e : 𝔠.elt), ∃ b : 𝓞 F, a j • e = b • d j) ∧ ∑ j, (a j : F) = x
  have h1 : (1 : F) ∈ (I : Submodule (𝓞 F) F) * (J : Submodule (𝓞 F) F) := by
    rw [← FractionalIdeal.coe_mul, hIJ]
    exact FractionalIdeal.one_mem_one _
  have hP : P 1 := by
    refine Submodule.mul_induction_on (C := P) h1 ?_ ?_
    · intro u hu v hv
      obtain ⟨r, hr⟩ := hmem hu hv
      refine ⟨1, fun _ => ⟨u, hu⟩, fun _ => r, ?_, ?_⟩
      · intro j e
        obtain ⟨s, hs⟩ := hmem' (u := (e : F)) hv e.2
        refine ⟨s, Subtype.ext ?_⟩
        show ((r • e : 𝔠.elt) : F) = ((s • (⟨u, hu⟩ : 𝔠.elt) : 𝔠.elt) : F)
        rw [Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def]
        change (r : F) * (e : F) = (s : F) * u
        rw [hr, hs]; ring
      · simp [hr]
    · rintro x y ⟨n, d, a, ha, hx⟩ ⟨m, d', a', ha', hy⟩
      refine ⟨n + m, Fin.append d d', Fin.append a a', ?_, ?_⟩
      · intro j e
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · obtain ⟨b, hb⟩ := ha i e
          exact ⟨b, by simpa using hb⟩
        · obtain ⟨b, hb⟩ := ha' i e
          exact ⟨b, by simpa using hb⟩
      · rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right, hx, hy]
  obtain ⟨n, d, a, ha, hs⟩ := hP
  refine ⟨n, d, a, ha, ?_⟩
  apply RingOfIntegers.coe_injective
  simpa using hs

end GlobalTheory.PartitionFracId
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractional_ideal_partition_of_unity : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F), ∃ (n : ℕ) (d : Fin n → 𝔠.elt) (a : Fin n → 𝓞 F),
    (∀ j (e : 𝔠.elt), ∃ b : 𝓞 F, a j • e = b • d j) ∧ ∑ j, a j = 1 := by
  atlas_forward_decl GlobalTheory.PartitionFracId.exists_partition
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerShift

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

theorem evc_congr {S : Scheme.{0}} {A T Y : Over S} {M N : LB (A ⊗ T).left} (hM : M.IsLB) (hN : N.IsLB)
    (e : LBIso M N) (a : Y ⟶ A) (t : Y ⟶ T) : evc hM a t = evc hN a t := by
  unfold evc
  rw [(cls_eq_iff hM hN).2 e]

theorem ker_shift : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (S : Scheme.{0}) (A : Over S) [GrpObj A]
    (rm : OAct (𝓞 F) A) (P : 𝔠.elt → LB (A ⊗ A).left), (∀ c, (P c).IsLB) →
    (∀ c, LBIso (P c) ((P c).pull (lift (snd A A) (fst A A)).left)) →
    (∀ (a : 𝓞 F) c, LBIso (P (a • c)) ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left)) →
    ∀ (c d : 𝔠.elt) (a b : 𝓞 F), a • d = b • c → ∀ (T : Over S) (y : T ⟶ A),
      HasGen ((P c).pull (lift (fst A T) (snd A T ≫ y)).left) →
      HasGen ((P d).pull (lift (fst A T) (snd A T ≫ (y ≫ rm.act a))).left) := by
  intro F _ _ 𝔠 S A _ rm P hP hsymm hsmul c d a b had T y hy
  have sy : ∀ c (Y : Over S) (u v : Y ⟶ A), evc (hP c) u v = evc (hP c) v u := by
    intro c Y u v
    have hs : ((P c).pull (lift (snd A A) (fst A A)).left).IsLB := pull_isLB (hP c) _
    rw [evc_congr (hP c) hs (hsymm c) u v]
    exact (evc_ev (hP c) (snd A A) (fst A A) hs u v).trans (by rw [lift_snd, lift_fst])
  have sm : ∀ (a : 𝓞 F) c (Y : Over S) (u v : Y ⟶ A), evc (hP (a • c)) u v = evc (hP c) u (v ≫ rm.act a) := by
    intro a c Y u v
    have hs : ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left).IsLB := pull_isLB (hP c) _
    rw [evc_congr (hP (a • c)) hs (hsmul a c) u v]
    exact (evc_ev (hP c) (fst A A) (snd A A ≫ rm.act a) hs u v).trans (by rw [lift_fst, lift_snd_assoc])
  have h0 : evc (hP c) (fst A T) (snd A T ≫ y) = 0 := (triv_ev_iff (hP c) _ _).1 hy
  have h1 := congrArg (CechPic.pull (lift (fst A T ≫ rm.act b) (snd A T)).left) h0
  rw [pull_evc, map_zero, lift_fst, lift_snd_assoc] at h1
  have e1 := sm a d (A ⊗ T) (fst A T) (snd A T ≫ y)
  rw [had] at e1
  show Triv _
  rw [triv_ev_iff (hP d), ← Category.assoc, ← e1, sy, sm, sy]
  exact h1

end GlobalTheory.KerShift
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_bundle_isomorphism_compat : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (S : Scheme.{0}) (A : Over S) [GrpObj A]
    (rm : OAct (𝓞 F) A) (P : 𝔠.elt → LB (A ⊗ A).left), (∀ c, (P c).IsLB) →
    (∀ c, LBIso (P c) ((P c).pull (lift (snd A A) (fst A A)).left)) →
    (∀ (a : 𝓞 F) c, LBIso (P (a • c)) ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left)) →
    ∀ (c d : 𝔠.elt) (a b : 𝓞 F), a • d = b • c → ∀ (T : Over S) (y : T ⟶ A),
      HasGen ((P c).pull (lift (fst A T) (snd A T ≫ y)).left) →
      HasGen ((P d).pull (lift (fst A T) (snd A T ≫ (y ≫ rm.act a))).left) := by
  atlas_forward_decl GlobalTheory.KerShift.ker_shift
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PrincipalModRadical

open GlobalTheory.CechPic GlobalTheory.LamOfDouble

theorem surjective_of_finite {R A : Type} [CommRing R] [CommRing A] (J : Ideal R) (hJ : J ≤ Ideal.jacobson ⊥)
    (φ : R →+* A) (hφ : φ.Finite) (h : ∀ a, ∃ r, a - φ r ∈ J.map φ) : Function.Surjective φ := by
  algebraize [φ]
  have key : (⊤ : Submodule R A) ≤ LinearMap.range (Algebra.linearMap R A) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ fun a _ => ?_
    obtain ⟨r, hr⟩ := h a
    rw [← add_sub_cancel (φ r) a]
    refine Submodule.add_mem_sup ⟨r, rfl⟩ ?_
    rw [Ideal.smul_top_eq_map]
    exact hr
  exact fun a => key (Submodule.mem_top (x := a))

theorem mono_of_section {R : Type} [CommRing R] (J : Ideal R) (hJ : J ≤ Ideal.jacobson ⊥) {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of R)) [IsFinite f] (e : Spec (CommRingCat.of R) ⟶ H)
    (h : ∀ (T : Scheme.{0}) (d : T ⟶ H) (t : T ⟶ Spec (CommRingCat.of (R ⧸ J))),
      d ≫ f = t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) → d = d ≫ f ≫ e) : Mono f := by
  have : IsAffine H := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (H.isoSpec.inv ≫ f)
  obtain ⟨ε, hε⟩ := Spec.map_surjective (e ≫ H.isoSpec.hom)
  have fin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  let q : Γ(H, ⊤) ⟶ CommRingCat.of (Γ(H, ⊤) ⧸ J.map φ.hom) := CommRingCat.ofHom (Ideal.Quotient.mk _)
  let τ : CommRingCat.of (R ⧸ J) ⟶ CommRingCat.of (Γ(H, ⊤) ⧸ J.map φ.hom) :=
    CommRingCat.ofHom (Ideal.quotientMap _ φ.hom Ideal.le_comap_map)
  have h₁ := h _ (Spec.map q ≫ H.isoSpec.inv) (Spec.map τ) (by
    rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_comp]
    rfl)
  have h₂ : q = ε ≫ φ ≫ q := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hφ, hε, ← cancel_mono H.isoSpec.inv, h₁]
    simp
  have sur : Function.Surjective φ.hom := surjective_of_finite J hJ φ.hom fin fun a =>
    ⟨ε.hom a, Ideal.Quotient.eq.1 (congrArg (fun g => g.hom a) h₂)⟩
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ sur
  have e' : f = H.isoSpec.hom ≫ Spec.map φ := by rw [hφ, Iso.hom_inv_id_assoc]
  rw [e']
  infer_instance

end GlobalTheory.PrincipalModRadical
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KernelThickening

theorem exists_closed_equalizer {S : Scheme.{0}} (D : Over S) [IsSeparated D.hom] (n : ℕ) :
    ∀ (A : Over S) (x z : Fin n → (A ⟶ D)), ∃ (K : Over S) (k : K ⟶ A), IsClosedImmersion k.left ∧
      ∀ (T : Over S) (y : T ⟶ A), (∀ j, y ≫ x j = y ≫ z j) ↔ ∃ y' : T ⟶ K, y' ≫ k = y := by
  induction n with
  | zero =>
    intro A x z
    refine ⟨A, 𝟙 A, by rw [Over.id_left]; infer_instance, fun T y => ⟨fun _ => ⟨y, by simp⟩, fun _ j => j.elim0⟩⟩
  | succ n ih =>
    intro A x z
    obtain ⟨K, k, hk, hK⟩ := ih (equalizer (x 0) (z 0)) (fun j => equalizer.ι _ _ ≫ x j.succ)
      (fun j => equalizer.ι _ _ ≫ z j.succ)
    refine ⟨K, k ≫ equalizer.ι _ _, by rw [Over.comp_left]; infer_instance, fun T y => ⟨fun h => ?_, ?_⟩⟩
    · obtain ⟨y', hy'⟩ := (hK T (equalizer.lift y (h 0))).1 fun j => by
        simpa using h j.succ
      exact ⟨y', by rw [← Category.assoc, hy', equalizer.lift_ι]⟩
    · rintro ⟨y', rfl⟩ j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Category.assoc]
        rw [equalizer.condition (x 0) (z 0)]
      · simpa using (hK T (y' ≫ k)).2 ⟨y', rfl⟩ j

theorem mono_of_proper {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (hπ : Function.Surjective π)
    (N : ℕ) (hN : RingHom.ker π ^ N = ⊥) {H : Scheme.{0}} (f : H ⟶ Sp R) [IsProper f] (e : Sp R ⟶ H)
    (h : ∀ (T : Scheme.{0}) (d : T ⟶ H) (t : T ⟶ Sp R₀), d ≫ f = t ≫ spMap π → d = d ≫ f ≫ e) : Mono f := by
  have hnil : ∀ a ∈ RingHom.ker π, a ^ N = 0 := fun a ha => by
    have := Ideal.pow_mem_pow ha N
    rwa [hN, Ideal.mem_bot] at this
  have hinj : Function.Injective f := by
    refine Function.LeftInverse.injective (g := e) fun p => ?_
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (H.fromSpecResidueField p ≫ f)
    have hker : RingHom.ker π ≤ RingHom.ker φ.hom := fun a ha => by
      have : (φ.hom a) ^ N = 0 := by rw [← map_pow, hnil a ha, map_zero]
      exact IsNilpotent.eq_zero ⟨N, this⟩
    let ψ : CommRingCat.of R₀ ⟶ H.residueField p := CommRingCat.ofHom (π.liftOfSurjective hπ ⟨φ.hom, hker⟩)
    have hψ : CommRingCat.ofHom π ≫ ψ = φ := CommRingCat.hom_ext (π.liftOfRightInverse_comp _ _ ⟨φ.hom, hker⟩)
    have h₁ := h _ (H.fromSpecResidueField p) (Spec.map ψ) (by
      rw [← hφ, spMap, ← Spec.map_comp, hψ])
    obtain ⟨q, hq⟩ : ∃ q : Spec (H.residueField p), H.fromSpecResidueField p q = p :=
      ⟨IsLocalRing.closedPoint (H.residueField p), Scheme.fromSpecResidueField_apply _ _⟩
    have h₂ : H.fromSpecResidueField p q = (H.fromSpecResidueField p ≫ f ≫ e) q := congrArg (fun g => g q) h₁
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hq] at h₂
    exact h₂.symm
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_injective hinj
  have : IsFinite f := IsFinite.of_isProper_of_locallyQuasiFinite f
  refine GlobalTheory.PrincipalModRadical.mono_of_section (RingHom.ker π) ?_ f e fun T d t hd => ?_
  · exact fun a ha => Ideal.radical_le_jacobson ⟨N, hnil a ha⟩
  · refine h T d (t ≫ spMap (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom) ?_
    rw [hd, Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext a
    apply (RingHom.quotientKerEquivOfSurjective hπ).injective
    simp

theorem kernel_trivial_of_nilpotent :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π →
    (∃ N : ℕ, RingHom.ker π ^ N = ⊥) → ∀ (A : Over (Sp R)) [GrpObj A], IsProper A.hom →
    ∀ (n : ℕ) (D : Over (Sp R)) [GrpObj D], IsSeparated D.hom → ∀ (x : Fin n → (A ⟶ D)), (∀ j, IsMonHom (x j)) →
    (∀ (T₀ : Over (Sp R₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ A), (∀ j, y ≫ x j = 1) → y = 1) →
    ∀ (T : Over (Sp R)) (y : T ⟶ A), (∀ j, y ≫ x j = 1) → y = 1 := by
  intro R R₀ _ _ π hπ ⟨N, hN⟩ A _ hA n D _ hD x hx h₀
  obtain ⟨K, k, hk, hK⟩ := exists_closed_equalizer D n A x fun _ => 1
  simp only [MonObj.comp_one] at hK
  have : IsProper K.hom := by
    rw [← Over.w k]
    infer_instance
  have one : ∀ T : Over (Sp R), ∃ y : T ⟶ K, y ≫ k = 1 := fun T => (hK T 1).1 fun j => by
    have := hx j
    simp [Hom.one_def]
  have hkx := (hK K k).2 ⟨𝟙 K, Category.id_comp k⟩
  obtain ⟨e, he⟩ := one (𝟙_ _)
  have : Mono K.hom := mono_of_proper π hπ N hN K.hom e.left fun T d t hd => by
    let d' : Over.mk ((Over.mk t).hom ≫ spMap π) ⟶ K := Over.homMk d hd
    have h₁ : d' ≫ k = 1 := h₀ (Over.mk t) _ fun j => by rw [Category.assoc, hkx, MonObj.comp_one]
    have : d' ≫ k = d' ≫ toUnit K ≫ e ≫ k := by
      rw [h₁, he, MonObj.comp_one, MonObj.comp_one]
    rw [← cancel_mono k.left, Category.assoc, Category.assoc]
    exact congrArg (·.left) this
  intro T y hy
  obtain ⟨y₁, hy₁⟩ := (hK T y).1 hy
  obtain ⟨y₂, hy₂⟩ := one T
  rw [← hy₁, ← hy₂, Over.OverMorphism.ext ((cancel_mono K.hom).1 ((Over.w y₁).trans (Over.w y₂).symm))]

end GlobalTheory.KernelThickening
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomorphism_trivial_on_kernel : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π →
    (∃ N : ℕ, RingHom.ker π ^ N = ⊥) → ∀ (A : Over (Sp R)) [GrpObj A], IsProper A.hom →
    ∀ (n : ℕ) (D : Over (Sp R)) [GrpObj D], IsSeparated D.hom → ∀ (x : Fin n → (A ⟶ D)), (∀ j, IsMonHom (x j)) →
    (∀ (T₀ : Over (Sp R₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ A), (∀ j, y ≫ x j = 1) → y = 1) →
    ∀ (T : Over (Sp R)) (y : T ⟶ A), (∀ j, y ≫ x j = 1) → y = 1 := by
  atlas_forward_decl GlobalTheory.KernelThickening.kernel_trivial_of_nilpotent
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbDual in

theorem GlobalTheory.KerDeform.ker_deform : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
  ∀ (X₀ : Obj F 𝔠 (Sp R₀)) (A : Over (Sp R)) [GrpObj A] (i : X₀.A.left ⟶ A.left),
    IsGrpPullback X₀.A A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension (Module.finrank ℚ F) A.hom →
  ∀ (rm : OAct (𝓞 F) A), (∀ a, (X₀.rm.act a).left ≫ i = i ≫ (rm.act a).left) →
  ∀ (P : 𝔠.elt → LB (G2 A).left) (l : (G2 X₀.A).left ⟶ (G2 A).left), IsSquare i l → (∀ c, (P c).IsLB) →
    (∀ c, HasGen ((P c).pull (lift (1 : A ⟶ A) (𝟙 A)).left)) → (∀ c, HasGen ((P c).pull (lift (𝟙 A) (1 : A ⟶ A)).left)) →
    (∀ c, LBIso ((P c).pull l) (X₀.P c)) →
    (∀ c, LBIso (P c) ((P c).pull (lift (snd A A) (fst A A)).left)) →
    (∀ c c', LBIso (P c') (LB.div (P (c + c')) (P c))) →
    (∀ (a : 𝓞 F) c, LBIso (P (a • c)) ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left)) →
    (∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A ((P c).pull (lift (𝟙 A) (𝟙 A)).left)) →
  ∀ (c : 𝔠.elt) (T : Over (Sp R)) (x : T ⟶ A), HasGen ((P c).pull (lift (fst A T) (snd A T ≫ x)).left) →
    ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → x ≫ rm.act a = 1 := by
  intro HG HR HD F _ _ _ 𝔠 R R₀ _ _ I κ hκ π hπ hI X₀ A _ i hi hA hdim rm hrm P l hl hLB rig₁ rig₂ hred symm add smul pos c T x hx a ha
  obtain ⟨n, d, a', hd, hsum⟩ := GlobalTheory.T.fractional_ideal_partition_of_unity F 𝔠
  have k₀ : ∀ (T₀ : Over (Sp R₀)) (y₀ : T₀ ⟶ X₀.A),
      (∀ j, HasGen ((X₀.P (d j)).pull (lift (fst X₀.A T₀) (snd X₀.A T₀ ≫ y₀)).left)) → y₀ = 1 := by
    intro T₀ y₀ hy
    have h0 : X₀.rm.act 0 = 1 := by
      have e := X₀.rm.add 0 0
      rw [add_zero] at e
      exact left_eq_mul.1 e
    have hs : ∀ s : Finset (Fin n), y₀ ≫ X₀.rm.act (∑ j ∈ s, a' j) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.sum_empty, h0, MonObj.comp_one]
      | @insert j s hj ih =>
        rw [Finset.sum_insert hj, X₀.rm.add, MonObj.comp_mul, ih, X₀.ker (d j) T₀ y₀ (hy j) (a' j) (hd j), _root_.mul_one]
    have e := hs Finset.univ
    rwa [hsum, X₀.rm.one, Category.comp_id] at e
  obtain ⟨N, hN⟩ := GlobalTheory.AmpleNilThickening.exists_pow_eq_bot_of_isNilDP hκ
  obtain ⟨D, _, Q, hDab, -, q, q'⟩ := HD.1 _ A hA
  obtain ⟨cp, hcp⟩ := fracId_exists_totPos F 𝔠
  have hL : ((P cp).pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB (hLB cp) _
  choose lam hlam hiff using fun j ↦ GlobalTheory.PoincarePull.exists_hom_triv_iff R A hA D Q q q' _ hL (pos cp hcp) (P (d j)) (hLB _) (rig₁ _) (rig₂ _)
  have key : ∀ (T : Over (Sp R)) (y : T ⟶ A),
      (∀ j, HasGen ((P (d j)).pull (lift (fst A T) (snd A T ≫ y)).left)) → y = 1 := by
    intro T y hy
    haveI := hDab.proper
    haveI := hA.proper
    refine GlobalTheory.T.monomorphism_trivial_on_kernel R R₀ π hπ ⟨N, by rw [hI]; exact hN⟩ A inferInstance n D inferInstance lam hlam ?_ T y
      fun j ↦ (hiff j T y).1 (hy j)
    intro T₀ z hz
    let z₀ : Over.mk T₀.hom ⟶ X₀.A := liftPt hi T₀.hom z.left (Over.w z)
    have hz₀ : z₀.left ≫ i = z.left := liftPt_left hi _ _ _
    have hpush : pushP hi (s := T₀.hom) rfl z₀ = z := Over.OverMorphism.ext hz₀
    have k₁ : z₀ = 1 := k₀ _ z₀ fun j ↦ by
      have hP := hLB (d j)
      have hP' := X₀.isLB (d j)
      have e := evc_trR hi hi hl.1 hl.2 hP hP' (hred (d j)) (Over.mk T₀.hom) z₀
      have e0 : evc hP (fst A (Over.mk (T₀.hom ≫ spMap π))) (snd A _ ≫ z) = 0 :=
        (triv_ev_iff hP _ _).1 ((hiff j _ z).2 (hz j))
      rw [hpush] at e
      obtain ⟨s, hs⟩ : ∃ s, s ≫ (trR hi (Over.mk T₀.hom)).left = 𝟙 _ := ⟨_, trR_section hi _⟩
      have e2 := congrArg (CechPic.pull s) (e.trans e0)
      rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id, map_zero] at e2
      exact (triv_ev_iff hP' _ _).2 e2
    apply Over.OverMorphism.ext
    rw [← hz₀, k₁]
    exact one_left_comp hi (s := T₀.hom) rfl
  refine key T (x ≫ rm.act a) fun j ↦ ?_
  obtain ⟨b, hb⟩ := ha (d j)
  exact GlobalTheory.T.poincare_bundle_isomorphism_compat F 𝔠 _ A rm P hLB symm smul c (d j) a b hb T x hx
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_mult_lift_divided_powers : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
  ∀ (X₀ : Obj F 𝔠 (Sp R₀)) (A : Over (Sp R)) [GrpObj A] (i : X₀.A.left ⟶ A.left),
    IsGrpPullback X₀.A A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension (Module.finrank ℚ F) A.hom →
  ∀ (rm : OAct (𝓞 F) A), (∀ a, (X₀.rm.act a).left ≫ i = i ≫ (rm.act a).left) →
  ∀ (P : 𝔠.elt → LB (G2 A).left) (l : (G2 X₀.A).left ⟶ (G2 A).left), IsSquare i l → (∀ c, (P c).IsLB) →
    (∀ c, HasGen ((P c).pull (lift (1 : A ⟶ A) (𝟙 A)).left)) → (∀ c, HasGen ((P c).pull (lift (𝟙 A) (1 : A ⟶ A)).left)) →
    (∀ c, LBIso ((P c).pull l) (X₀.P c)) →
    (∀ c, LBIso (P c) ((P c).pull (lift (snd A A) (fst A A)).left)) →
    (∀ c c', LBIso (P c') (LB.div (P (c + c')) (P c))) →
    (∀ (a : 𝓞 F) c, LBIso (P (a • c)) ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left)) →
    (∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A ((P c).pull (lift (𝟙 A) (𝟙 A)).left)) →
  ∀ (c : 𝔠.elt) (T : Over (Sp R)) (x : T ⟶ A), HasGen ((P c).pull (lift (fst A T) (snd A T ≫ x)).left) →
    ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → x ≫ rm.act a = 1 := by
  first | exact @GlobalTheory.KerDeform.ker_deform | exact GlobalTheory.KerDeform.ker_deform | (intros; apply GlobalTheory.KerDeform.ker_deform <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RMDeform

theorem exists_lift_abelian (GD : GlobalTheory.Published.GrothendieckDeformation) (ADR : GlobalTheory.Published.AbelianDeRham)
    {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (κ : DividedPowers I) (hκ : IsNilDP κ) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hI : RingHom.ker π = I) {g : ℕ}
    {A₀ : Over (Sp R₀)} [GrpObj A₀] {A : Over (Sp R)} [GrpObj A] {i : A₀.left ⟶ A.left}
    (h : IsGrpPullback A₀ A (spMap π) i) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (E : Submodule R (Crys κ (spMap π) A₀)) (hE : ∃ N, IsCompl E N)
    (hF : ∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor κ hI A₀).Corr d y) :
    ∃ (A' : Over (Sp R)) (_ : GrpObj A') (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'),
      IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ liftFil κ h' = E := by
  obtain ⟨HC, HL, -⟩ := GD R I κ hκ R₀ π hπ hI
  have b := (HC g A₀ A i h hA hg).1
  have c := HC.crysToDR_bijective h hA hg
  obtain ⟨N, hN⟩ := hE
  have adm : GlobalTheory.Published.GrothendieckMessing.IsAdmissible h (E.map (crysToDR κ h)) := by
    refine ⟨⟨N.map (crysToDR κ h), (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ c)).isCompl hN⟩,
      fun y ↦ ?_⟩
    rw [hF]
    constructor
    · rintro ⟨d, hd, e⟩
      exact ⟨_, ⟨d, hd, rfl⟩, (GlobalTheory.Published.GrothendieckMessing.corr_crysToDR_iff hI h b.2 d y).2 e⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, e⟩
      exact ⟨d, hd, (GlobalTheory.Published.GrothendieckMessing.corr_crysToDR_iff hI h b.2 d y).1 e⟩
  obtain ⟨A', _, i', h', hA', hg', e⟩ := HL g A₀ A i h hA hg _ adm
  exact ⟨A', inferInstance, i', h', hA', hg', by rw [e, Submodule.comap_map_eq_of_injective c.1]⟩

theorem lbIso_pull_square {X₀ X Y₀ Y : Scheme.{0}} {P : LB X} {P₀ : LB X₀} (hP : P.IsLB) (hP₀ : P₀.IsLB)
    {l : X₀ ⟶ X} (e : LBIso (P.pull l) P₀) (a₀ : Y₀ ⟶ X₀) (a : Y ⟶ X) (y : Y₀ ⟶ Y) (w : a₀ ≫ l = y ≫ a) :
    LBIso (P₀.pull a₀) ((P.pull a).pull y) := by
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP₀ _) (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull hP₀, ← (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP l) hP₀).2 e, GlobalTheory.CechPic.cls_pull hP,
    GlobalTheory.CechPic.cls_pull (pull_isLB hP a), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp,
    ← GlobalTheory.CechPic.pull_comp, w]

theorem exists_deform : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → ∀ (hI : RingHom.ker π = I)
    (X₀ : Obj F 𝔠 (Sp R₀)) (A : Over (Sp R)) [GrpObj A] (i : X₀.A.left ⟶ A.left), IsGrpPullback X₀.A A (spMap π) i →
    IsAbelianScheme A → SmoothOfRelativeDimension (Module.finrank ℚ F) A.hom →
    ∀ (E : Submodule R (Crys κ (spMap π) X₀.A)), (∃ N : Submodule R (Crys κ (spMap π) X₀.A), IsCompl E N) →
      (∀ y : HdR X₀.A, y ∈ Fil X₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor κ hI X₀.A).Corr d y) →
      (∀ (a : 𝓞 F), ∀ d ∈ E, act κ (spMap π) X₀.rm a d ∈ E) →
      (∀ (c : 𝔠.elt) (φ : Crys κ (spMap π) X₀.A →ₗ[R] Crys κ (spMap π) X₀.A →ₗ[R] R),
        GlobalTheory.AbDual.IsCorrForm κ (spMap π) X₀.A X₀.A (X₀.P c) φ → ∀ a ∈ E, ∀ b ∈ E, φ a b = 0) →
      ∃ (X' : Obj F 𝔠 (Sp R)) (i' : X₀.A.left ⟶ X'.A.left) (pull : X₀.IsPullBy X' (spMap π) i'), liftFil κ pull.grp = E := by
  intro GD ADR ADC F _ _ _ 𝔠 R R₀ _ _ I κ hκ π hπ hI X₀ A _ i h hA hg E hE hFil hstab hiso
  obtain ⟨A', _, i', h', hA', hg', rfl⟩ := exists_lift_abelian GD ADR κ hκ π hπ hI h hA hg E hE hFil
  haveI : IsCommMonObj A' := hA'.comm
  obtain ⟨rm', hrm'⟩ := GlobalTheory.T.abelian_lift_crystalline_comparison GD R R₀ I κ hκ π hπ hI _ X₀.A A' i' h' hA' hg' (𝓞 F) X₀.rm hstab
  obtain ⟨l, l₁, l₂⟩ := GlobalTheory.AbDual.exists_prod_pullback h' h'
  have hsq : IsSquare i' l := ⟨l₁, l₂⟩
  obtain ⟨cp, hcp⟩ := fracId_exists_totPos F 𝔠
  have hdiag₀ : (X₀.diag cp).IsLB := pull_isLB (X₀.isLB cp) _
  have C := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ hI hA' hg' hA' hg' h' h'
  have hP : ∀ c : 𝔠.elt, ∃ P : LB (G2 A').left, P.IsLB ∧ HasGen (P.pull (lift (1 : A' ⟶ A') (𝟙 A')).left) ∧
      HasGen (P.pull (lift (𝟙 A') (1 : A' ⟶ A')).left) ∧ LBIso (P.pull l) (X₀.P c) := by
    intro c
    obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.AbDual.exists_isCorrForm C (X₀.isLB c) (X₀.rig₁ c) (X₀.rig₂ c)
    obtain ⟨P, hP, t₁, t₂, -, -, e⟩ := GlobalTheory.BirigidLift.exists_lift GD ADR ADC hκ hπ hI hA' hg' hA' hg' h' h' l₁ l₂
      hdiag₀ (X₀.pos cp hcp) hdiag₀ (X₀.pos cp hcp) (X₀.isLB c) (X₀.rig₁ c) (X₀.rig₂ c) hφ₀ (hiso c φ₀ hφ₀)
    exact ⟨P, hP, t₁, t₂, e⟩
  choose P' hP'LB hr₁ hr₂ hP'e using hP
  have wΔ : (lift (𝟙 X₀.A) (𝟙 X₀.A)).left ≫ l = i' ≫ (lift (𝟙 A') (𝟙 A')).left := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, l₁, Category.assoc, GlobalTheory.AbDual.lift_left_fst, ← Category.assoc, GlobalTheory.AbDual.lift_left_fst]
      simp
    · rw [Category.assoc, l₂, Category.assoc, GlobalTheory.AbDual.lift_left_snd, ← Category.assoc, GlobalTheory.AbDual.lift_left_snd]
      simp
  have pos' : ∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A' ((P' c).pull (lift (𝟙 A') (𝟙 A')).left) := by
    intro c hc
    haveI := hA'.smooth
    exact GlobalTheory.T.relAmple_lift_of_nilpotentDividedPowers_thickening R R₀ I κ hκ π hπ hI A' X₀.A i' h'.1 inferInstance _ (X₀.diag c) (pull_isLB (hP'LB c) _)
      (pull_isLB (X₀.isLB c) _) (lbIso_pull_square (hP'LB c) (X₀.isLB c) (hP'e c) _ _ i' wΔ) (X₀.pos c hc)
  have hL := pull_isLB (hP'LB cp) (lift (𝟙 A') (𝟙 A')).left
  have symm' : ∀ c, LBIso (P' c) ((P' c).pull (lift (snd A' A') (fst A' A')).left) := fun c ↦
    GlobalTheory.T.birigidified_lift_symmetric_of_symmetric_reduction GD ADC R R₀ I κ hκ π hπ hI _ X₀.A A' i' h' hA' hg' l hsq _ hL (pos' cp hcp) (X₀.P c) (X₀.isLB c)
      (X₀.symm c) (P' c) (hP'LB c) (hr₁ c) (hr₂ c) (hP'e c)
  have add' : ∀ c c', LBIso (P' c') (LB.div (P' (c + c')) (P' c)) := fun c c' ↦
    GlobalTheory.T.abelian_lift_de_rham_unique GD ADC R R₀ I κ hκ π hπ hI _ X₀.A A' i' h' hA' hg' l hsq _ hL (pos' cp hcp) (X₀.P c) (X₀.P c')
      (X₀.P (c + c')) (X₀.isLB c) (X₀.isLB c') (X₀.isLB (c + c')) (X₀.add c c') (P' c) (P' c') (P' (c + c'))
      (hP'LB c) (hP'LB c') (hP'LB (c + c')) (hr₁ c) (hr₂ c) (hr₁ c') (hr₂ c') (hr₁ (c + c')) (hr₂ (c + c'))
      (hP'e c) (hP'e c') (hP'e (c + c'))
  have smul' : ∀ (a : 𝓞 F) c, LBIso (P' (a • c)) ((P' c).pull (lift (fst A' A') (snd A' A' ≫ rm'.act a)).left) :=
    fun a c ↦ by
      haveI := X₀.rm.hom a
      haveI := rm'.hom a
      exact GlobalTheory.T.birigidified_lift_pullback_one_prod_endomorphism GD ADC R R₀ I κ hκ π hπ hI _ X₀.A A' i' h' hA' hg' l hsq _ hL (pos' cp hcp) (X₀.rm.act a)
        (rm'.act a) (hrm' a) (X₀.P c) (X₀.P (a • c)) (X₀.isLB c) (X₀.isLB (a • c)) (X₀.smul a c) (P' c) (P' (a • c))
        (hP'LB c) (hP'LB (a • c)) (hr₁ c) (hr₂ c) (hr₁ (a • c)) (hr₂ (a • c)) (hP'e c) (hP'e (a • c))
  have ker' := GlobalTheory.T.real_mult_lift_divided_powers GD ADR ADC F 𝔠 R R₀ I κ hκ π hπ hI X₀ A' i' h' hA' hg' rm' hrm' P' l hsq hP'LB hr₁ hr₂ hP'e
    symm' add' smul' pos'
  let X' : Obj F 𝔠 (Sp R) :=
    { A := A', ab := hA', dim := hg', rm := rm', P := P', isLB := hP'LB, rig₁ := hr₁, rig₂ := hr₂, symm := symm',
      add := add', smul := smul', pos := pos', ker := ker' }
  exact ⟨X', i', ⟨h', hrm', ⟨l, hsq, fun c ↦ (hP'e c).symm⟩⟩, rfl⟩

end GlobalTheory.RMDeform
end
end
