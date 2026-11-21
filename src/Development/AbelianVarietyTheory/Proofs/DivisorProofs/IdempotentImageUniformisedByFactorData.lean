import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationCompleteNormalBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismsAdjointPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianEndomorphismUniqueOverDegenerationDat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CFxi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataOfAdj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsumLeftPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismsActionUniformisedThick
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFormalEndomorphismAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductUniformisedGroupsSumData
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseChangeUniformization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUniformizationIdentityPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdentityPullbackDegeneration
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.CubicalPullBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeClsPullHom

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem gAdj_act_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ x : O, GAdj U.LG.L U.LG.L (oG.act x) (oG.act (Star.star x)) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin x
  have hL : ∀ a : O, LinHom U.toUnifPre U.toUnifPre (o.onB.act a)
      (DistribMulAction.toAddMonoidHom D.toPre.X (Star.star a)) (oG.act a) := fun a =>
    ⟨oG.hom a, fun e => hlin.q_lin e a, fun e => by
      obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
      exact ⟨t, ht, hi⟩⟩
  have hE := (GlobalTheory.Mum.endData_symm_and_ofOAct R D.toPre).2 O o x
  have h₁ := linHom_iff_linEnd.1 (hL x)
  have h₂ := linHom_iff_linEnd.1 (hL (Star.star x))
  rw [star_star] at h₂
  exact GlobalTheory.Mum.linEnd_adjoint_lbIso R hR D A G hG U _ _ _ _ hE _ _ h₁ h₂

end GlobalTheory.MumFam
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_groupAction_star_adjoint_bundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ x : O, GAdj U.LG.L U.LG.L (oG.act x) (oG.act (Star.star x)) := by
  atlas_forward_decl GlobalTheory.MumFam.gAdj_act_star
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.ActAdj

section Iso

variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem chart_le (j' : K' → L.ι) (j : K → L.ι) :
    LB.wchart L φ' j' ⊓ LB.wchart L φ j ≤ LB.wchart L (Sum.elim φ' φ) (Sum.elim j' j) := fun _ hy =>
  Set.mem_iInter.2 fun k => match k with
    | Sum.inl k => Set.mem_iInter.1 hy.1 k
    | Sum.inr k => Set.mem_iInter.1 hy.2 k

def genIso (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) :
    LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') :=
  ⟨fun p => res (chart_le p.1 p.2) (t.s (Sum.elim p.1 p.2))⟩

theorem gm_genIso (t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (p : (K' → L.ι) × (K → L.ι)) (hp : r z ∈ LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2) :
    gm r z _ ((genIso t).s p) = gm r z _ (t.s (Sum.elim p.1 p.2)) :=
  gm_res r z (chart_le p.1 p.2) hp _

theorem genIso_isGen {t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k)))} (ht : t.IsGen) :
    (genIso t).IsGen := by
  intro p q
  refine unit_ext fun y hy => ?_
  have hp := chart_le (φ := φ) (φ' := φ') p.1 p.2 hy.1
  have hq := chart_le (φ := φ) (φ' := φ') q.1 q.2 hy.2
  have e := gen_trans ht (𝟙 Y) y hp hq
  refine ((gm_res (𝟙 Y) y _ hy _).trans ((gm_genIso t (𝟙 Y) y p hy.1).trans e)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y p q hy)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_genIso t (𝟙 Y) y q hy.2)))).trans ?_
  congr 1
  refine (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hy.1.1 hy.2.1)
    (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hy.1.2 hy.2.2))).trans ?_
  simp only [trF, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

end Iso

end GlobalTheory.MumFam.ActAdj

namespace GlobalTheory.MumFam

open ActAdj in

theorem adj_act : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), Adj (pol D) (pol D) (o.onB.act a) (o.onB.act (Star.star a)) (DistribMulAction.toAddMonoidHom D.toPre.X a) (DistribMulAction.toAddMonoidHom D.toPre.X (Star.star a)) := by
  intro R _ _ I D O _ _ _ o a
  have hL := D.toPre.P.isLB
  let B := D.toPre.P.A
  let f := o.onB.act a
  let g := o.onB.act (star a)
  haveI hf : IsMonHom f := o.onB.hom a
  haveI hg : IsMonHom g := o.onB.hom (star a)
  let φ₀ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
    fun I => (psum B ![fst B B ≫ f, snd B B] I.down).left
  let φ₁ : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
    fun I => (psum B ![fst B B, snd B B ≫ g] I.down).left
  let e₂ : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)
  obtain ⟨u, hu, h0⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb hL f g (o.onB.rosati a)
  have hF : FormEq (rosatiφ B f g) (fun i => - rosatiε i) (Sum.elim φ₁ φ₀) (Sum.elim e₂ (fun k => - e₂ k)) := by
    intro U _ k
    have p := prod_ros f g (fst B B) (snd B B) k
    rw [lift_fst_snd] at p
    have p' : ∏ i, k (rosatiφ B f g i) ^ rosatiε i = _ :=
      (Finset.prod_congr rfl fun i _ => by erw [Over.id_left, Category.id_comp]).trans p
    have s1 : ∏ I, k (φ₁ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B) (snd B B ≫ g) k
    have s0 : ∏ I, k (φ₀ I) ^ e₂ I = _ := GlobalTheory.NormRos.prod_square (fst B B ≫ f) (snd B B) k
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [p', s1, s0]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨t, ht, htv⟩ := exists_gen hL hF (LB.invGen _ _ _ u) (DVR.invGen_isGen _ _ _ _ hu)
  let w : LB.Iso (cubeLB B ![fst B B ≫ f, snd B B] D.toPre.P.L) (cubeLB B ![fst B B, snd B B ≫ g] D.toPre.P.L) :=
    genIso t
  refine ⟨hf, hg, fun y => o.c_lin a y, fun y => o.c_lin (star a) y, w, genIso_isGen ht,
    fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  let P := (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left
  have hp : ∀ b b' J, Good D.toPre.P.L z J → val ((pol D).tau b b') (𝟙 _) z J = val (D.toPre.tau b b') (𝟙 _) z J :=
    fun b b' J hJ => (Wit.exists_tau D.toPre b b').choose_spec.2 _ _ z J hJ
  have hK₁ : Good D.toPre.P.L z J₁ := hJ₁
  have hK₂ : Good D.toPre.P.L z J₂ := hJ₂

  have bal := val_corr hK₁ (o.tau_bal a u hu h0 y y') (𝟙 _)
  rw [val_mul hK₁, val_pull hK₁, Category.id_comp] at bal
  have hut : val t P z J₁ = (val u P z J₁)⁻¹ := (htv _ P z J₁ hK₁).trans (val_inv _ _)
  let h := DistribMulAction.toAddMonoidHom D.toPre.X a
  let h' := DistribMulAction.toAddMonoidHom D.toPre.X (star a)
  have single : val ((pol D).tau (h y) y') (𝟙 _) z J₁ =
      val t P z J₁ * val ((pol D).tau y (h' y')) (𝟙 _) z J₁ := by
    exact (hp _ _ _ hK₁).trans ((eq_inv_mul_of_mul_eq ((mul_comm _ _).trans bal)).trans
      (congrArg₂ (· * ·) hut.symm (hp _ _ _ hK₁).symm))

  let j₁ : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₁ (P ≫ φ₁ I)
  let j₂ : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₂ (P ≫ φ₀ I)
  let j₁' : ULift.{0} (Finset (Fin 2)) → D.toPre.P.L.ι := fun I => J₁ (P ≫ φ₀ I)
  have m₁ : P z ∈ LB.wchart D.toPre.P.L φ₁ j₁ := hK₁.mem φ₁ P
  have m₂ : P z ∈ LB.wchart D.toPre.P.L φ₀ j₂ := hK₂.mem φ₀ P
  have m₁' : P z ∈ LB.wchart D.toPre.P.L φ₀ j₁' := hK₁.mem φ₀ P
  have eA : adjVal w P z J₁ J₂ = gm P z _ (t.s (Sum.elim j₁ j₂)) := gm_genIso t P z (j₁, j₂) ⟨m₁, m₂⟩
  have eT : val t P z J₁ = gm P z _ (t.s (Sum.elim j₁ j₁')) := val_of t P z J₁ _ (by rintro (k | k) <;> rfl)
  have tr := gen_trans ht P z (chart_le j₁ j₂ ⟨m₁, m₂⟩) (chart_le j₁ j₁' ⟨m₁, m₁'⟩)
  have trτ := gen_trans ((pol D).tau_gen (h y) y') (𝟙 _) z (hK₂.mem _ (𝟙 _)) (hK₁.mem _ (𝟙 _))
  let H : ((TK R).left ⟶ B.left) → ((TK R).left.presheaf.stalk z)ˣ :=
    fun ψ => gm ψ z (D.toPre.P.L.U (J₂ ψ) ⊓ D.toPre.P.L.U (J₁ ψ)) (D.toPre.P.L.g (J₂ ψ) (J₁ ψ))
  have kt : trF (Sum.elim φ₁ φ₀) (Sum.elim e₂ fun k => -e₂ k) P z (Sum.elim j₁ j₂) (Sum.elim j₁ j₁') =
      (∏ I, H (P ≫ φ₀ I) ^ e₂ I)⁻¹ := by
    unfold trF
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Finset.prod_eq_one (fun I _ => by erw [gm_self hL (P ≫ φ₁ I) z (hK₁ (P ≫ φ₁ I)), one_zpow]), _root_.one_mul]
    simp only [zpow_neg, Finset.prod_inv_distrib]
    rfl
  have cx : (toUnit (TK R) ≫ D.toPre.c y) ≫ f = toUnit (TK R) ≫ (pol D).c (h y) :=
    (Category.assoc _ _ _).trans (congrArg (toUnit (TK R) ≫ ·) (o.c_lin a y)).symm
  let X : TK R ⟶ B := toUnit (TK R) ≫ (pol D).c (h y)
  let Y : TK R ⟶ B := toUnit (TK R) ≫ (pol D).c y'
  have q1 : P ≫ ((fst B B ≫ f) * snd B B).left = (X * Y).left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd, cx]
    rfl
  have q2 : P ≫ (fst B B ≫ f).left = X.left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, lift_fst_assoc, cx]
    rfl
  have q3 : P ≫ (snd B B).left = Y.left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, lift_snd]
    rfl
  have q4 : P ≫ (1 : B ⊗ B ⟶ B).left = (1 : TK R ⟶ B).left := by
    show (lift (toUnit (TK R) ≫ D.toPre.c y) (toUnit (TK R) ≫ D.toPre.c y')).left ≫ _ = _
    rw [← Over.comp_left, MonObj.comp_one]
  have s0 : ∏ I, H (P ≫ φ₀ I) ^ e₂ I = H (P ≫ ((fst B B ≫ f) * snd B B).left) * (H (P ≫ (fst B B ≫ f).left))⁻¹ *
      (H (P ≫ (snd B B).left))⁻¹ * H (P ≫ (1 : B ⊗ B ⟶ B).left) :=
    GlobalTheory.NormRos.prod_square (fst B B ≫ f) (snd B B) (fun ψ => H (P ≫ ψ))
  have l4 : ∀ X Y : TK R ⟶ B, ∏ k, H (𝟙 _ ≫ lamPts X Y k) ^ negε k =
      (H (X * Y).left)⁻¹ * H X.left * H Y.left * (H (1 : TK R ⟶ B).left)⁻¹ := fun X Y => by
    have e := Wit.prod_neg_lamPts X Y (fun ψ => (H ψ)⁻¹)
    simpa only [inv_inv] using e
  have kτ : ∏ k, H (𝟙 _ ≫ lamPts X Y k) ^ negε k = (∏ I, H (P ≫ φ₀ I) ^ e₂ I)⁻¹ := by
    rw [l4 X Y, s0, q1, q2, q3, q4]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine (trτ.trans (congrArg (_ * ·) single)).trans (Eq.trans ?_
    (congrArg (· * _) (eA.trans (tr.trans (congrArg (_ * ·) eT.symm)))).symm)
  rw [_root_.mul_assoc]
  congr 1
  exact kτ.trans kt.symm

end GlobalTheory.MumFam
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringInvolutionAction_gives_polarisedAdjointPair : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), Adj (pol D) (pol D) (o.onB.act a) (o.onB.act (Star.star a)) (DistribMulAction.toAddMonoidHom D.toPre.X a) (DistribMulAction.toAddMonoidHom D.toPre.X (Star.star a)) := by
  atlas_forward_decl GlobalTheory.MumFam.adj_act
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam.FactorAdj

open AdjComp

def chartPullTwo {X Y Y' Y'' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ' : K → (Y'' ⟶ X)) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (h : Y'' ⟶ Y') (n : Y' ⟶ Y) (hc : ∀ k, φ' k = (h ≫ n) ≫ φ k) :
    ChartPull (LB.LinComb L φ' ε) ((LB.LinComb L φ ε).pull n) h :=
  have le : ∀ j : K → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ ((LB.LinComb L φ ε).pull n).U (fun _ => j) := fun j _ hy =>
    (mem_pull (L := LB.LinComb L φ ε)).2 ((chartPullSame L φ' φ ε (h ≫ n) hc).le j hy)
  { idx := fun j _ => j
    le := le
    g := fun y j j' hj hj' => ((chartPullSame L φ' φ ε (h ≫ n) hc).g y j j' hj hj').trans
      (gm_pull_g (LB.LinComb L φ ε) n h y (fun _ => j) (fun _ => j') (le j hj) (le j' hj')).symm }

theorem exists_pull_lam {S : Scheme.{0}} {T G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {L : LB G.left} {L' : LB G'.left} {n : G2 G ⟶ G2 G'} (w : LB.Iso (abelian₂ G L) ((abelian₂ G' L').pull n.left))
    (hw : w.IsGen) (m : T ⟶ G2 G) (x : Fin 2 → (T ⟶ G)) (x' : Fin 2 → (T ⟶ G')) (hx : ∀ i, x i = m ≫ x2 G i)
    (hx' : ∀ i, x' i = (m ≫ n) ≫ x2 G' i) :
    ∃ w' : LB.Iso (cubeLB G x L) (cubeLB G' x' L'), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ T.left) (z : Z) J' J,
      Good L' z J' → Good L z J → adjVal w' p z J' J = lamVal w (p ≫ m.left) z J' J := by
  let a : ChartPull (cubeLB G x L) (abelian₂ G L) m.left := cubePull L m _ _ hx
  let b : ChartPull (cubeLB G' x' L') ((abelian₂ G' L').pull n.left) m.left :=
    chartPullTwo L' _ _ _ m.left n.left (psum_left_pull (m ≫ n) _ _ hx')
  refine ⟨pullIso a b w, pullIso_isGen a b hw, fun Z p z J' J hJ' hJ => ?_⟩
  have mA := Good.mem hJ (fun I : ULift (Finset (Fin 2)) => (psum G x I.down).left) p
  have mB := Good.mem hJ' (fun I : ULift (Finset (Fin 2)) => (psum G' x' I.down).left) p
  refine ((adjVal_of (pullIso a b w) p z J' J _ _ (fun _ => rfl) (fun _ => rfl)).trans
    (gm_pullIso a b w p z (_, _) ⟨mB, mA⟩)).trans ?_
  have e₁ : (fun I : ULift (Finset (Fin 2)) => J (p ≫ (psum G x I.down).left)) =
      fun I => J ((p ≫ m.left) ≫ (psum G (x2 G) I.down).left) := funext fun I => by
    rw [psum_left_pull m _ _ hx I, Category.assoc]
  have e₂ : (fun I : ULift (Finset (Fin 2)) => J' (p ≫ (psum G' x' I.down).left)) =
      fun I => J' ((p ≫ m.left) ≫ n.left ≫ (psum G' (x2 G') I.down).left) := funext fun I => by
    rw [psum_left_pull (m ≫ n) _ _ hx' I, Over.comp_left, Category.assoc, Category.assoc]
  rw [e₁, e₂]
  rfl

theorem exists_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), ∃ w : LB.Iso (cubeLB (pol D).B ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B] (pol D).M.L) (cubeLB (pol D').B ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f] (pol D').M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good (pol D').M.L z J₁ → Good (pol D).M.L z J₂ → val ((pol D).tau (F.xp y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left z J₁ J₂ * val ((pol D').tau ((DistribMulAction.toAddMonoidHom D'.toPre.X F.e) y) (((DistribMulAction.toAddMonoidHom D'.toPre.X F.f).comp F.xi) y')) (𝟙 _) z J₁ := by
  intro R _ _ I D D' F
  let m : (pol D').B ⊗ (pol D).B ⟶ G2 (pol D).B := lift (fst _ _ ≫ F.pr) (snd _ _)
  let n : G2 (pol D).B ⟶ G2 (pol D').B := lift (fst _ _ ≫ F.inc) (snd _ _ ≫ F.inc ≫ F.o.onB.act F.f)
  let w₀ : LB.Iso (abelian₂ (pol D).B (pol D).M.L) ((abelian₂ (pol D').B (pol D').M.L).pull n.left) := F.w
  obtain ⟨w, gw, hw⟩ := exists_pull_lam w₀ F.w_gen m ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B]
    ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f]
    (fun i => by
      fin_cases i
      · exact (lift_fst _ _).symm
      · exact (lift_snd _ _).symm)
    (fun i => by
      fin_cases i
      · refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (lift_fst _ _)).trans ?_))
        refine (lift_fst_assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)
        exact congrArg (fst (pol D').B (pol D).B ≫ ·) F.pr_inc
      · refine Eq.symm ((Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (lift_snd _ _)).trans ?_))
        exact lift_snd_assoc _ _ _)
  refine ⟨w, gw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have hP : (lift (toUnit (TK R) ≫ D.toPre.c (F.xp y)) (toUnit (TK R) ≫ D.toPre.c y')).left =
      (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left ≫ m.left := by
    refine congrArg (fun q : TK R ⟶ G2 (pol D).B => q.left) (Eq.symm ((comp_lift _ _ _).trans ?_))
    refine congrArg₂ lift ((lift_fst_assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)) (lift_snd _ _)
    exact congrArg (toUnit (TK R) ≫ ·) (c_xp F y).symm
  have e := F.tau (F.xp y) y' z J₁ J₂ hJ₁ hJ₂
  rw [F.xi_xp, hP] at e
  refine ((GlobalTheory.PolDeg.Wit.exists_tau D.toPre _ _).choose_spec.2 _ _ z J₂ hJ₂).trans (e.trans ?_)
  exact congrArg₂ (· * ·) (hw _ _ z J₁ J₂ hJ₁ hJ₂).symm
    ((GlobalTheory.PolDeg.Wit.exists_tau D'.toPre (F.e • y) (F.f • F.xi y')).choose_spec.2 _ _ z J₁ hJ₁).symm

end GlobalTheory.MumFam.FactorAdj
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationFactor_pairing_iso_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), ∃ w : LB.Iso (cubeLB (pol D).B ![fst (pol D').B (pol D).B ≫ F.pr, snd (pol D').B (pol D).B] (pol D).M.L) (cubeLB (pol D').B ![fst (pol D').B (pol D).B ≫ F.o.onB.act F.e, snd (pol D').B (pol D).B ≫ F.inc ≫ F.o.onB.act F.f] (pol D').M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good (pol D').M.L z J₁ → Good (pol D).M.L z J₂ → val ((pol D).tau (F.xp y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ (pol D').c y) (toUnit (TK R) ≫ (pol D).c y')).left z J₁ J₂ * val ((pol D').tau ((DistribMulAction.toAddMonoidHom D'.toPre.X F.e) y) (((DistribMulAction.toAddMonoidHom D'.toPre.X F.f).comp F.xi) y')) (𝟙 _) z J₁ := by
  atlas_forward_decl GlobalTheory.MumFam.FactorAdj.exists_pull
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam

open AdjComp in

theorem Adj.of_twisted_comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a₁ a₁' : Q₁.B ⟶ Q₁.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h₁ h₁' : Q₁.X →+ Q₁.X) (h' : Q₂.X →+ Q₁.X), IsMonHom a → IsMonHom a' → (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) → (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') → Adj Q₁ Q₁ a₁ a₁' h₁ h₁' → (∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ → val (Q₂.tau (h y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau (h₁ y) (h' y')) (𝟙 _) z J₁) → Adj Q₁ Q₂ a (a' ≫ a₁') h (h₁'.comp h') := by
  intro R _ _ Q₁ Q₂ a a₁ a₁' a' h h₁ h₁' h' ma ma' ca ca' H₁ H₂
  obtain ⟨mb, mb', cb, cb', w₁, g₁, V₁⟩ := H₁
  obtain ⟨w₂, g₂, V₂⟩ := H₂
  let m₂ : Q₁.B ⊗ Q₂.B ⟶ Q₁.B ⊗ Q₁.B := lift (fst _ _) (snd _ _ ≫ a')
  have xB : ∀ i, (![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₁.B ≫ a₁, snd Q₁.B Q₁.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  have xC : ∀ i, (![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₁.B, snd Q₁.B Q₁.B ≫ a₁'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  let cB := cubePull Q₁.M.L m₂ _ _ xB
  let cC := cubePull Q₁.M.L m₂ _ _ xC
  have lA : (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L).IsLB := DVR.linComb_isLB _ Q₂.M.isLB _ _
  have lB : (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  have lC : (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  obtain ⟨w, gw, hw⟩ := exists_comp lA lB lC w₂ g₂ (pullIso cB cC w₁) (pullIso_isGen cB cC g₁)
  refine ⟨ma, inferInstance, ca, fun y => ?_, w, gw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  · rw [AddMonoidHom.comp_apply, cb', ca', Category.assoc]
  · have e₂ := V₂ y y' z J₁ J₂ hJ₁ hJ₂
    have e₁ := V₁ y (h' y') z J₁ J₁ hJ₁ hJ₁
    have hP : (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₁.c (h' y'))).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left ≫ m₂.left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, ca', Category.assoc]
    rw [hP] at e₁
    generalize (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left = P at e₂ e₁ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] I.down).left) P
    have mB := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] I.down).left) P
    have mA := Good.mem hJ₂ (fun I : ULift (Finset (Fin 2)) => (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] I.down).left) P
    have K : adjVal w P z J₁ J₂ = adjVal w₂ P z J₁ J₂ * adjVal w₁ (P ≫ m₂.left) z J₁ J₁ := by
      refine ((adjVal_of w P z J₁ J₂ _ _ (fun _ => rfl) (fun _ => rfl)).trans ((hw _ P z _ _ _ mC mB mA).trans
        (congrArg₂ (· * ·) (gm_pullIso cB cC w₁ P z (_, _) ⟨mC, mB⟩) rfl))).trans ?_
      rw [mul_comm]
      refine congrArg₂ (· * ·) (adjVal_of w₂ P z J₁ J₂ _ _ (fun _ => rfl) (fun _ => rfl)).symm
        (adjVal_of w₁ (P ≫ m₂.left) z J₁ J₁ _ _ (fun I => ?_) (fun I => ?_)).symm
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xC I]
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xB I]
    rw [AddMonoidHom.comp_apply, e₂, e₁, K]
    exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory.MumFam
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.of_twisted_adjoint_comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a₁ a₁' : Q₁.B ⟶ Q₁.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h₁ h₁' : Q₁.X →+ Q₁.X) (h' : Q₂.X →+ Q₁.X), IsMonHom a → IsMonHom a' → (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) → (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') → Adj Q₁ Q₁ a₁ a₁' h₁ h₁' → (∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ → val (Q₂.tau (h y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau (h₁ y) (h' y')) (𝟙 _) z J₁) → Adj Q₁ Q₂ a (a' ≫ a₁') h (h₁'.comp h') := by
  atlas_forward_decl GlobalTheory.MumFam.Adj.of_twisted_comp
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.FactorAdj

theorem factor_adj : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), Adj (pol D') (pol D) F.pr (F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) F.xp ((DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi) := by
  intro R _ _ I D D' F
  haveI := F.inc_hom
  haveI := F.o.onB.hom F.f
  have hm : IsMonHom (F.inc ≫ F.o.onB.act F.f) := inferInstance
  have H := GlobalTheory.T.of_twisted_adjoint_comp R (pol D') (pol D) F.pr (F.o.onB.act F.e) (F.o.onB.act (Star.star F.e))
    (F.inc ≫ F.o.onB.act F.f) F.xp
    (DistribMulAction.toAddMonoidHom D'.toPre.X F.e) (DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star F.e))
    ((DistribMulAction.toAddMonoidHom D'.toPre.X F.f).comp F.xi) F.pr_hom hm
    (fun y => c_xp F y) (fun z => c_fxi F z) (GlobalTheory.T.ringInvolutionAction_gives_polarisedAdjointPair R I D' F.O F.o F.e) (GlobalTheory.T.exists_degenerationFactor_pairing_iso_pullback R I D D' F)
  have e1 : (F.inc ≫ F.o.onB.act F.f) ≫ F.o.onB.act (Star.star F.e) = F.inc ≫ F.o.onB.act (Star.star F.e * F.f) := by
    rw [F.o.onB.map_mul, Category.assoc]
  have e2 : (DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star F.e)).comp
      ((DistribMulAction.toAddMonoidHom D'.toPre.X F.f).comp F.xi) =
      (DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi := by
    ext y
    simp [mul_smul]
  exact e1 ▸ e2 ▸ H

end GlobalTheory.MumFam.FactorAdj
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentFactor_projection_adjointPair : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), Adj (pol D') (pol D) F.pr (F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) F.xp ((DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi) := by
  atlas_forward_decl GlobalTheory.MumFam.FactorAdj.factor_adj
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.AdjSwap

section Charts

variable {X Y Y' : Scheme.{0}}

def pullInv {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h) (w : LB.Iso B A) :
    LB.Iso A' B' where
  s p := (res (fun y hy => ⟨a.le _ hy.2, b.le _ hy.1⟩ :
      B'.U p.1 ⊓ A'.U p.2 ≤ h ⁻¹ᵁ (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)))
    (pullU h _ (w.s (a.idx p.2, b.idx p.1))))⁻¹

theorem gm_pullInv {Z : Scheme.{0}} {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (b : ChartPull B' B h) (w : LB.Iso B A) (r : Z ⟶ Y') (z : Z) (p : B'.ι × A'.ι) (hz : r z ∈ B'.U p.1 ⊓ A'.U p.2) :
    gm r z (B'.U p.1 ⊓ A'.U p.2) ((pullInv a b w).s p) =
      (gm (r ≫ h) z (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)))⁻¹ :=
  (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z _ hz _).trans
    (gm_pull r h z _ (show h (r z) ∈ A.U (a.idx p.2) ⊓ B.U (b.idx p.1) from ⟨a.le _ hz.2, b.le _ hz.1⟩) _)))

theorem pullInv_isGen {A B : LB Y} {A' B' : LB Y'} {h : Y' ⟶ Y} (a : ChartPull A' A h) (b : ChartPull B' B h)
    {w : LB.Iso B A} (hw : w.IsGen) : (pullInv a b w).IsGen := fun p q => unit_ext fun y hy => by
  have val : ∀ p : B'.ι × A'.ι, y ∈ B'.U p.1 ⊓ A'.U p.2 →
      gm (𝟙 Y') y _ ((pullInv a b w).s p) =
        (gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)))⁻¹ := fun p hp =>
    (gm_pullInv a b w (𝟙 Y') y p hp).trans (by rw [Category.id_comp])
  have hm : h y ∈ A.U (a.idx p.2) ⊓ B.U (b.idx p.1) ⊓ (A.U (a.idx q.2) ⊓ B.U (b.idx q.1)) :=
    ⟨⟨a.le _ hy.1.2, b.le _ hy.1.1⟩, ⟨a.le _ hy.2.2, b.le _ hy.2.1⟩⟩
  have e := congrArg (gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1) ⊓ (A.U (a.idx q.2) ⊓ B.U (b.idx q.1))))
    (hw (a.idx p.2, b.idx p.1) (a.idx q.2, b.idx q.1))
  have e' : gm h y (A.U (a.idx p.2) ⊓ B.U (b.idx p.1)) (w.s (a.idx p.2, b.idx p.1)) =
      gm h y (A.U (a.idx p.2) ⊓ A.U (a.idx q.2)) (A.g (a.idx p.2) (a.idx q.2)) *
        (gm h y (B.U (b.idx p.1) ⊓ B.U (b.idx q.1)) (B.g (b.idx p.1) (b.idx q.1)))⁻¹ *
        gm h y (A.U (a.idx q.2) ⊓ B.U (b.idx q.1)) (w.s (a.idx q.2, b.idx q.1)) :=
    (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div B A h y (a.idx p.2, b.idx p.1) (a.idx q.2, b.idx q.1) hm) (gm_res h y _ hm _))))
  have d : gm (𝟙 Y') y ((LB.div B' A').U p ⊓ (LB.div B' A').U q) ((LB.div B' A').g p q) =
      gm (𝟙 Y') y (B'.U p.1 ⊓ B'.U q.1) (B'.g p.1 q.1) * (gm (𝟙 Y') y (A'.U p.2 ⊓ A'.U q.2) (A'.g p.2 q.2))⁻¹ :=
    gm_div A' B' (𝟙 Y') y p q hy
  refine (gm_res _ y _ hy _).trans ((val p hy.1).trans (Eq.symm ((map_mul _ _ _).trans ?_)))
  rw [d, gm_res (𝟙 Y') y _ hy, val q hy.2, b.g y _ _ hy.1.1 hy.2.1, a.g y _ _ hy.1.2 hy.2.2, e']
  simp only [mul_inv, inv_inv]
  ac_rfl

theorem gm_gen_congr {M : LB X} (t : LB.Gen M) {r r' : Y ⟶ X} (hr : r = r') (y : Y) {i i' : M.ι} (hi : i = i') :
    gm r y (M.U i) (t.s i) = gm r' y (M.U i') (t.s i') := by
  subst hr hi; rfl

theorem gm_g_congr (L : LB X) (f : Y ⟶ X) (y : Y) {i i' j j' : L.ι} (hi : i = i') (hj : j = j') :
    gm f y (L.U i ⊓ L.U j) (L.g i j) = gm f y (L.U i' ⊓ L.U j') (L.g i' j') := by
  subst hi hj; rfl

def chartPullPerm (L : LB X) {K : Type} [Fintype K] (φ' : K → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (e : K ≃ K) (hc : ∀ k, φ' k = h ≫ φ (e k)) (hε : ∀ k, ε (e k) = ε k) :
    ChartPull (LB.LinComb L φ' ε) (LB.LinComb L φ ε) h where
  idx j k := j (e.symm k)
  le j y hy := Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy (e.symm k)
    rw [hc, Equiv.apply_symm_apply] at this
    exact this
  g y j j' hj hj' := by
    refine (gm_linComb L φ' ε (𝟙 Y') y j j' hj hj').trans (Eq.trans ?_ (gm_linComb L φ ε h y _ _
      (Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hj (e.symm k)
        rw [hc, Equiv.apply_symm_apply] at this
        exact this)
      (Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hj' (e.symm k)
        rw [hc, Equiv.apply_symm_apply] at this
        exact this)).symm)
    refine Fintype.prod_equiv e _ _ fun k => ?_
    simp only [hε, Category.id_comp, hc]
    exact congrArg (· ^ ε k) (gm_g_congr L _ y (congrArg j (e.symm_apply_apply k)).symm
      (congrArg j' (e.symm_apply_apply k)).symm)

end Charts

section Sums

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem psum_eq_prod {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G x I = ∏ i ∈ I, x i := by
  have hnd : ((List.finRange n).filter (· ∈ I)).Nodup := (List.nodup_finRange n).filter _
  calc psum G x I = (((List.finRange n).filter (· ∈ I)).map x).prod := by
        unfold psum
        generalize ((List.finRange n).filter (· ∈ I)) = l
        induction l with
        | nil => rfl
        | cons k l ih => rw [List.foldr_cons, ih, List.map_cons, List.prod_cons]; rfl
    _ = ∏ i ∈ I, x i := by
        rw [← List.prod_toFinset x hnd]
        congr 1
        ext i
        simp

theorem psum_perm {T T' : Over S} (σ : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G))
    (π : Equiv.Perm (Fin n)) (hx : ∀ i, x' i = σ ≫ x (π i)) (I : Finset (Fin n)) :
    psum G x' I = σ ≫ psum G x (I.map π.toEmbedding) := by
  calc psum G x' I = ∏ i ∈ I, x' i := psum_eq_prod x' I
    _ = ∏ i ∈ I, σ ≫ x (π i) := by simp only [hx]
    _ = σ ≫ ∏ i ∈ I, x (π i) := (map_prod (preHom (G := G) σ) _ I).symm
    _ = σ ≫ ∏ i ∈ I.map π.toEmbedding, x i := by rw [Finset.prod_map]; rfl
    _ = σ ≫ psum G x (I.map π.toEmbedding) := by rw [psum_eq_prod]

end Sums

def swapIdx : ULift.{0} (Finset (Fin 2)) ≃ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.swap (0 : Fin 2) 1).finsetCongr.trans Equiv.ulift.symm)

theorem swapIdx_down (I : ULift.{0} (Finset (Fin 2))) :
    (swapIdx I).down = I.down.map (Equiv.swap (0 : Fin 2) 1).toEmbedding := rfl

end GlobalTheory.MumFam.AdjSwap

namespace GlobalTheory.MumFam

open AdjSwap in

theorem adj_symm : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a' : Q₂.B ⟶ Q₁.B)
    (h : Q₁.X →+ Q₂.X) (h' : Q₂.X →+ Q₁.X), Adj Q₁ Q₂ a a' h h' → Adj Q₂ Q₁ a' a h' h := by
  intro R _ _ Q₁ Q₂ a a' h h' ⟨ha, ha', hc, hc', w, hw, hv⟩
  let σ : Q₂.B ⊗ Q₁.B ⟶ Q₁.B ⊗ Q₂.B := lift (snd Q₂.B Q₁.B) (fst Q₂.B Q₁.B)
  have hA : ∀ K : ULift.{0} (Finset (Fin 2)), (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] K.down).left =
      σ.left ≫ (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] (swapIdx K).down).left := fun K => by
    rw [swapIdx_down, psum_perm σ ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] _ (Equiv.swap 0 1)
      (fun i => by fin_cases i <;> simp [σ]) K.down, Over.comp_left]
  have hB : ∀ K : ULift.{0} (Finset (Fin 2)), (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] K.down).left =
      σ.left ≫ (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] (swapIdx K).down).left := fun K => by
    rw [swapIdx_down, psum_perm σ ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] _ (Equiv.swap 0 1)
      (fun i => by fin_cases i <;> simp [σ]) K.down, Over.comp_left]
  have hε : ∀ K : ULift.{0} (Finset (Fin 2)), ((-1 : ℤ) ^ (2 - (swapIdx K).down.card)) = (-1) ^ (2 - K.down.card) :=
    fun K => by rw [swapIdx_down, Finset.card_map]
  let cA : ChartPull (cubeLB Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] Q₁.M.L)
      (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L) σ.left :=
    chartPullPerm Q₁.M.L _ _ _ σ.left swapIdx hA hε
  let cB : ChartPull (cubeLB Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] Q₂.M.L)
      (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) σ.left :=
    chartPullPerm Q₂.M.L _ _ _ σ.left swapIdx hB hε
  refine ⟨ha', ha, hc', hc, pullInv cA cB w, pullInv_isGen cA cB hw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have hp : (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left ≫ σ.left =
      (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left := by
    rw [← Over.comp_left]; congr 1; simp [σ]
  have key : adjVal (pullInv cA cB w) (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left z J₁ J₂ =
      (adjVal w (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left z J₂ J₁)⁻¹ := by
    let p' := (lift (toUnit (TK R) ≫ Q₂.c y) (toUnit (TK R) ≫ Q₁.c y')).left
    have m₁ := hJ₁.mem (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left) p'
    have m₂ := hJ₂.mem (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left) p'
    have e1 := gm_pullInv cA cB w p' z
      (fun I => J₁ (p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left),
        fun I => J₂ (p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left)) ⟨m₁, m₂⟩
    have i₁ : ∀ k : ULift.{0} (Finset (Fin 2)),
        p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] (swapIdx.symm k).down).left =
          (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] k.down).left := fun k => by
      rw [hA, Equiv.apply_symm_apply, ← Category.assoc, hp]
    have i₂ : ∀ k : ULift.{0} (Finset (Fin 2)),
        p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] (swapIdx.symm k).down).left =
          (lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] k.down).left := fun k => by
      rw [hB, Equiv.apply_symm_apply, ← Category.assoc, hp]
    have e2 := gm_gen_congr w hp z (Prod.ext (funext fun k => congrArg J₂ (i₁ k)) (funext fun k => congrArg J₁ (i₂ k)) :
      ((cA.idx (fun I => J₂ (p' ≫ (psum Q₁.B ![fst Q₂.B Q₁.B ≫ a', snd Q₂.B Q₁.B] I.down).left)),
        cB.idx (fun I => J₁ (p' ≫ (psum Q₂.B ![fst Q₂.B Q₁.B, snd Q₂.B Q₁.B ≫ a] I.down).left))) :
          (LB.div (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L)
            (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L)).ι) =
        (fun I => J₂ ((lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a'] I.down).left),
          fun I => J₁ ((lift (toUnit (TK R) ≫ Q₁.c y') (toUnit (TK R) ≫ Q₂.c y)).left ≫
            (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] I.down).left)))
    exact e1.trans (congrArg (·⁻¹) e2)
  have o := hv y' y z J₂ J₁ hJ₂ hJ₁
  rw [Q₂.tau_symm (h y') y z J₁ hJ₁, Q₁.tau_symm y' (h' y) z J₂ hJ₂] at o
  rw [key, o, inv_mul_cancel_left]

end GlobalTheory.MumFam
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam

def chartPullPerm {X Y Y' : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ' : K' → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε' : K' → ℤ) (ε : K → ℤ) (h : Y' ⟶ Y) (e : K' ≃ K)
    (hc : ∀ k, φ' (e.symm k) = h ≫ φ k) (hε : ∀ k, ε' (e.symm k) = ε k) :
    ChartPull (LB.LinComb L φ' ε') (LB.LinComb L φ ε) h :=
  have le : ∀ j : K' → L.ι, LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => j (e.symm k)) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy (e.symm k)
      rw [hc] at this
      exact this
  { idx := fun j k => j (e.symm k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε' (𝟙 Y') y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L φ ε h y _ _ (le j hj) (le j' hj')).symm)
      refine (Fintype.prod_equiv e.symm _ _ fun k => ?_).symm
      rw [Category.id_comp, hc, hε] }

theorem psum_perm {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (σ : Fin n ≃ Fin n) (hx : ∀ i, x' i = h ≫ x (σ i))
    (I : Finset (Fin n)) : psum G x' I = h ≫ psum G x (I.map σ.toEmbedding) := by
  rw [CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.comp_prod, Finset.prod_map]
  exact Finset.prod_congr rfl fun i _ => hx i

def chartPullCube {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (σ : Fin n ≃ Fin n) (hx : ∀ i, x' i = h ≫ x (σ i))
    (L : LB G.left) : ChartPull (cubeLB G x' L) (cubeLB G x L) h.left :=
  chartPullPerm L _ _ _ _ h.left (Equiv.ulift.trans ((Equiv.finsetCongr σ).trans Equiv.ulift.symm))
    (fun k => by
      show (psum G x' ((Equiv.finsetCongr σ).symm k.down)).left = h.left ≫ (psum G x k.down).left
      rw [psum_perm G h x x' σ hx, Over.comp_left]
      congr 3
      exact (Equiv.finsetCongr σ).apply_symm_apply k.down)
    (fun k => by
      show (-1 : ℤ) ^ (n - ((Equiv.finsetCongr σ).symm k.down).card) = (-1) ^ (n - k.down.card)
      simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply])

end GlobalTheory.MumFam

namespace GlobalTheory.MumFam

theorem gAdj_swap {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} {u : G₁ ⟶ G₂} {u' : G₂ ⟶ G₁} (H : GAdj L₁ L₂ u u') : GAdj L₂ L₁ u' u :=
  LBIso.chartPull
    (chartPullCube G₁ (lift (snd G₂ G₁) (fst G₂ G₁)) ![fst G₁ G₂, snd G₁ G₂ ≫ u'] ![fst G₂ G₁ ≫ u', snd G₂ G₁]
      (Equiv.swap 0 1) (fun i => by fin_cases i <;> simp) L₁)
    (chartPullCube G₂ (lift (snd G₂ G₁) (fst G₂ G₁)) ![fst G₁ G₂ ≫ u, snd G₁ G₂] ![fst G₂ G₁, snd G₂ G₁ ≫ u]
      (Equiv.swap 0 1) (fun i => by fin_cases i <;> simp) L₂)
    (LBIso.symm H)

theorem gAdj_comp {S : Scheme.{0}} {G₁ G₂ G₃ : Over S} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    [GrpObj G₃] [IsCommMonObj G₃] {L₁ : LB G₁.left} {L₂ : LB G₂.left} {L₃ : LB G₃.left} (hL₁ : L₁.IsLB)
    (hL₂ : L₂.IsLB) (hL₃ : L₃.IsLB) {u : G₁ ⟶ G₂} {u' : G₂ ⟶ G₁} {v : G₂ ⟶ G₃} {v' : G₃ ⟶ G₂}
    (H : GAdj L₁ L₂ u u') (H' : GAdj L₂ L₃ v v') : GAdj L₁ L₃ (u ≫ v) (v' ≫ u') :=
  LBIso.trans (LB.isLB_linComb hL₃ _ _) (LB.isLB_linComb hL₂ _ _) (LB.isLB_linComb hL₁ _ _)
    (LBIso.chartPull
      (chartPullCube G₃ (lift (fst G₁ G₃ ≫ u) (snd G₁ G₃)) ![fst G₂ G₃ ≫ v, snd G₂ G₃]
        ![fst G₁ G₃ ≫ u ≫ v, snd G₁ G₃] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₃)
      (chartPullCube G₂ (lift (fst G₁ G₃ ≫ u) (snd G₁ G₃)) ![fst G₂ G₃, snd G₂ G₃ ≫ v']
        ![fst G₁ G₃ ≫ u, snd G₁ G₃ ≫ v'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₂) H')
    (LBIso.chartPull
      (chartPullCube G₂ (lift (fst G₁ G₃) (snd G₁ G₃ ≫ v')) ![fst G₁ G₂ ≫ u, snd G₁ G₂]
        ![fst G₁ G₃ ≫ u, snd G₁ G₃ ≫ v'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₂)
      (chartPullCube G₁ (lift (fst G₁ G₃) (snd G₁ G₃ ≫ v')) ![fst G₁ G₂, snd G₁ G₂ ≫ u']
        ![fst G₁ G₃, snd G₁ G₃ ≫ v' ≫ u'] (Equiv.refl _) (fun i => by fin_cases i <;> simp) L₁) H)

theorem gAdj_swap_comp :
    (∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : LB G₁.left)
      (L₂ : LB G₂.left), L₁.IsLB → L₂.IsLB → ∀ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), GAdj L₁ L₂ u u' → GAdj L₂ L₁ u' u) ∧
    ∀ (S : Scheme.{0}) (G₁ G₂ G₃ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] [GrpObj G₃]
      [IsCommMonObj G₃] (L₁ : LB G₁.left) (L₂ : LB G₂.left) (L₃ : LB G₃.left), L₁.IsLB → L₂.IsLB → L₃.IsLB →
      ∀ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁) (v : G₂ ⟶ G₃) (v' : G₃ ⟶ G₂), GAdj L₁ L₂ u u' → GAdj L₂ L₃ v v' →
        GAdj L₁ L₃ (u ≫ v) (v' ≫ u') :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ H => gAdj_swap H,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ _ _ _ _ H H' => gAdj_comp h₁ h₂ h₃ H H'⟩

end GlobalTheory.MumFam
end
end

section
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumAdj

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D D₁ D₂ : DegData R (maximalIdeal R)}
  {A A₁ A₂ : PolAV (Sp (FractionRing R))} {G G₁ G₂ : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G₁] [IsCommMonObj G₁]
  [GrpObj G₂] [IsCommMonObj G₂]

theorem linHom_unique (hR : Base R) (hG : IsSemiAbelian G) {U : Unif (maximalIdeal R) D A G} {a a' k k' g g'}
    (h : LinHom U.toUnifPre U.toUnifPre a k g) (h' : LinHom U.toUnifPre U.toUnifPre a' k' g') (ha : a = a')
    (hk : ∀ y, k y = k' y) : g = g' := by
  obtain rfl := ha
  obtain rfl : k = k' := AddMonoidHom.ext hk
  obtain ⟨u₁, u₂⟩ := GlobalTheory.MumUniq.main R hR.1 D A G hG U a k
  exact u₂ g g' (congrFun (u₁ _ _ (linHom_iff_linEnd.1 h).2 (linHom_iff_linEnd.1 h').2))

theorem exists_linHom_end (hR : Base R) (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) {a a' h h'}
    (H : Adj (pol D) (pol D) a a' h h') : ∃ g, LinHom U.toUnifPre U.toUnifPre a h' g := by
  have hE := GlobalTheory.MumFam.AdjEnd.endData_of_adj R hR D a a' h h' H
  obtain ⟨b, hb⟩ := GlobalTheory.Mum.EndThick.formalEnd_exists R hR.1 D A G hG U a a' h h' hE
  obtain ⟨g, hg, e⟩ := GlobalTheory.T.mumford_formalEndomorphism_algebraic R hR D A G hG U a a' h h' hE b hb
  exact ⟨g, linHom_iff_linEnd.2 ⟨hg, (funext e : _ = b).symm ▸ hb⟩⟩

theorem exists_linHom (hR : Base R) (hG₁ : IsSemiAbelian G₁) (hG₂ : IsSemiAbelian G₂) (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁)
    (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) {a : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {a' : D₂.toPre.P.A ⟶ D₁.toPre.P.A}
    {h : D₁.toPre.X →+ D₂.toPre.X} {h' : D₂.toPre.X →+ D₁.toPre.X} (H : Adj (pol D₁) (pol D₂) a a' h h') :
    ∃ u u', LinHom U₁.toUnifPre U₂.toUnifPre a h' u ∧ LinHom U₂.toUnifPre U₁.toUnifPre a' h u' ∧
      GAdj U₁.LG.L U₂.LG.L u u' := by
  obtain ⟨D, A, U, i₁, p₁, i₂, p₂, j₁, q₁, j₂, q₂, hG, ip₁, ip₂, jq₁, jq₂, ad₁, ad₂, l₁, r₁, l₂, r₂, g₁, g₂⟩ :=
    GlobalTheory.T.product_uniformised_groups_sum_data R hR D₁ A₁ G₁ hG₁ U₁ D₂ A₂ G₂ hG₂ U₂
  have H' := GlobalTheory.MumFam.Adj.comp R _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.MumFam.Adj.comp R _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.MumFam.adj_symm R _ _ _ _ _ _ ad₁) H) ad₂
  obtain ⟨g, hg⟩ := exists_linHom_end hR hG U H'
  obtain ⟨g', hg'⟩ := exists_linHom_end hR hG U (GlobalTheory.MumFam.adj_symm R _ _ _ _ _ _ H')
  have ros : GAdj U.LG.L U.LG.L g g' := GlobalTheory.Mum.linEnd_adjoint_lbIso R hR D A _ hG U _ _ _ _ (GlobalTheory.MumFam.AdjEnd.endData_of_adj R hR D _ _ _ _ H') g g'
    (linHom_iff_linEnd.1 hg) (linHom_iff_linEnd.1 hg')
  refine ⟨_, _, ?_, ?_, GlobalTheory.MumFam.gAdj_swap_comp.2 _ _ _ _ _ _ _ U₁.LG.isLB U.LG.isLB U₂.LG.isLB _ _ _ _
    (GlobalTheory.MumFam.gAdj_swap_comp.2 _ _ _ _ _ _ _ U₁.LG.isLB U.LG.isLB U.LG.isLB _ _ _ _ g₁ ros)
    (GlobalTheory.MumFam.gAdj_swap_comp.1 _ _ _ _ _ U₂.LG.isLB U.LG.isLB _ _ g₂)⟩
  · have := (l₁.comp hg).comp r₂
    convert this using 1
    · change a = (i₁ ≫ (p₁ ≫ a) ≫ i₂) ≫ p₂
      simp only [Category.assoc, ip₂, Category.comp_id, reassoc_of% ip₁]
    · ext y
      change h' y = q₁ (j₁ (h' (q₂ (j₂ y))))
      rw [jq₁, jq₂]
  · have := l₂.comp (hg'.comp r₁)
    convert this using 1
    · change a' = i₂ ≫ (p₂ ≫ a' ≫ i₁) ≫ p₁
      simp only [Category.assoc, ip₁, Category.comp_id, reassoc_of% ip₂]
    · ext y
      change h y = q₂ (j₂ (h (q₁ (j₁ y))))
      rw [jq₁, jq₂]

end

theorem adj_groups : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (a' : D₂.toPre.P.A ⟶ D₁.toPre.P.A) (h : D₁.toPre.X →+ D₂.toPre.X) (h' : D₂.toPre.X →+ D₁.toPre.X), Adj (pol D₁) (pol D₂) a a' h h' → ∃ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), LinHom U₁.toUnifPre U₂.toUnifPre a h' u ∧ LinHom U₂.toUnifPre U₁.toUnifPre a' h u' ∧ GAdj U₁.LG.L U₂.LG.L u u' := fun R _ _ _ hR D₁ A₁ G₁ _ _ hG₁ U₁ D₂ A₂ G₂ _ _ hG₂ U₂ _ _ _ _ H =>
  exists_linHom hR hG₁ hG₂ U₁ U₂ H

end GlobalTheory.MumAdj
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroups_adjointHomPair_closedForm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (a' : D₂.toPre.P.A ⟶ D₁.toPre.P.A) (h : D₁.toPre.X →+ D₂.toPre.X) (h' : D₂.toPre.X →+ D₁.toPre.X), Adj (pol D₁) (pol D₂) a a' h h' → ∃ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), LinHom U₁.toUnifPre U₂.toUnifPre a h' u ∧ LinHom U₂.toUnifPre U₁.toUnifPre a' h u' ∧ GAdj U₁.LG.L U₂.LG.L u u' := by
  atlas_forward_decl GlobalTheory.MumAdj.adj_groups
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumIsoAdj

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem linHom_unique (hR : Base R) (hG : IsSemiAbelian G) {U : Unif (maximalIdeal R) D A G} {a a' k k' g g'}
    (h : LinHom U.toUnifPre U.toUnifPre a k g) (h' : LinHom U.toUnifPre U.toUnifPre a' k' g') (ha : a = a')
    (hk : ∀ y, k y = k' y) : g = g' := by
  obtain rfl := ha
  obtain rfl : k = k' := AddMonoidHom.ext hk
  obtain ⟨u₁, u₂⟩ := GlobalTheory.MumUniq.main R hR.1 D A G hG U a k
  exact u₂ g g' (congrFun (u₁ _ _ (linHom_iff_linEnd.1 h).2 (linHom_iff_linEnd.1 h').2))

end

theorem iso_of_factor_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ (ε : G ≅ G₀) (u : G' ⟶ G₀) (u' : G₀ ⟶ G'), IsMonHom ε.hom ∧ IsMonHom u ∧ IsMonHom u' ∧ ε.hom = inc ≫ u ∧ u ≫ u' = oG.act (Star.star F.e * F.f * F.e) ∧ GAdj U'.LG.L U₀.LG.L u u' := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi A₀ G₀ _ _ hG₀ U₀
  obtain ⟨-, hsym, g, hg⟩ := hF
  obtain ⟨u, u', hu, hu', hadj⟩ :=
    GlobalTheory.T.uniformisedGroups_adjointHomPair_closedForm R hR D' A' G' hG' U' D A₀ G₀ hG₀ U₀ _ _ _ _ (GlobalTheory.T.idempotentFactor_projection_adjointPair R _ D D' F)
  have hO : ∀ a : F.O, LinHom U'.toUnifPre U'.toUnifPre (F.o.onB.act a)
      (DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star a)) (oG.act a) := fun a =>
    ⟨oG.hom a, fun e => hlin.q_lin e a, fun e => by
      obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
      exact ⟨t, ht, hi⟩⟩
  have hu1 := hu.1
  have hu1' := hu'.1
  have hee : Star.star F.e * Star.star F.e = Star.star F.e := by rw [← star_mul, F.idem]
  have hsS : Star.star (Star.star F.e * F.f * F.e) = Star.star F.e * F.f * F.e := by
    rw [star_mul, star_mul, star_star, ← _root_.mul_assoc, ← hsym]
  have hsg : (Star.star F.e * F.f * F.e) * Star.star g = Star.star F.e := by
    have := congrArg Star.star hg
    rwa [star_mul, hsS] at this
  have hkey : F.e * Star.star g * (Star.star F.e * F.f * F.e) = F.e := by
    calc F.e * Star.star g * (Star.star F.e * F.f * F.e)
        = g * ((Star.star F.e * F.f * F.e) * Star.star g) * (Star.star F.e * F.f * F.e) := by
          nth_rewrite 1 [← hg]; simp only [_root_.mul_assoc]
      _ = g * (Star.star F.e * (Star.star F.e * F.f * F.e)) := by rw [hsg, _root_.mul_assoc]
      _ = F.e := by
          rw [← _root_.mul_assoc (Star.star F.e) (Star.star F.e * F.f) F.e,
            ← _root_.mul_assoc (Star.star F.e) (Star.star F.e) F.f, hee, hg]
  have hxi : ∀ y, F.xi y = F.e • F.xi y := fun y => by rw [← F.xi_xp, F.xp_xi]
  have hincE : F.inc ≫ F.o.onB.act F.e = F.inc := by
    rw [← F.pr_inc, ← Category.assoc, F.inc_pr, Category.id_comp]
  have h1 : u ≫ u' = oG.act (Star.star F.e * F.f * F.e) :=
    GlobalTheory.MumIsoAdj.linHom_unique hR hG' (hu.comp hu') (hO _)
      (by rw [F.o.onB.map_mul (Star.star F.e * F.f) F.e, ← F.pr_inc]; exact (Category.assoc _ _ _).symm)
      (fun y => by
        change (Star.star F.e * F.f) • F.xi (F.xp y) = Star.star (Star.star F.e * F.f * F.e) • y
        rw [hsS, F.xi_xp, smul_smul])
  have h2 : u' ≫ oG.act (F.e * g) ≫ u = 𝟙 G₀ :=
    GlobalTheory.MumIsoAdj.linHom_unique hR hG₀ ((hu'.comp (hO _)).comp hu) (LinHom.id _)
      (by
        calc ((F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) ≫ F.o.onB.act (F.e * g)) ≫ F.pr
            = F.inc ≫ F.o.onB.act ((F.e * g) * (Star.star F.e * F.f * F.e)) ≫ F.pr := by
              rw [F.o.onB.map_mul (F.e * g) (Star.star F.e * F.f * F.e),
                F.o.onB.map_mul (Star.star F.e * F.f) F.e]
              conv_lhs => rw [← hincE]
              simp only [Category.assoc]
          _ = 𝟙 _ := by
              rw [_root_.mul_assoc F.e g, hg, F.idem, ← F.pr_inc]
              simp only [← Category.assoc, F.inc_pr, Category.id_comp])
      (fun y => by
        change F.xp (Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y)) = y
        have hw : Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y) =
            (Star.star g * (Star.star F.e * F.f * F.e)) • F.xi y := by
          conv_lhs => rw [hxi y]
          rw [smul_smul, smul_smul, star_mul]
          congr 1
          simp only [_root_.mul_assoc]
          rw [← _root_.mul_assoc (Star.star F.e) (Star.star F.e), hee]
        have h3 : F.xi (F.xp (Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y))) = F.xi y := by
          rw [F.xi_xp, hw, smul_smul, ← _root_.mul_assoc, hkey, ← hxi]
        have := congrArg F.xp h3
        rwa [F.xp_xi, F.xp_xi] at this)
  refine ⟨⟨inc ≫ u, u' ≫ oG.act g ≫ pr, ?_, ?_⟩, u, u', inferInstance, hu.1, hu'.1, rfl, h1, hadj⟩
  · calc (inc ≫ u) ≫ u' ≫ oG.act g ≫ pr = inc ≫ ((u ≫ u') ≫ oG.act g) ≫ pr := by simp only [Category.assoc]
      _ = 𝟙 G := by
          rw [h1, ← oG.map_mul, hg, ← hpi]
          simp only [← Category.assoc, hip, Category.id_comp]
  · calc (u' ≫ oG.act g ≫ pr) ≫ inc ≫ u = u' ≫ (oG.act g ≫ pr ≫ inc) ≫ u := by simp only [Category.assoc]
      _ = 𝟙 G₀ := by rw [hpi, ← oG.map_mul, h2]

end GlobalTheory.MumIsoAdj
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_image_iso_uniformised_factor_with_adjoint_pair : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ (ε : G ≅ G₀) (u : G' ⟶ G₀) (u' : G₀ ⟶ G'), IsMonHom ε.hom ∧ IsMonHom u ∧ IsMonHom u' ∧ ε.hom = inc ≫ u ∧ u ≫ u' = oG.act (Star.star F.e * F.f * F.e) ∧ GAdj U'.LG.L U₀.LG.L u u' := by
  atlas_forward_decl GlobalTheory.MumIsoAdj.iso_of_factor_adj
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

noncomputable section
namespace GlobalTheory.Mum

open GlobalTheory.TorsionFormCompare in

theorem exists_unif_move_iso_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀] (ε : G ≅ G₀), IsMonHom ε.hom → IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ U : Unif (maximalIdeal R) D A₀ G, LBIso U.LG.L (U₀.LG.L.pull ε.hom.left) := by
  intro R _ _ _ hB D A₀ G G₀ _ _ _ _ ε hε hsa U₀
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have he : eSec G ≫ ε.hom.left = 𝟙 _ ≫ eSec G₀ := by
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ε.hom)
  let L' : RigLB G := ⟨U₀.LG.L.pull ε.hom.left, rigPullOf ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig,
    LB.isLB_pull U₀.LG.isLB _,
    GlobalTheory.CubePullLawChecks.rigPullIsGen ε.hom.left (𝟙 _) he U₀.LG.L U₀.LG.rig U₀.LG.isLB U₀.LG.rigGen⟩
  let w : LB.Iso L'.L (U₀.LG.L.pull ε.hom.left) := idIso L'.L
  have hw : RigAlong ε.hom U₀.LG L' w :=
    ⟨idIso_isGen L'.isLB, (maps_iff w _ (fun _ => eSec G₀) _ L'.rig U₀.LG.rig (𝟙 _) _
      (rigPull_le _ _ he U₀.LG.L) (fun _ => rfl)).1 (idIso_maps L')⟩
  obtain ⟨W, hW, hψ⟩ := psiOnExists R (maximalIdeal R) hR D
  obtain ⟨hD, hid⟩ := exists_isIdPull R D.toPre W hW hψ
  obtain ⟨bc, U, -, hb, -, hgen, hU⟩ :=
    exists_unif_move R (maximalIdeal R) D A₀ G₀ G ε hR hsa hε U₀ L' w hw hD
  obtain ⟨-, w', hw', -⟩ := sameUnif_of_isPullUnif R (maximalIdeal R) D A₀ G₀ G ε hD hid bc U₀ U hb hgen hU
  exact ⟨U, w', hw'.1⟩

end GlobalTheory.Mum
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_along_group_iso_lbIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀] (ε : G ≅ G₀), IsMonHom ε.hom → IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ U : Unif (maximalIdeal R) D A₀ G, LBIso U.LG.L (U₀.LG.L.pull ε.hom.left) := by
  atlas_forward_decl GlobalTheory.Mum.exists_unif_move_iso_lbIso
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.MumFam

theorem lbIso_lam_retract_adj : ∀ (S : Scheme.{0}) (G G' G₀ : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G₀] [IsCommMonObj G₀] (L : LB G.left) (L' : LB G'.left) (L₀ : LB G₀.left), L.IsLB → L'.IsLB → L₀.IsLB → ∀ (inc : G ⟶ G') (u : G' ⟶ G₀) (u' : G₀ ⟶ G') (E E' Fm : G' ⟶ G'), IsMonHom inc → IsMonHom u → inc ≫ E = inc → u ≫ u' = E ≫ Fm ≫ E' → GAdj L' L₀ u u' → GAdj L' L' E E' → LBIso L (L₀.pull (inc ≫ u).left) → LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm) : G2 G ⟶ G2 G').left) := by
  intro S G G' G₀ _ _ _ _ _ _ L L' L₀ hL hL' hL₀ inc u u' E E' Fm hinc hu hE huu hA hB hLL
  haveI := hinc
  haveI := hu
  have key : inc ≫ u ≫ u' = inc ≫ Fm ≫ E' := by
    rw [huu, ← Category.assoc inc E, hE]
  let P : G2 G ⟶ G2 G' := lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm)
  let Q : G2 G ⟶ G' ⊗ G₀ := lift (fst G G ≫ inc) (snd G G ≫ inc ≫ u)
  have hLam : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _
  have hLam' : (abelian₂ G' L').IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff hLam (pull_isLB hLam' _)).1 ?_
  rw [cls_pull hLam']
  have c1 : cls (abelian₂ G L) hLam =
      GlobalTheory.ZH.EndoExtend.cubeCls G₀ ![fst G G ≫ inc ≫ u, snd G G ≫ inc ≫ u] (cls L₀ hL₀) := by
    have e0 : cls L hL = CechPic.pull (inc ≫ u).left (cls L₀ hL₀) := (cls_eq_iff hL (pull_isLB hL₀ _)).2 hLL
    rw [show cls (abelian₂ G L) hLam = GlobalTheory.ZH.EndoExtend.cubeCls G (x2 G) (cls L hL) from
      GlobalTheory.ZH.EndoExtend.cls_cubeLB G _ hL, e0, GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom]
    congr 1
    ext i
    fin_cases i <;> simp [x2]
  have c2 : CechPic.pull P.left (cls (abelian₂ G' L') hLam') =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm] (cls L' hL') := by
    rw [show cls (abelian₂ G' L') hLam' = GlobalTheory.ZH.EndoExtend.cubeCls G' (x2 G') (cls L' hL') from
      GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL']
    exact GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ _ _ (fun i => by fin_cases i <;> simp [x2, P]) _
  have a1 : GlobalTheory.ZH.EndoExtend.cubeCls G₀ ![fst G' G₀ ≫ u, snd G' G₀] (cls L₀ hL₀) =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G₀, snd G' G₀ ≫ u'] (cls L' hL') :=
    (GlobalTheory.ZH.EndoExtend.cls_cubeLB G₀ _ hL₀).symm.trans
      (((cls_eq_iff _ _).2 hA).trans (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL'))
  have b1 := congrArg (CechPic.pull Q.left) a1
  rw [GlobalTheory.ZH.EndoExtend.pull_cubeCls G₀ _ ![fst G G ≫ inc ≫ u, snd G G ≫ inc ≫ u] Q
      (fun i => by fin_cases i <;> simp [Q]),
    GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm ≫ E'] Q
      (fun i => by fin_cases i <;> simp [Q, key])] at b1
  have a2 : GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G' ≫ E, snd G' G'] (cls L' hL') =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G', snd G' G' ≫ E'] (cls L' hL') :=
    (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL').symm.trans
      (((cls_eq_iff _ _).2 hB).trans (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL'))
  have b2 := congrArg (CechPic.pull P.left) a2
  rw [GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm] P
      (fun i => by fin_cases i <;> simp [P, hE]),
    GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm ≫ E'] P
      (fun i => by fin_cases i <;> simp [P])] at b2
  exact c1.trans (b1.trans (b2.symm.trans c2.symm))

end GlobalTheory.MumFam
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_retract_of_adjoint_pairs : ∀ (S : Scheme.{0}) (G G' G₀ : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G₀] [IsCommMonObj G₀] (L : LB G.left) (L' : LB G'.left) (L₀ : LB G₀.left), L.IsLB → L'.IsLB → L₀.IsLB → ∀ (inc : G ⟶ G') (u : G' ⟶ G₀) (u' : G₀ ⟶ G') (E E' Fm : G' ⟶ G'), IsMonHom inc → IsMonHom u → inc ≫ E = inc → u ≫ u' = E ≫ Fm ≫ E' → GAdj L' L₀ u u' → GAdj L' L' E E' → LBIso L (L₀.pull (inc ≫ u).left) → LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm) : G2 G ⟶ G2 G').left) := by
  atlas_forward_decl GlobalTheory.MumFam.lbIso_lam_retract_adj
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.MumDesc

theorem image_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso (abelian₂ G U.LG.L) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hi hp hip hpi
  obtain ⟨G₀, _, _, A₀, hG₀, ⟨U₀⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base R hR D
  obtain ⟨ε, u, u', hε, hu, -, he, huu, hadj⟩ :=
    GlobalTheory.T.idempotent_image_iso_uniformised_factor_with_adjoint_pair R hR D D' F hF A' G' hG' U' oA oG hlin G hG inc pr hi hp hip hpi A₀ G₀ hG₀ U₀
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_uniformisation_along_group_iso_lbIso R hR D A₀ G G₀ ε hε hG₀ U₀
  refine ⟨A₀, U, GlobalTheory.T.mumfordBundle_retract_of_adjoint_pairs _ G G' G₀ U.LG.L U'.LG.L U₀.LG.L U.LG.isLB U'.LG.isLB U₀.LG.isLB inc u u'
    (oG.act F.e) (oG.act (Star.star F.e)) (oG.act F.f) hi hu ?_ ?_ hadj
    (GlobalTheory.T.semiAbelian_groupAction_star_adjoint_bundle R hR D' A' G' hG' U' F.O F.o oA oG hlin F.e) (he ▸ hU)⟩
  · rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  · rw [huu, oG.map_mul, oG.map_mul]

end GlobalTheory.MumDesc
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_image_uniformised_by_factor_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso (abelian₂ G U.LG.L) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) := by
  atlas_forward_decl GlobalTheory.MumDesc.image_unif
end
