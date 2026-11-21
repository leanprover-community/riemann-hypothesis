import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTotalClosed
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureE8Power
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerBundleHypothesis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisedFibrewiseNonvanishingSection
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCpEvenOn
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UniformisationPowerWithoutExpansion
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypW_e8LB_powObj : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → GlobalTheory.LN.HypW (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ P.L.L W) := by
  first | exact @GlobalTheory.PowE8.hypW_e8LB | exact GlobalTheory.PowE8.hypW_e8LB | (intros; apply GlobalTheory.PowE8.hypW_e8LB <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SplitPow

theorem splitExtensionModuloIdeal_eighth_power : ∀ (R : Type) [CommRing R] (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (I : Ideal R),
    GlobalTheory.LN.SplitOver G₀ I → GlobalTheory.LN.SplitOver (powObj G₀ 8) I := by
  intro R _ G₀ _ _ I ⟨E, ⟨D⟩⟩
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  obtain ⟨p, -⟩ := GlobalTheory.isPowGrp_baseChange _ _ (spMap (Ideal.Quotient.mk I)) (powObj G₀ 8) G₀ 8 (powIsPowGrp G₀ 8)
  obtain ⟨pT, -⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Sp (R ⧸ I)) E.X (Fin 8 → E.X) 8 (AddEquiv.refl _)
  obtain ⟨q', hq, hq1, hq2, hq3, hq4, -⟩ :=
    GlobalTheory.PowMap.main _ _ _ (powObj E.B 8) E.B 8 p (powIsPowGrp E.B 8) D.q
  obtain ⟨i', hi, hi1, -⟩ := GlobalTheory.PowMap.main _ _ _ _ _ 8 pT p D.i
  have hB : IsAbelianScheme (powObj E.B 8) := (GlobalTheory.PowGrp.powers _ _ _ 8 (powIsPowGrp E.B 8)).2.2.2.1 E.isAbelian
  have hk := GlobalTheory.PowKernel.main _ _ _ _ _ _ _ 8 pT p (powIsPowGrp E.B 8) D.i D.q i' q' hi hq D.isKernel
  haveI : IsCommMonObj ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj G₀) := inferInstance
  haveI : IsCommMonObj ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj (powObj G₀ 8)) := inferInstance
  have hqc : QuasiCompact D.q.left := by
    have := D.q_affine
    infer_instance
  obtain ⟨O, h₁, h₂, h₃, h⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ (Fin 8 → E.X) _ (powObj E.B 8) hB q' i'
    (hq1 D.q_hom) (hi1 D.i_hom) (hq2 D.q_flat) (hq3 D.q_surjective) (hq4 hqc) hk
  obtain ⟨d, -, -⟩ := h hB
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory.SplitPow
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitOver_powObj_eight : ∀ (R : Type) [CommRing R] (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (I : Ideal R), GlobalTheory.LN.SplitOver G₀ I → GlobalTheory.LN.SplitOver (powObj G₀ 8) I := by
  atlas_forward_decl GlobalTheory.SplitPow.splitExtensionModuloIdeal_eighth_power
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SplitRed

theorem splitOver_of_unif : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))), Unif (maximalIdeal V₁) D₀ A₀ G₀ → IsSemiAbelian G₀ → GlobalTheory.LN.SplitOver G₀ (maximalIdeal V₁) := by
  intro V₁ _ _ _ _ D₀ G₀ _ _ A₀ U _
  obtain ⟨E, -, -, -, -, hE⟩ := GlobalTheory.gtCoord_isGt V₁ (IsLocalRing.maximalIdeal V₁) D₀.toPre 0 G₀ ⟨U.gt 0⟩
  have key : ∀ J : Ideal V₁, J = IsLocalRing.maximalIdeal V₁ →
      ∀ S : SplitExt (Spec (CommRingCat.of (V₁ ⧸ J))),
        S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G₀) →
        GlobalTheory.LN.SplitOver G₀ (IsLocalRing.maximalIdeal V₁) := by
    rintro J rfl S hS
    exact ⟨S, hS⟩
  exact key _ (pow_one _) E hE

end GlobalTheory.SplitRed
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_semiAbelian_split_mod_maximalIdeal : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))), Unif (maximalIdeal V₁) D₀ A₀ G₀ → IsSemiAbelian G₀ → GlobalTheory.LN.SplitOver G₀ (maximalIdeal V₁) := by
  atlas_forward_decl GlobalTheory.SplitRed.splitOver_of_unif
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

set_option maxHeartbeats 2000000 in

theorem exists_cp_evenOn : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ Pc : GlobalTheory.UU.CP (powObj G₀ 8), Pc.L.L = GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W ∧ GlobalTheory.Mum.EvenOn Pc := by
  intro hL _ _ V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ hS W hW
  let P₁ : GlobalTheory.UU.CP G₀ := GlobalTheory.ValueForm.modelCP U₀.toUnifPre hL.globalFns
  obtain ⟨Pc, hPc⟩ := GlobalTheory.T.cubical_structure_e8_power _ G₀ P₁ W
  refine ⟨Pc, hPc, ?_⟩
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨D', ⟨pD⟩⟩ := GlobalTheory.PowDegData.main hL.globalFns V₁ _ D₀ 8
  obtain ⟨A', pA, -⟩ := GlobalTheory.exists_powPolAV _ A₀ 8
  obtain ⟨U', -⟩ := GlobalTheory.PowUnif.main hL.globalFns V₁ _ 8 D₀ D' A₀ A' G₀ (powObj G₀ 8) pD pA (powIsPowGrp G₀ 8)
    U₀.toUnifPre
  have hp : IsProper (pullback.snd (powObj G₀ 8).hom (jK V₁)) := by
    have := A'.isAb.proper
    have e : pullback.snd (powObj G₀ 8).hom (jK V₁) = U'.gen.hom.left ≫ A'.A.hom := (Over.w U'.gen.hom).symm
    have : IsIso U'.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U'.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U'.gen.hom.left A'.A.hom inferInstance A'.isAb.proper
  have h3 := GlobalTheory.EvenTriv.surjective_cube_of_generic (powObj G₀ 8) hS8 hp
  obtain ⟨w, -, hw, -, -, hwL, -⟩ := GlobalTheory.PowE8.hypW_e8LB _ G₀ P₁ W hW
  have hwL' : LBIso Pc.L.L (cubeLB (powObj G₀ 8) ![𝟙 _, w] Pc.L.L) := by rw [hPc]; exact hwL
  obtain ⟨P₀, v, hv⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal V₁) 0 Pc
  have hB' : IsAbelianScheme (thickObj V₁ (maximalIdeal V₁) 0 D'.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D'.toPre.P.isAb
  let Q₀ := GlobalTheory.Mum.tqOfGtCoord (U'.gt 0) hB'
  have hm : (maximalIdeal V₁ ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (V₁ ⧸ maximalIdeal V₁ ^ (0 + 1)) := Ideal.Quotient.field _
  have hS0 := IsSemiAbelian.pullback (thick V₁ (maximalIdeal V₁) 0) (powObj G₀ 8) hS8
  have := hS0.smooth
  have := hS0.geomConnected
  have := Q₀.i_hom
  letI := D'.toPre.addX
  haveI := D'.toPre.freeX
  haveI := D'.toPre.finX
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (V₁ ⧸ maximalIdeal V₁ ^ (0 + 1)) D'.toPre.X
    (thickObj V₁ (maximalIdeal V₁) 0 (powObj G₀ 8)) P₀.L P₀.c Q₀.i Q₀.i_hom
  haveI := hw
  obtain ⟨σ, hσ⟩ := GlobalTheory.EvenTriv.exists_even_of_surjective h3 Pc w hwL' P₀
    (IsPullback.of_hasPullback (powObj G₀ 8).hom (thick V₁ (maximalIdeal V₁) 0)) hv Q₀.i s
  exact ⟨D'.toPre.X, D'.toPre.addX, D'.toPre.freeX, D'.toPre.finX, Q₀, P₀, ⟨v, hv⟩, σ, hσ⟩

end GlobalTheory.PowE8
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubical_e8LB_evenOn : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ Pc : GlobalTheory.UU.CP (powObj G₀ 8), Pc.L.L = GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W ∧ GlobalTheory.Mum.EvenOn Pc := by
  atlas_forward_decl GlobalTheory.PowE8.exists_cp_evenOn
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.E8LatticePullbackGeneric

open GlobalTheory.CechPic

theorem sum_lamPts {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x y : T ⟶ G) (c : Pic G.left) (w : ℤ) :
    ∑ k : Fin 4, (-(w * GlobalTheory.PolDeg.negε k)) • pull (GlobalTheory.PolDeg.lamPts x y k) c = w • lam c x y := by
  simp only [Fin.sum_univ_four, GlobalTheory.PolDeg.lamPts, GlobalTheory.PolDeg.negε, lam, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [smul_add, smul_sub, mul_neg, mul_one, neg_neg, neg_smul]
  first
  | (norm_num; done)
  | (norm_num; abel)
  | (push_cast; abel)
  | (rw [sub_eq_add_neg, sub_eq_add_neg]; congr 1 <;> [congr 1; skip] <;> norm_num)

theorem lam_pull_hom {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G'] (φ : G' ⟶ G) [IsMonHom φ]
    (c : Pic G.left) (x y : T ⟶ G') : lam (pull φ.left c) x y = lam c (x ≫ φ) (y ≫ φ) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, MonObj.mul_comp, MonObj.one_comp]

theorem pull_fst_lam {S S' : Scheme.{0}} (f : S' ⟶ S) {X G : Over S} [GrpObj G] (c : Pic G.left) (x x' : X ⟶ G) :
    GlobalTheory.CechPic.pull (pullback.fst X.hom f) (lam c x x') =
      lam (GlobalTheory.CechPic.pull (pullback.fst G.hom f) c) ((Over.pullback f).map x) ((Over.pullback f).map x') := by
  have hfst : ∀ z : X ⟶ G, pullback.fst X.hom f ≫ z.left = ((Over.pullback f).map z).left ≫ pullback.fst G.hom f :=
    fun z => by simp [pullback.lift_fst]
  simp only [lam, map_add, map_sub, ← pull_comp, hfst, Functor.map_mul, Functor.map_one]

open GlobalTheory.E8LatticePullbackGeneric GlobalTheory.CechPic in

theorem exists_polAV_gen : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ (A : PolAV (Sp (FractionRing V₁))) (gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  intro hL₁ _ _ V₁ _ _ _ _ D₀ G₀ _ _ A₀ U₀ _ W hW
  have := A₀.isAb.comm

  let c := GlobalTheory.EighthPowerFactor.siegOne hL₁.globalFns A₀.isAb A₀.isLB A₀.g
  have hc1 : RelAmple c.A c.diag := GlobalTheory.EighthPowerFactor.relAmple_diag_lam A₀.isAb A₀.isLB
    (GlobalTheory.Moduli.cube_of_isLB _ A₀ A₀.L A₀.isLB) A₀.ample
  have hb := GlobalTheory.EighthPower.isSymBilin hL₁.globalFns c hc1
  have hpw := GlobalTheory.PowGrp.powers _ _ _ 8 (powIsPowGrp A₀.A 8)
  have hu : ∀ (T : Over (Sp (FractionRing V₁))) (y : Fin 8 → (T ⟶ A₀.A)),
      ∃! x : T ⟶ powObj A₀.A 8, ∀ u, x ≫ powPr A₀.A u = y u := fun T y =>
    ⟨(powIsLimit A₀.A 8).lift (Fan.mk T y), fun u => (powIsLimit A₀.A 8).fac _ ⟨u⟩,
      fun x hx => (powIsLimit A₀.A 8).hom_ext fun ⟨u⟩ => by rw [(powIsLimit A₀.A 8).fac]; exact hx u⟩
  let Q : PolAV (Sp (FractionRing V₁)) :=
    { A := powObj A₀.A 8, isAb := hpw.2.2.2.1 A₀.isAb, g := 8 * A₀.g, smoothDim := hpw.2.2.1 _ A₀.smoothDim
      L := GlobalTheory.MatrixBundle.matLB c.P (powPr A₀.A) W, isLB := LB.isLB_linComb c.isLB _ _
      rigid := GlobalTheory.MatrixBundle.rigidified_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u)
      sym := GlobalTheory.MatrixBundle.sym_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u)
      ample := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hL₁.globalFns _ _ 8 _ _ _ _ c _ (powPr A₀.A) W
        (fun u => powPr.isMonHom A₀.A u) hu hc1 hW.1
      ktriv := GlobalTheory.MatrixBundle.kTriv_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u) hu hW.2
        (fun T x hx => GlobalTheory.SiegelOfPolarised.eq_one_of_lam A₀.isLB A₀.ktriv x hx) }

  let F := Over.pullback (jK V₁)
  have hP : IsLimit (Fan.mk (F.obj (powObj G₀ 8)) fun u => F.map (powPr G₀ u)) :=
    isLimitFanMkObjOfIsLimit F _ _ (powIsLimit G₀ 8)
  let y : Fin 8 → (F.obj (powObj G₀ 8) ⟶ A₀.A) := fun u => F.map (powPr G₀ u) ≫ U₀.gen.hom
  let gen : F.obj (powObj G₀ 8) ≅ Q.A :=
    { hom := (powIsLimit A₀.A 8).lift (Fan.mk _ y)
      inv := hP.lift (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv)
      hom_inv_id := hP.hom_ext fun ⟨u⟩ => by
        simp only [Fan.mk_pt, Fan.mk_π_app, Category.assoc, Category.id_comp]
        erw [hP.fac (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv) ⟨u⟩]
        simp only [Fan.mk_π_app]
        erw [(powIsLimit A₀.A 8).fac_assoc (Fan.mk _ y) ⟨u⟩]
        simp [y]
      inv_hom_id := (powIsLimit A₀.A 8).hom_ext fun ⟨u⟩ => by
        simp only [Fan.mk_pt, Fan.mk_π_app, Category.assoc, Category.id_comp]
        erw [(powIsLimit A₀.A 8).fac (Fan.mk _ y) ⟨u⟩]
        simp only [Fan.mk_π_app, y]
        rw [← Category.assoc]
        erw [hP.fac (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv) ⟨u⟩]
        simp }
  have hgen : ∀ u, gen.hom ≫ powPr A₀.A u = y u := fun u => (powIsLimit A₀.A 8).fac _ ⟨u⟩
  have := U₀.gen_hom
  refine ⟨Q, gen, ?_, ?_⟩
  · refine GlobalTheory.EighthPowerFactor.isMonHom_of_coord (fun u => powPr.isMonHom A₀.A u) hu fun u => ?_
    rw [hgen u]
    infer_instance
  · have hA := A₀.isLB
    have hLG := U₀.LG.isLB
    have hQ : Q.L.IsLB := Q.isLB
    have hE : (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).IsLB := LB.isLB_linComb hLG _ _
    have hext : pull (pullback.fst G₀.hom (jK V₁)) (cls _ hLG) = pull U₀.gen.hom.left (cls _ hA) := by
      obtain ⟨w, hw⟩ := U₀.ext
      have e := (cls_eq_iff (pull_isLB hA _) (pull_isLB hLG _)).2 ⟨w, hw⟩
      rw [cls_pull hA, cls_pull hLG] at e
      exact e.symm
    have key : ∀ x x' : powObj G₀ 8 ⟶ G₀, pull (pullback.fst (powObj G₀ 8).hom (jK V₁)) (lam (cls _ hLG) x x') =
        lam (cls _ hA) (F.map x ≫ U₀.gen.hom) (F.map x' ≫ U₀.gen.hom) := by
      intro x x'
      rw [pull_fst_lam, hext, lam_pull_hom]
    have hlam : cls c.P c.isLB = lam (cls _ hA) (fst A₀.A A₀.A) (snd A₀.A A₀.A) := cls_cube_two hA _ _ c.isLB
    have eL : pull gen.hom.left (cls Q.L hQ) =
        ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • lam (cls _ hA) (y uv.1) (y uv.2) := by
      rw [show cls Q.L hQ = _ from cls_linComb c.isLB
        (fun uv : Fin 8 × Fin 8 => (lift (powPr A₀.A uv.1) (powPr A₀.A uv.2)).left) (fun uv => W uv.1 uv.2) hQ, map_sum]
      refine Finset.sum_congr rfl fun uv _ => ?_
      rw [map_zsmul, hlam]
      erw [pull_lam, pull_lam]
      rw [lift_fst, lift_snd]
      erw [hgen, hgen]
    have eR : pull (pullback.fst (powObj G₀ 8).hom (jK V₁)) (cls _ hE) =
        ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • lam (cls _ hA) (y uv.1) (y uv.2) := by
      rw [show cls _ hE = _ from cls_linComb hLG (K := (Fin 8 × Fin 8) × Fin 4)
        (fun k => GlobalTheory.PolDeg.lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
        (fun k => -(W k.1.1 k.1.2 * GlobalTheory.PolDeg.negε k.2)) hE, Fintype.sum_prod_type]
      simp only [sum_lamPts, map_sum, map_zsmul, key, y]
    refine (cls_eq_iff (pull_isLB hQ _) (pull_isLB hE _)).1 ?_
    rw [cls_pull hQ, cls_pull hE, eL, eR]

end GlobalTheory.E8LatticePullbackGeneric

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polAV_generic_fibre_e8LB : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ (A : PolAV (Sp (FractionRing V₁))) (gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  atlas_forward_decl GlobalTheory.E8LatticePullbackGeneric.exists_polAV_gen
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

theorem thetaNZ_e8LB : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → GlobalTheory.LN.ThetaNZ (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W) := by
  intro hL hL2 hE V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ hS W hW
  have hB : GlobalTheory.Mum.Base V₁ := by
    obtain ⟨h1, h2, h3, h4⟩ := hCN
    exact ⟨⟨h1, inferInstance, h2, h3⟩, h4⟩
  obtain ⟨Pc, hPc, hEv⟩ := GlobalTheory.T.exists_cubical_e8LB_evenOn hL hL2 hE V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  obtain ⟨A, gen, hgen, hA⟩ := GlobalTheory.T.exists_polAV_generic_fibre_e8LB hL hL2 hE V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨D, U, hU, -⟩ := GlobalTheory.T.exists_preUniformisation_even_torus_completeNormal V₁ hB _ Pc hS8 hEv A gen hgen (hPc ▸ hA)
  have h := GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section V₁ hB D A _ U (hU ▸ hEv)
  rw [hU, hPc] at h
  exact h

end GlobalTheory.PowE8
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaNZ_e8LB_powObj : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → GlobalTheory.LN.ThetaNZ (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W) := by
  atlas_forward_decl GlobalTheory.PowE8.thetaNZ_e8LB
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SharpGen
open GlobalTheory.PowE8

theorem exists_gen {S T : Scheme.{0}} (f : T ⟶ S) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] {B C : Over T}
    [GrpObj B] [GrpObj C] (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniq : ∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a)
    (u : (Over.pullback f).obj G₀ ≅ C) [IsMonHom u.hom] :
    ∃ gen : (Over.pullback f).obj (powObj G₀ 8) ≅ B, IsMonHom gen.hom ∧
      ∀ a, gen.hom ≫ pr a = (Over.pullback f).map (powPr G₀ a) ≫ u.hom := by
  let hl := isLimitOfPreserves (Over.pullback f) (powIsLimit G₀ 8)
  let ρ : Fin 8 → ((Over.pullback f).obj (powObj G₀ 8) ⟶ (Over.pullback f).obj G₀) :=
    fun a => (Over.pullback f).map (powPr G₀ a)
  choose x hx hxu using fun (T' : Over T) (y : Fin 8 → (T' ⟶ C)) => huniq T' y
  let inv : B ⟶ (Over.pullback f).obj (powObj G₀ 8) :=
    hl.lift ⟨B, Discrete.natTrans fun a => pr a.as ≫ u.inv⟩
  have hinv : ∀ a, inv ≫ ρ a = pr a ≫ u.inv := fun a => hl.fac ⟨B, Discrete.natTrans fun a => pr a.as ≫ u.inv⟩ ⟨a⟩
  let hom := x _ (fun a => ρ a ≫ u.hom)
  have hhom : ∀ a, hom ≫ pr a = ρ a ≫ u.hom := hx _ _
  refine ⟨⟨hom, inv, ?_, ?_⟩, ?_, hhom⟩
  · refine hl.hom_ext fun ⟨a⟩ => ?_
    show (hom ≫ inv) ≫ ρ a = 𝟙 _ ≫ ρ a
    rw [Category.assoc, hinv, ← Category.assoc, hhom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Category.id_comp]
  · have h1 := hxu B (fun a => pr a) (inv ≫ hom) (fun a => by
      rw [Category.assoc, hhom, ← Category.assoc, hinv, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have h2 := hxu B (fun a => pr a) (𝟙 B) (fun a => Category.id_comp _)
    exact h1.trans h2.symm
  · have hm : ∀ a, IsMonHom (hom ≫ pr a) := fun a => by rw [hhom]; infer_instance
    constructor
    · have h1 := hxu _ (fun a => η[C]) (η ≫ hom) (fun a => by
        haveI := hm a; rw [Category.assoc]; exact IsMonHom.one_hom (hom ≫ pr a))
      have h2 := hxu _ (fun a => η[C]) η (fun a => by haveI := hpr a; exact IsMonHom.one_hom (pr a))
      exact h1.trans h2.symm
    · have h1 := hxu _ (fun a => ((hom ≫ pr a) ⊗ₘ (hom ≫ pr a)) ≫ μ[C]) (μ ≫ hom) (fun a => by
        haveI := hm a; rw [Category.assoc]; exact IsMonHom.mul_hom (hom ≫ pr a))
      have h2 := hxu _ (fun a => ((hom ≫ pr a) ⊗ₘ (hom ≫ pr a)) ≫ μ[C]) ((hom ⊗ₘ hom) ≫ μ) (fun a => by
        haveI := hpr a; rw [Category.assoc, IsMonHom.mul_hom (pr a), ← Category.assoc, tensorHom_comp_tensorHom])
      exact h1.trans h2.symm

theorem lift_lamφ {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (x y : T ⟶ B)
    (I : ULift.{0} (Finset (Fin 2))) :
    (lift x y).left ≫ GlobalTheory.PrimCocycle.lamφ B I = (psum B ![x, y] I.down).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I.down).trans
    (congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))

theorem psum_comp_hom {S : Scheme.{0}} {B C T : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C]
    (u : B ⟶ C) [IsMonHom u] (x y : T ⟶ B) (I : Finset (Fin 2)) :
    psum C ![x ≫ u, y ≫ u] I = psum B ![x, y] I ≫ u :=
  ((congrArg (fun q => psum C q I) (funext fun i => by fin_cases i <;> rfl)).trans
    (psum_hom (MonoidHom.mk' (fun z : T ⟶ B => z ≫ u) fun a b => MonObj.mul_comp a b u) ![x, y] I).symm)

theorem zpow_lam {U : Type} [CommGroup U] (a b c d : U) (w : ℤ) :
    (a * b⁻¹ * c⁻¹ * d) ^ w = a ^ (-(w * negε 0)) * b ^ (-(w * negε 1)) * c ^ (-(w * negε 2)) * d ^ (-(w * negε 3)) := by
  simp only [negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, mul_zpow, inv_zpow', mul_neg, mul_one, neg_neg]
  norm_num

theorem gen_eighthPower : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ P.A, IsMonHom gen.hom ∧ LBIso (P.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  intro g n o _ ζ F W V₁ _ _ _ D₀ G₀ _ _ A₀ U₀ y α α₂ hcart hsq hlb P hP
  obtain ⟨c, ⟨φ, φ₂, hφ, hφsq, hφlb, -⟩, pr, prh, prl, hPL⟩ := hP
  obtain ⟨e, he, heα⟩ := grpPullback_iso hcart hφ
  haveI := he
  haveI := U₀.gen_hom
  haveI : IsMonHom (U₀.gen ≪≫ e).hom := by rw [Iso.trans_hom]; infer_instance
  obtain ⟨gen, hgen, hcoord⟩ := exists_gen (jK V₁) G₀ pr prh prl (U₀.gen ≪≫ e)
  refine ⟨gen, hgen, ?_⟩
  have hA0 := A₀.isLB
  have hc := c.isLB
  have hLG := U₀.LG.isLB
  have hPl := P.isLB
  have hU := F.univ.isLB
  let ρ : Fin 8 → ((Over.pullback (jK V₁)).obj (powObj G₀ 8) ⟶ (Over.pullback (jK V₁)).obj G₀) :=
    fun a => (Over.pullback (jK V₁)).map (powPr G₀ a)
  let e₂ : (G2 A₀.A).left ⟶ (G2 c.A).left := (lift (fst _ _ ≫ e.hom) (snd _ _ ≫ e.hom)).left
  let mAB : Fin 8 × Fin 8 → (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).left ⟶ (G2 A₀.A).left) :=
    fun ab => (lift (ρ ab.1 ≫ U₀.gen.hom) (ρ ab.2 ≫ U₀.gen.hom)).left
  have hm : ∀ ab : Fin 8 × Fin 8, mAB ab ≫ e₂ = gen.hom.left ≫ (lift (pr ab.1) (pr ab.2)).left := fun ab => by
    simp only [mAB, e₂, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, hcoord, Iso.trans_hom,
      Category.assoc]
    rfl
  have he₂ : e₂ ≫ φ₂ = α₂ := by
    apply pullback.hom_ext
    · have h1 : (fst F.univ.A F.univ.A).left = pullback.fst _ _ := rfl
      rw [← h1, Category.assoc, hφsq.1, hsq.1, ← heα]
      simp only [e₂, ← Category.assoc, ← Over.comp_left, lift_fst]
    · have h1 : (snd F.univ.A F.univ.A).left = pullback.snd _ _ := rfl
      rw [← h1, Category.assoc, hφsq.2, hsq.2, ← heα]
      simp only [e₂, ← Category.assoc, ← Over.comp_left, lift_snd]
  have Q1 : LBIso (c.P.pull e₂) (abelian₂ A₀.A A₀.L) := by
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (GlobalTheory.PowPrimitive.lbIso_linComb hφlb (fun _ : PUnit => e₂) (fun _ => 1)) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (GlobalTheory.PrimNorm.lbIso_nested hU (fun _ : PUnit => φ₂) (fun _ => 1) (fun _ : PUnit => e₂) (fun _ => 1)
        (fun _ : PUnit => α₂) (fun _ => 1) (by simp [he₂])) ?_
    exact hlb.symm
  let q := pullback.fst (powObj G₀ 8).hom (jK V₁)
  let q0 := pullback.fst G₀.hom (jK V₁)
  let n : (Fin 8 × Fin 8) × ULift.{0} (Finset (Fin 2)) →
      (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).left ⟶ ((Over.pullback (jK V₁)).obj G₀).left) :=
    fun p => (psum _ ![ρ p.1.1, ρ p.1.2] p.2.down).left
  let κ : (Fin 8 × Fin 8) × ULift.{0} (Finset (Fin 2)) → ℤ := fun p => GlobalTheory.PrimCocycle.lamε p.2 * W p.1.1 p.1.2
  have hn : ∀ ab I, mAB ab ≫ GlobalTheory.PrimCocycle.lamφ A₀.A I = n (ab, I) ≫ U₀.gen.hom.left := fun ab I => by
    rw [lift_lamφ, psum_comp_hom]; rfl
  let Uq : Over.mk (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).hom ≫ jK V₁) ⟶ powObj G₀ 8 :=
    Over.homMk q pullback.condition
  have hq : ∀ ab I, n (ab, I) ≫ q0 = q ≫ (lift (powPr G₀ ab.1) (powPr G₀ ab.2)).left ≫ GlobalTheory.PrimCocycle.lamφ G₀ I :=
    fun ab I => by
      rw [lift_lamφ]
      refine psum_push (isGrpPullback_pullback G₀ (jK V₁)) _ _ Uq (fun i => ?_) I.down
      apply Over.OverMorphism.ext
      fin_cases i
      · exact pullback.lift_fst _ _ _
      · exact pullback.lift_fst _ _ _
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PowPrimitive.lbIso_linComb hPL (fun _ : PUnit => gen.hom.left) (fun _ => 1)) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hc _ _ (fun _ : PUnit => gen.hom.left) (fun _ => 1) (fun ab => mAB ab ≫ e₂)
      (fun ab => W ab.1 ab.2) (by simp [hm])) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hc (fun _ : PUnit => e₂) (fun _ => 1) mAB (fun ab => W ab.1 ab.2)
      (fun ab => mAB ab ≫ e₂) (fun ab => W ab.1 ab.2) (by simp)).symm ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PowPrimitive.lbIso_linComb Q1 mAB (fun ab => W ab.1 ab.2)) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hA0 (GlobalTheory.PrimCocycle.lamφ A₀.A) GlobalTheory.PrimCocycle.lamε mAB (fun ab => W ab.1 ab.2)
      (fun p => n p ≫ U₀.gen.hom.left) κ ?_) ?_
  · refine Eq.trans ?_ (Fintype.prod_prod_type _).symm
    refine Fintype.prod_congr _ _ fun ab => ?_
    rw [← Finset.prod_zpow]
    refine Fintype.prod_congr _ _ fun I => ?_
    rw [← zpow_mul, hn]
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hA0 (fun _ : PUnit => U₀.gen.hom.left) (fun _ => 1) n κ
      (fun p => n p ≫ U₀.gen.hom.left) κ (by simp)).symm ?_
  obtain ⟨w, hw⟩ := U₀.ext
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (GlobalTheory.PowPrimitive.lbIso_linComb ⟨w, hw⟩ n κ) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hLG (fun _ : PUnit => q0) (fun _ => 1) n κ (fun p => n p ≫ q0) κ (by simp)) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    ((GlobalTheory.PrimNorm.lbIso_iff hLG (fun p => n p ≫ q0) κ
      (fun k : (Fin 8 × Fin 8) × Fin 4 => q ≫ lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
      (fun k => -(W k.1.1 k.1.2 * negε k.2))).2 ?_) ?_
  · refine ((Fintype.prod_prod_type _).trans ?_).trans (Fintype.prod_prod_type _).symm
    refine Fintype.prod_congr _ _ fun ab => ?_
    have e1 : ∏ I, GlobalTheory.PrimNorm.cls U₀.LG.L (n (ab, I) ≫ q0) ^ κ (ab, I) =
        (∏ I, (fun m => GlobalTheory.PrimNorm.cls U₀.LG.L (q ≫ m))
          ((lift (powPr G₀ ab.1) (powPr G₀ ab.2)).left ≫ GlobalTheory.PrimCocycle.lamφ G₀ I) ^ GlobalTheory.PrimCocycle.lamε I) ^
          W ab.1 ab.2 := by
      rw [← Finset.prod_zpow]
      refine Fintype.prod_congr _ _ fun I => ?_
      rw [← zpow_mul, hq]
    rw [e1]
    refine (congrArg (· ^ W ab.1 ab.2) (GlobalTheory.PrimCocycle.prod_lam (powPr G₀ ab.1) (powPr G₀ ab.2)
      (fun m => GlobalTheory.PrimNorm.cls U₀.LG.L (q ≫ m)))).trans ?_
    rw [Fin.prod_univ_four]
    exact zpow_lam _ _ _ _ _
  exact (GlobalTheory.PrimNorm.lbIso_nested hLG
    (fun k : (Fin 8 × Fin 8) × Fin 4 => lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
    (fun k => -(W k.1.1 k.1.2 * negε k.2)) (fun _ : PUnit => q) (fun _ => 1) _ _ (by simp)).symm

end GlobalTheory.SharpGen
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_eighth_power_uniformised_is_polarised : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ P.A, IsMonHom gen.hom ∧ LBIso (P.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  atlas_forward_decl GlobalTheory.SharpGen.gen_eighthPower
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

theorem isAdmissibleBase_of_completeNormalLocalCharZero (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (h : IsCN V₁) :
    GlobalTheory.LN.admitted V₁ (maximalIdeal V₁) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  letI : Field (V₁ ⧸ maximalIdeal V₁) := Ideal.Quotient.field _
  exact ⟨⟨h1, inferInstance, h2, h3⟩, h3, h4, inferInstance, inferInstance⟩

theorem exists_unif_pow8 : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ D : DegData V₁ (maximalIdeal V₁), Nonempty (Unif (maximalIdeal V₁) D P (powObj G₀ 8)) := by
  intro g n o _ ζ F W hW V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α α₂ hS hpb hsq hlb P hP
  have hL := GlobalTheory.abelianSchemeLaws_all
  let P₀ := GlobalTheory.ValueForm.modelCP U₀.toUnifPre hL.1.globalFns
  obtain ⟨Pc, hPc⟩ := GlobalTheory.T.cubical_structure_e8_power _ G₀ P₀ W
  obtain ⟨gen, hgen, hA⟩ := GlobalTheory.T.generic_eighth_power_uniformised_is_polarised g n o ζ F W V₁ D₀ G₀ A₀ U₀ y α α₂ hpb hsq hlb P hP
  have hW8 : GlobalTheory.LN.HypW (powObj G₀ 8) Pc.L.L := hPc ▸ GlobalTheory.T.hypW_e8LB_powObj _ G₀ P₀ W hW
  have hT : GlobalTheory.LN.ThetaNZ (powObj G₀ 8) Pc.L.L :=
    hPc ▸ GlobalTheory.T.thetaNZ_e8LB_powObj hL.1 hL.2 GlobalTheory.LN.ega_holds V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  have hA' : LBIso (P.L.pull gen.hom.left) (Pc.L.L.pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := hPc ▸ hA
  letI : Field (V₁ ⧸ maximalIdeal V₁) := Ideal.Quotient.field _
  obtain ⟨D, U, -, -⟩ := GlobalTheory.PrimeUnif.exists_unif hL.1 hL.2 GlobalTheory.laws3 GlobalTheory.LN.ega_holds GlobalTheory.uniformisation_total_closed V₁
    (maximalIdeal V₁) (isAdmissibleBase_of_completeNormalLocalCharZero V₁ hCN) inferInstance (powObj G₀ 8) Pc
    (GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS) hW8
    (GlobalTheory.T.splitOver_powObj_eight V₁ G₀ _ (GlobalTheory.T.uniformised_semiAbelian_split_mod_maximalIdeal V₁ hCN D₀ G₀ A₀ U₀ hS)) hT P gen hgen hA'
  exact ⟨D, ⟨U⟩⟩

end GlobalTheory.PowE8
end
end
