import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralBottomDatumStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralBottomDatum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BotHypMatch
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselCompatibilityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Placed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselCompatibility
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchingTranslatesBottomStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchingTranslatesBottom
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FinECentralRatioMemStStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseMovesVectorZStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseMovesVectorZ
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelIntegralTwistStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelIntegralTwist
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.LevNorm
open Formalism.BasicNotions.TH
end GlobalTheory.LevNorm
theorem GlobalTheory.MiTop.matches_differ_central_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → 1 ≤ D.R.rS → ∀ (u : D.what₂.Word) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ t ∈ GfC (D.sp.Y 0), ∀ t' ∈ GfC (D.sp.Y 0), Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t → Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t' → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ ∃ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, t = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o a * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * z * t' * k := by
  intro D L hT Gi Gl Kc Yd cX ex W _ hρ u B t _ t' _ ht ht'
  exact GlobalTheory.LevNorm.matches_differ W.S.X W.Q.instEq hρ u B ht ht'
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_translates_bottom_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → 1 ≤ D.R.rS → ∀ (u : D.what₂.Word) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ t ∈ GfC (D.sp.Y 0), ∀ t' ∈ GfC (D.sp.Y 0), Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t → Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t' → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ ∃ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, t = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o a * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * z * t' * k := by
  atlas_forward_decl _root_.GlobalTheory.MiTop.matches_differ_central_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.LocMod Matrix
noncomputable section
namespace GlobalTheory.MiTop.MoveZ
section Two
variable {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
end Two
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem addChar_uniformizer_eq_chi_of_gRead (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (PP : (_root_.GlobalTheory.Fam.pk_z W).Pg) : ∃ χ : 𝓞 D.host.E → ℂ, ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (n : ℕ)
    (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ i, pl i = PP → ∀ z : 𝓞 D.host.E,
      ((G i).S.ψ ((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k) * (ofSplit (G i).q).pr (z : D.host.E)) : ℂ) = χ z := by
  classical
  have hr : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hk : 2 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  let a : Fin D.R.r := ⟨0, by omega⟩
  let b : Fin D.R.r := ⟨1, by omega⟩
  have hab : a ≠ b := fun e => by have := congrArg Fin.val e; simp [a, b] at this
  let g : 𝓞 D.host.E → ∀ P : (_root_.GlobalTheory.Fam.pk_z W).Pg, GL (Fin D.R.r) (kP P.1) := fun z P =>
    elem a b hab (Ideal.Quotient.mk P.1.asIdeal (if P = PP then z else 0))
  refine ⟨fun z => if h : g z ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H then (((_root_.GlobalTheory.Fam.complexLevelStructure W).chi ⟨g z, h⟩ : ℂˣ) : ℂ) else 0, ?_⟩
  intro u f v n G pl hG i hi z
  have hex : ∀ j, ∃ x, GlobalTheory.LevZero.Red (G j) (pl j).1 x (g z (pl j)) := fun j =>
    (GlobalTheory.LevZero.exists_red_iff_isPat (G j) (pl j).1 (hG.idem j).1 _).2
      (isPat_elem a b hab (Or.inl ⟨by simp only [a]; omega, by simp only [b]; omega, by simp [a, b]⟩) _)
  have hmem : g z ∈ (_root_.GlobalTheory.Fam.complexLevelStructure W).H := (hG.lev (g z)).1.2 hex
  choose x hx using hex
  have hchi := (hG.lev (g z)).2 hmem x hx
  have hlam : ∀ j, (((G j).S.P.lam (x j) : ℂˣ) : ℂ) = (G j).S.ψ ((((G j).S.ϖ⁻¹ : (G j).kˣ) : (G j).k) *
      (ofSplit (G j).q).pr ((if pl j = PP then z else 0 : 𝓞 D.host.E) : D.host.E)) := fun j =>
    GlobalTheory.LevZero.lam_eq_of_red (G j) (pl j).1 (hG.idem j).1 (x j) _ (hx j) _
      (edgeSum_elem a b hab ⟨rfl, by simp only [a]; omega⟩ _).symm
  simp only [dif_pos hmem]
  rw [hchi, Units.coe_prod, Finset.prod_eq_single i (fun j _ hj => ?_) (by simp), hlam, if_pos hi]
  rw [hlam, if_neg (fun e => hj (pl.injective (e.trans hi.symm)))]
  simp [Place.pr]
set_option maxHeartbeats 1000000 in
theorem base_inv_alt_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hG : _root_.GlobalTheory.Fam.LocalGroupReading f G pl)
    (hB : _root_.GlobalTheory.MiTop.LocalBottomCompatibility f B v o G) (i : Fin n) : ∃ j₀ : Fin (Yc D 0).rank, j₀.val = D.R.k + D.R.rS ∧ ∀ r,
      toEAf D (G i).q.e * (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *ᵥ
        (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
          (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))) r =
      toEAf D ((G i).q.sec (((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k)) ^ (D.R.rS + 1))) * ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r j₀ := by
  have hs := (G i).hs
  have hodd := (G i).S.odd
  have hρ : D.R.rS = (G i).S.ρ := by unfold Ranks.rS; omega
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by omega
  have he := (hG.idem i).1
  obtain ⟨μ, lam, hμ, hv, hτ⟩ := hB.norm
  have hsc := sc_mul_mu (G i) μ lam hμ o.ζ₀ hτ (hB.last i)
  obtain ⟨e, hord, hM⟩ := hG.frame i 0 ((G i).s + 1) (Nat.zero_add _)
  let p : Fin ((G i).s + 1) := ⟨D.R.rS, by omega⟩
  refine ⟨e (.inl (.inr p)), hord _, fun r => ?_⟩
  refine e_mul_of_prF (G i).q he _ _ _ ?_
  refine map_inv_mulVec ((G i).q.prF he) _ _ (fun r => ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r (e (.inl (.inr p)))) _ (fun r => ?_) r
  choose lf hlf using fun x : Formalism.IndefR.Datum.EAf D => GlobalTheory.ResLoc.toEAf_surj x
  have h1 := congrFun (congrFun (hM (((_root_.GlobalTheory.Fam.pk_z W).βY 0).val.map lf) (Matrix.ext fun a b => hlf _)) r) (e (.inl (.inr p)))
  have h2 : (G i).q.prF he (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0)).val *ᵥ
      fun r => ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r (e (.inl (.inr p)))) r) =
      (ofSplit (G i).q).π ((Formalism.L2.Theta.mt (Yc D 0) (f.g.b 0) * ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val.map lf) r (e (.inl (.inr p)))) := by
    rw [Matrix.mul_apply, map_sum, mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hlf (((_root_.GlobalTheory.Fam.pk_z W).βY 0).val a _)]
    exact (congrArg ((G i).q.prF he) ((toEAf D).map_mul _ _).symm).trans ((G i).q.prF_toEAf he _)
  have h3 : (ofSplit (G i).q).π ((Formalism.L2.Theta.mt (Yc D 0) (f.g.b 0) * ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val.map lf) r (e (.inl (.inr p)))) =
      ((G i).FY 0 ((G i).s + 1) (Nat.zero_add _)).β r (.inr p) * ((G i).S.ϖ : (G i).k) ^ (D.R.rS + 1) := by
    refine h1.trans ?_
    rw [submatrix_apply, Equiv.symm_apply_apply, GlobalTheory.LevZeroUp.bas_val, mul_diagonal]
    rw [GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block (Fin D.R.k) (Fin D.R.t) (l := (G i).s + 1) 0 ((G i).s + 1) (Nat.zero_add _) p]
    rfl
  have h4 := ((G i).bes 0 D.R.rS h₀ ((G i).s + 1) (Nat.zero_add _)).2.2.2.1 p rfl r
  have h5 : B.d.i₀ *ᵥ vecB B.o B.ζ = (f.c.B 0 D.R.rS h₀).d.i₀ *ᵥ vecB (f.c.B 0 D.R.rS h₀).o (f.c.B 0 D.R.rS h₀).ζ :=
    eq_of_heq (congr_arg_heq (fun B' : BesLev D D.R.rS => B'.d.i₀ *ᵥ vecB B'.o B'.ζ) (hB.lev h₀))
  rw [← h5, hv r] at h4
  have h6 : (G i).q.prF he (algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
      (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) =
      (ofSplit (G i).q).pr (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) :=
    (G i).q.prF_toEAf he (incA D _)
  have h7 : ∀ x y, (ofSplit (G i).q).pr (x * y) = (ofSplit (G i).q).pr x * (ofSplit (G i).q).pr y := fun x y =>
    ((G i).q.pr.comp (incA D)).map_mul x y
  rw [h7, ← mul_assoc, hsc, one_mul] at h4
  rw [h6, h2, h3, h4, mul_comm, mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]
theorem inv_mulVec_adelic_embedding_eq_self (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.PackageHypotheses W) {u : D.what₂.Word} (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    (g : GA D (D.sp.X 0)) :
    ((Formalism.IndefR.Lev.finE (D.sp.Y 0) (embA B.d B.o g))⁻¹).val *ᵥ (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
      (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) =
      fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) := by
  have h := GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hW.bot.idE (Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet W.S.X u) (W.S.X.zR u)
    (Or.inr rfl) (embA B.d B.o g)⁻¹ ((B.tieH _).1 ((embA B.d B.o).range.inv_mem ⟨g, rfl⟩))
  funext r
  rw [← map_inv]
  exact ((toEAf D).map_mulVec _ _ r).symm.trans (congrArg (toEAf D) (congrFun h r))
end GlobalTheory.MiTop.MoveZ
open GlobalTheory.MiTop.MoveZ in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.MiTop.base_moves_vector_z_alt_bis : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, ∃ Γ : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D, ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∃ (θ : Formalism.IndefR.Lev.EAf D) (hθ : θ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP ⟨θ, hθ⟩ = 1 ∧ ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) = toEAf D ei • (θ • Γ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr PP hPP
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.MiTop.MoveZ.addChar_uniformizer_eq_chi_of_gRead W ⟨PP, hPP⟩
  by_cases hex : ∃ u, ∃ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B
  swap
  · exact ⟨0, fun u f B h => absurd ⟨u, f, B, h⟩ hex⟩
  obtain ⟨u₀, f₀, B₀, k₀, _, _, _, _, ι₀, v₀, o₀, n₀, G₀, pl₀, -, -, -, -, -, hG₀, hB₀⟩ := hex
  obtain ⟨i₀, hi₀⟩ := pl₀.surjective ⟨PP, hPP⟩
  have he₀ : Formalism.L2.NTheta.IsIdemAt (G₀ i₀).q.e PP := by have := (hG₀.idem i₀).1; rwa [hi₀] at this
  obtain ⟨j₀, hj₀, -⟩ := _root_.GlobalTheory.MiTop.MoveZ.base_inv_alt_alt W f₀ B₀ v₀ o₀ G₀ pl₀ hG₀ hB₀ i₀
  refine ⟨fun r => toEAf D ((G₀ i₀).q.sec (((((G₀ i₀).S.ϖ⁻¹ : (G₀ i₀).kˣ) : (G₀ i₀).k)) ^ (D.R.rS + 1))) *
    ((_root_.GlobalTheory.Fam.pk_z W).βY 0).val r j₀, ?_⟩
  rintro u f B ⟨k, _, _, _, _, ι, v, o, n, G, pl, -, -, -, -, -, hG, hB⟩ a₀ a -
  obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
  have he : Formalism.L2.NTheta.IsIdemAt (G i).q.e PP := by have := (hG.idem i).1; rwa [hi] at this
  have hee : (G₀ i₀).q.e = (G i).q.e := GlobalTheory.LocMod.PinInhab.idem_unique he₀ he
  obtain ⟨j, hj, hz⟩ := _root_.GlobalTheory.MiTop.MoveZ.base_inv_alt_alt W f B v o G pl hG hB i
  obtain rfl : j = j₀ := Fin.ext (hj.trans hj₀.symm)
  have hrat := unif_ratio (G₀ i₀).q (G i).q he₀ hee (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (G₀ i₀).char (G i).char (G₀ i₀).S.cond _ _
    (G₀ i₀).S.unif (G i).S.unif fun z => (hχ u₀ f₀ v₀ n₀ G₀ pl₀ hG₀ i₀ hi₀ z).trans (hχ u f v n G pl hG i hi z).symm
  obtain ⟨θ, hθ, h1, h2⟩ := exists_theta (G₀ i₀).q he₀ _ (pow_sub_one_lt hrat (D.R.rS + 1))
  refine ⟨θ, hθ, h1, fun ei hei => ?_⟩
  obtain rfl : ei = (G i).q.e := GlobalTheory.LocMod.PinInhab.idem_unique hei he
  have h3 : toEAf D ((G i).q.sec (((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k)) ^ (D.R.rS + 1))) = toEAf D (G i).q.e * θ *
      toEAf D ((G₀ i₀).q.sec (((((G₀ i₀).S.ϖ⁻¹ : (G₀ i₀).kˣ) : (G₀ i₀).k)) ^ (D.R.rS + 1))) := by
    rw [← hee, h2, ← RingHom.map_mul, ← sec_mul_sec, ← mul_pow, mul_right_comm, Units.mul_inv, one_mul, ← map_pow, sec_chg]
  have h4 : (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) *
      (show GA D (D.sp.Y 0) from f.g.b 0))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val =
      ((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *
        ((Formalism.IndefR.Lev.finE (Yc D 0) (embA B.d B.o (a₀ * a)))⁻¹).val := by
    have := (Formalism.IndefR.Lev.finE (D.sp.Y 0)).map_mul (embA B.d B.o (a₀ * a)) (f.g.b 0)
    exact congrArg Units.val ((congrArg Inv.inv this).trans (_root_.mul_inv_rev _ _))
  funext r
  rw [h4, ← mulVec_mulVec]
  have h5 := _root_.GlobalTheory.MiTop.MoveZ.inv_mulVec_adelic_embedding_eq_self W hW B (a₀ * a)
  refine Eq.trans ?_ ((hz r).trans ?_)
  · exact congrArg (fun w => toEAf D (G i).q.e * (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *ᵥ w) r) h5
  · rw [h3, mul_assoc, mul_assoc]
    rfl
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_moves_vector_z_alt_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, ∃ Γ : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D, ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∃ (θ : Formalism.IndefR.Lev.EAf D) (hθ : θ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP ⟨θ, hθ⟩ = 1 ∧ ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) = toEAf D ei • (θ • Γ) := by
  atlas_forward_decl _root_.GlobalTheory.MiTop.base_moves_vector_z_alt_bis
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence
open scoped Matrix
end GlobalTheory.CongFlag
namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
end GlobalTheory.CongFlag
namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped Matrix
end GlobalTheory.CongFlag
namespace GlobalTheory.CongFlag
theorem resS_eq_of_flag_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)), κ ∈ rowJ W.S.X W.Q.instEq → ∀ (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, (∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u' (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))))) = toEAf D ei • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))))) → Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  intro D L hT Gi Gl Kc Yd cX ex W hP _ u u' κ hκ c c₂ hc hc₂ PP hPP hEq
  have lev : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hP.bot.hyp.2.2.2.1.lev
  have hPP' : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg := hPP
  have hg := (GlobalTheory.SeeConjRead.places_over_g (_root_.GlobalTheory.Fam.pk_z W) lev).1 PP hPP'
  obtain ⟨ei, hei⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (GlobalTheory.TypePlaces.not_isConjPl _ _ lev.Pg PP hPP' PP hPP')
  obtain ⟨hε, hε1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D ei PP hei
  exact finiteRing_sq_sub_mul_sq_eq_of_card W.S.X W.Q.instEq hP.bot.idE u u' κ hκ c c₂ hc hc₂ PP hg (toEAf D ei) hε hε1 (hEq ei hei)
end GlobalTheory.CongFlag
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_level_integral_twist_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)), κ ∈ rowJ W.S.X W.Q.instEq → ∀ (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, (∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u' (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))))) = toEAf D ei • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))))) → Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  atlas_forward_decl _root_.GlobalTheory.CongFlag.resS_eq_of_flag_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.MiTop
set_option maxHeartbeats 2000000 in
theorem centralRatio_red_eq_one_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, Formalism.L2.DIV.redFn (W.Q.Rl.βY 0) PP (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z)) = 1 := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr u u' f f' B B' hPl hPl' a₀ a a₀' a' hA hA' z hzf hzc k hk heq PP hPP
  classical
  by_cases hS : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z) ∈ Formalism.L2.DIV.St (W.Q.Rl.βY 0)
  swap
  · unfold Formalism.L2.DIV.redFn Formalism.L2.DIV.ext1
    rw [dif_neg hS]
  rcases Nat.eq_zero_or_pos (Yc D 0).rank with h0 | hpos
  · apply Units.ext; ext i; exact absurd i.2 (by omega)
  obtain ⟨c, hc⟩ := GlobalTheory.T.center_adelicUnitaryGroup_finitePart_scalar (Yc D 0) (show GA D (Yc D 0) from z) hzc hzf
  obtain ⟨hci, hfin⟩ := redFn_scalar_eq_one (W.Q.Rl.βY 0) PP _ c hS hc ⟨0, hpos⟩
  apply hfin
  obtain ⟨-, hconj⟩ := hA'.2.2.2
  have hκ : _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k * (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a')⁻¹ ∈ rowJ W.S.X W.Q.instEq := by
    have := ((hconj k).1).1 hk
    simpa using this
  obtain ⟨Γ, hΓ⟩ := _root_.GlobalTheory.T.base_moves_vector_z_alt_alt W hP hr PP hPP
  obtain ⟨θ, hθ, hθ1, hm⟩ := hΓ u f B (by first | exact hPl | exact _root_.GlobalTheory.MiTop.PlacedConditions.placed f B hPl) a₀ a hA
  obtain ⟨θ', hθ', hθ1', hm'⟩ := hΓ u' f' B' (by first | exact hPl' | exact _root_.GlobalTheory.MiTop.PlacedConditions.placed f' B' hPl') a₀' a' hA'
  have hmul : ∀ x y : GA D (D.sp.Y 0), Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (x * y : GA D (D.sp.Y 0))) =
      Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from x) * Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y) :=
    fun x y => map_mul (Formalism.IndefR.Lev.finE (Yc D 0)) x y
  have hinv : ∀ x : GA D (D.sp.Y 0), Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (x⁻¹ : GA D (D.sp.Y 0))) =
      (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from x))⁻¹ :=
    fun x => map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) x
  have ht : ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) a₀ a,
      Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from _root_.GlobalTheory.MiTop.translationElement f B a₀ a) =
        (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u)))⁻¹ *
          Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0)) := by
    intro u f B a₀ a
    unfold _root_.GlobalTheory.MiTop.translationElement
    rw [mul_assoc, hmul, hinv]
  have hT := congrArg (fun g : GA D (D.sp.Y 0) => Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from g)) heq
  simp only [hmul, ht] at hT
  have hcong := _root_.GlobalTheory.T.row_level_integral_twist_alt W hP hr u u' _ hκ (θ * c) θ' (Subring.mul_mem _ hθ hci) hθ' PP hPP (fun ei hei => by
    have key := lattice_ratio_vector_of_scalar_factorisation (toEAf D ei) c θ θ' _ _ _ _ _ _ hc hT _ _ Γ (hm ei hei) (hm' ei hei)
    have hκE : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k * (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a')⁻¹ : GA D (D.sp.Y 0))) =
        Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a') * Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from k) *
          (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a'))⁻¹ :=
      ((map_mul (Formalism.IndefR.Lev.finE (Yc D 0)) _ _).trans (congrArg₂ (· * ·) (map_mul (Formalism.IndefR.Lev.finE (Yc D 0)) _ _)
        (map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) _)))
    rw [ht u' f' B' a₀' a'] at hκE
    rw [← hκE] at key
    exact key)
  have e1 : (⟨θ * c, Subring.mul_mem _ hθ hci⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨θ, hθ⟩ * ⟨c, hci⟩ := rfl
  rw [e1, map_mul, hθ1, hθ1', one_mul] at hcong
  exact hcong
end GlobalTheory.MiTop
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placed_bessel_pair_identity_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, Formalism.L2.DIV.redFn (W.Q.Rl.βY 0) PP (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z)) = 1 := by
  atlas_forward_decl _root_.GlobalTheory.MiTop.centralRatio_red_eq_one_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem mem_rJ_of_red_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (z : GA D (D.sp.Y 0)) (hz : z ∈ GfC (D.sp.Y 0))
    (hS : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z) ∈ Formalism.L2.DIV.St (W.Q.Rl.βY 0))
    (hR : ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg,
      Formalism.L2.DIV.redFn (W.Q.Rl.βY 0) PP (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z)) = 1) :
    z ∈ _root_.GlobalTheory.MiTop.rJ_z W := by
  refine ⟨hz, ?_⟩
  refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA _ _) hS ?_
  rintro PP (hP | hP)
  · exact hR PP hP
  · exact absurd hP (Finset.notMem_empty _)
theorem reduced_character_conj_eq_of_mem_level_group (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {k κ : GA D (D.sp.Y 0)} (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) (hκ : κ ∈ _root_.GlobalTheory.MiTop.rJ_z W) :
    _root_.GlobalTheory.MiTop.realCharacter W (k * κ * k⁻¹) = _root_.GlobalTheory.MiTop.realCharacter W κ := by
  have h1 : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) := hk.2
  have h2 : Formalism.IndefR.Lev.finE (Yc D 0) κ ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) := hκ.2
  have e := levFn_conj D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) h1 h2
  unfold _root_.GlobalTheory.MiTop.realCharacter Formalism.IndefR.Lev.levChi
  erw [map_mul, map_mul, map_inv, e]
theorem mem_rJ_iff_conj_mem (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {k κ : GA D (D.sp.Y 0)} (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) : κ ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ k * κ * k⁻¹ ∈ _root_.GlobalTheory.MiTop.rJ_z W := by
  have := (Subgroup.mul_mem_cancel_right (Formalism.IndefR.Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (y := k * κ) (Subgroup.inv_mem _ hk)).trans
    (Subgroup.mul_mem_cancel_left (Formalism.IndefR.Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (y := κ) hk)
  exact this.symm
theorem matches_mul_of_mem_rJ (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {z t k : GA D (D.sp.Y 0)} (hzf : z ∈ GfC (D.sp.Y 0))
    (hzc : z ∈ Subgroup.center (GA D (D.sp.Y 0))) (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) (ht : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t) :
    Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (z * t * k) := by
  have hkf : k ∈ GfC (D.sp.Y 0) := hk.1
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hzf ht.1) hkf, fun κ => ?_⟩
  have hz := Subgroup.mem_center_iff.mp hzc
  have hc : (z * t * k)⁻¹⁻¹ * κ * (z * t * k)⁻¹ = t⁻¹⁻¹ * (k * κ * k⁻¹) * t⁻¹ := by
    have e : (z * t * k)⁻¹⁻¹ * κ * (z * t * k)⁻¹ = z * (t⁻¹⁻¹ * (k * κ * k⁻¹) * t⁻¹) * z⁻¹ := by group
    rw [e, ← hz, mul_inv_cancel_right]
  obtain ⟨h1, h2⟩ := ht.2 (k * κ * k⁻¹)
  rw [hc]
  refine ⟨(_root_.GlobalTheory.MiTop.mem_rJ_iff_conj_mem W hk).trans h1, fun hκ => ?_⟩
  rw [h2 ((_root_.GlobalTheory.MiTop.mem_rJ_iff_conj_mem W hk).1 hκ), _root_.GlobalTheory.MiTop.reduced_character_conj_eq_of_mem_level_group W hk hκ]
theorem matching_coset_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → GlobalTheory.MiTop.Framed B → GlobalTheory.MiTop.Framed B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∃ a₁, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a₁ ∧ ∃ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a₁ = _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' hF hF' a₀ a a₀' a' hA hA'
  obtain ⟨z, hzf, hzc, c, hcf, hcc, k, hk, he⟩ :=
    _root_.GlobalTheory.T.matching_translates_bottom_alt W hW.bot hr u B (_root_.GlobalTheory.MiTop.translationElement f B a₀ a) hA.2.2.2.1 (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a') hA'.2.2.2.1 hA.2.2.2 hA'.2.2.2
  have hcc' := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hcc)
  have hX : _root_.GlobalTheory.MiTop.translationElement f B a₀ (a * c⁻¹) = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o c⁻¹ *
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * _root_.GlobalTheory.MiTop.translationElement f B a₀ a := by
    unfold _root_.GlobalTheory.MiTop.translationElement
    rw [show a₀ * (a * c⁻¹) = c⁻¹ * (a₀ * a) by rw [← hcc' (a₀ * a), mul_assoc], map_mul]
    have key : ∀ {G : Type} [Group G] (x e y b : G), x⁻¹ * (e * y) * b = x⁻¹ * e * x * (x⁻¹ * y * b) := by
      intros; group
    exact key (G := GA D (D.sp.Y 0)) _ _ _ _
  have e1 : _root_.GlobalTheory.MiTop.translationElement f B a₀ (a * c⁻¹) = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k := by
    rw [hX, he, map_inv]
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
  have hA₁ : _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ (a * c⁻¹) := by
    refine ⟨hA.1, Subgroup.mul_mem _ hA.2.1 (Subgroup.inv_mem _ hcf),
      Subgroup.mul_mem _ hA.2.2.1 (Subgroup.inv_mem _ hcc), ?_⟩
    rw [e1]
    exact _root_.GlobalTheory.MiTop.matches_mul_of_mem_rJ W hzf hzc hk hA'.2.2.2
  have hz : z ∈ _root_.GlobalTheory.MiTop.rJ_z W := _root_.GlobalTheory.MiTop.mem_rJ_of_red_alt W z hzf
    (by first
      | exact _root_.GlobalTheory.T.placed_bessel_pair_relation_alt W hW hr u u' f f' B B' hP hP' hF hF' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1
      | exact _root_.GlobalTheory.T.placed_bessel_pair_relation_alt W hW hr u u' f f' B B' hP hP' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1)
    (by first
      | exact _root_.GlobalTheory.T.placed_bessel_pair_identity_alt W hW hr u u' f f' B B' hP hP' hF hF' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1
      | exact _root_.GlobalTheory.T.placed_bessel_pair_identity_alt W hW hr u u' f f' B B' hP hP' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1)
  refine ⟨a * c⁻¹, hA₁, z * k, Subgroup.mul_mem _ hz hk, ?_⟩
  rw [e1, ← (Subgroup.mem_center_iff.mp hzc (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a')), mul_assoc]
end GlobalTheory.MiTop
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placed_bessel_compatibility_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → GlobalTheory.MiTop.Framed B → GlobalTheory.MiTop.Framed B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∃ a₁, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a₁ ∧ ∃ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a₁ = _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k := by
  atlas_forward_decl _root_.GlobalTheory.MiTop.matching_coset_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
theorem GlobalTheory.MiTop.matches_mul_of_mem_rJ' {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
    {t k : GA D (D.sp.Y 0)} (ht : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t) (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) :
    Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (t * k) := by
  refine ⟨mul_mem ht.1 hk.1, fun j => ?_⟩
  have hc := GlobalTheory.MiTop.conj_in_level (G := GA D (D.sp.Y 0))
    (Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (_root_.GlobalTheory.MiTop.realCharacter W)
    (fun a ha b hb => GlobalTheory.MiTop.levChi_mul_lev _ _ _ ha hb) (fun a => Lev.levChi_ne_zero _ _) hk j
  have h2 := ht.2 (k * j * k⁻¹)
  have e : (t⁻¹)⁻¹ * (k * j * k⁻¹) * t⁻¹ = ((t * k)⁻¹)⁻¹ * j * (t * k)⁻¹ := by group
  rw [e] at h2
  exact ⟨hc.1.trans h2.1, fun hj => (h2.2 (hc.1.1 hj)).trans (hc.2 hj)⟩
theorem GlobalTheory.MiTop.exists_botDat_pin_of_placed_of_framed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → GlobalTheory.MiTop.Framed B → ∃ d : _root_.GlobalTheory.MiTop.BottomData W u, d.B = B ∧ d.b = (show GA D (D.sp.Y 0) from f.g.b 0) ∧ d.Pin z := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr
  classical
  by_cases hex : ∃ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B ∧ Framed B
  · obtain ⟨u₀, f₀, B₀, hpl₀, hF₀⟩ := hex
    obtain ⟨a₀, a, hAt⟩ := _root_.GlobalTheory.T.exists_isAt_of_placed_framed W hP u₀ f₀ B₀ (by first | exact _root_.GlobalTheory.MiTop.PlacedConditions.placed _ _ hpl₀ | exact hpl₀) hF₀
    have hm := _root_.GlobalTheory.MiTop.botHyp_match_alt W hP.bot
    have hS : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (show GA D (D.sp.Y 0) from W.Q.tS) := by
      have h1 := hm.2.2.2.1 1 (one_mem _) (one_mem _)
      rwa [one_mul] at h1
    obtain ⟨z, hzf, hzc, c, hcf, hcc, k₀, hk₀, ht⟩ :=
      _root_.GlobalTheory.T.matching_translates_bottom_alt W hP.bot hr u₀ B₀ _ hAt.2.2.2.1 _ hS.1 hAt.2.2.2 hS
    have ht₀ : _root_.GlobalTheory.MiTop.translationElement f₀ B₀ a₀ (c⁻¹ * a) = z * (show GA D (D.sp.Y 0) from W.Q.tS) * k₀ := by
      have hc : a₀ * (c⁻¹ * a) = c⁻¹ * (a₀ * a) := by
        rw [← mul_assoc, Subgroup.mem_center_iff.1 (inv_mem hcc) a₀, mul_assoc]
      unfold _root_.GlobalTheory.MiTop.translationElement at ht ⊢
      rw [hc, map_mul, map_inv]
      generalize (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u₀) = x at ht ⊢
      generalize embA B₀.d B₀.o (a₀ * a) = p at ht ⊢
      generalize embA B₀.d B₀.o c = q at ht ⊢
      generalize (show GA D (D.sp.Y 0) from f₀.g.b 0) = b at ht ⊢
      generalize (show GA D (D.sp.Y 0) from W.Q.tS) = s at ht ⊢
      calc x⁻¹ * (q⁻¹ * p) * b = x⁻¹ * q⁻¹ * x * (x⁻¹ * p * b) := by group
        _ = z * s * k₀ := by rw [ht]; group
    have hAt₀ : _root_.GlobalTheory.MiTop.IsTranslate' f₀ B₀ a₀ (c⁻¹ * a) := by
      refine ⟨hAt.1, mul_mem (inv_mem hcf) hAt.2.1, mul_mem (inv_mem hcc) hAt.2.2.1, ?_⟩
      rw [ht₀]
      exact _root_.GlobalTheory.MiTop.matches_mul_of_mem_rJ' W (hm.2.2.2.1 z hzf hzc) hk₀
    refine ⟨z, hzf, hzc, fun u f B hpl hF => ?_⟩
    obtain ⟨b₀, b, hAt'⟩ := _root_.GlobalTheory.T.exists_isAt_of_placed_framed W hP u f B (by first | exact _root_.GlobalTheory.MiTop.PlacedConditions.placed _ _ hpl | exact hpl) hF
    obtain ⟨a₁, hAt1, k, hk, hkt⟩ := _root_.GlobalTheory.T.placed_bessel_compatibility_alt W hP hr u u₀ f f₀ B B₀ hpl hpl₀ hF hF₀ b₀ b a₀ _ hAt' hAt₀
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hBT, _⟩ := hpl
    refine ⟨⟨B, (show GA D (D.sp.Y 0) from f.g.b 0), b₀, a₁, k₀ * k⟩, rfl, rfl,
      ⟨hBT.adapted, hAt1.1, hAt1.2.1, hAt1.2.2.1, ?_, ?_⟩⟩
    · exact (Formalism.IndefR.Lev.levG _ _ _).mul_mem hk₀ hk
    · have e := hkt
      rw [ht₀] at e
      unfold _root_.GlobalTheory.MiTop.translationElement at e
      show embA B.d B.o (b₀ * a₁) * (show GA D (D.sp.Y 0) from f.g.b 0) =
        (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * (z * (show GA D (D.sp.Y 0) from W.Q.tS) * (k₀ * k))
      have e' : ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ *
          (embA B.d B.o (b₀ * a₁) * (show GA D (D.sp.Y 0) from f.g.b 0)) =
          z * (show GA D (D.sp.Y 0) from W.Q.tS) * k₀ * k := by
        rw [← mul_assoc]; exact e
      rw [← mul_assoc (z * _) k₀ k, ← e', mul_inv_cancel_left]
  · exact ⟨1, one_mem _, one_mem _, fun u f B hpl hF => (hex ⟨u, f, B, hpl, hF⟩).elim⟩
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_botDat_of_placedP_framed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → GlobalTheory.MiTop.Framed B → ∃ d : _root_.GlobalTheory.MiTop.BottomData W u, d.B = B ∧ d.b = (show GA D (D.sp.Y 0) from f.g.b 0) ∧ d.Pin z := by
  atlas_forward_decl _root_.GlobalTheory.MiTop.exists_botDat_pin_of_placed_of_framed
end
end
