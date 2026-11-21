import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightAmpleTwistQuotient
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightAmpleTwistQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightSectionsNonvanishingOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightSectionsNonvanishingOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGapStatement

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RelAmpleComp
open GlobalTheory.FlagMod (FlagCover FlagModel)
theorem exists_weight_isAmple_lineBundle_comp : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∃ ρ : AllWt.Weight Dw, ∀ A : LB TF.Y.X, A.IsLB → IsAmpleLB A → ∃ n : ℕ, IsAmpleLB (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)) := by
  intro _ _ E _ _ _ H Dw l Xo c TF Z hF
  refine ⟨fun _ k => if (k : ℕ) < Dw.p then ((k : ℕ) : ℤ) - Dw.p else ((k : ℕ) : ℤ) - Dw.p + 1, ?_⟩
  intro A hA hAmp
  set ρ : AllWt.Weight Dw := fun _ k => if (k : ℕ) < Dw.p then ((k : ℕ) : ℤ) - Dw.p else ((k : ℕ) : ℤ) - Dw.p + 1 with hρ
  let e : Ix Dw → ℤ := fun ix => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ)
  have hex : AllWt.exOf Dw ρ 0 = -e := by
    refine GlobalTheory.FlagMod.exOf_ext rfl (fun τ i hi => ?_) (fun τ i hi => ?_)
    · have hm := GlobalTheory.FlagMod.mult_of_mem (Dw := Dw) τ
      have h2 := i.2
      simp only [hρ, e, Pi.neg_apply, Option.elim]
      rw [if_pos (by omega)]
      omega
    · have hm := GlobalTheory.FlagMod.mult_conj (Dw := Dw) τ
      have h2 := i.2
      simp only [hρ, e, Pi.neg_apply, Option.elim]
      rw [if_neg (by omega)]
      push_cast
      omega
  have : IsProper TF.Y.s := projProper _ _ _ TF.Y.proj
  have : CompactSpace TF.Y.X := QuasiCompact.compactSpace_of_compactSpace TF.Y.s
  have : IsProper TF.X.π := TF.X.proper
  have : CompactSpace TF.X.YY := QuasiCompact.compactSpace_of_compactSpace TF.X.π
  have : QuasiSeparatedSpace TF.X.YY := quasiSeparatedSpace_of_quasiSeparated (TF.X.π ≫ TF.Y.s)
  obtain ⟨-, hPj, -⟩ := GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF
  have : IsProper (str₀ TF.X Z) := GlobalTheory.CommonModel.isProper_of_isProjOver hPj
  have : CompactSpace (Y₀ TF.X Z) := QuasiCompact.compactSpace_of_compactSpace (str₀ TF.X Z)
  have hN : (TF.X.F.LL (AllWt.exOf Dw ρ 0)).IsLB := TF.X.F.isLB_LL _
  have hM : (TF.X.F.LL e).IsLB := TF.X.F.isLB_LL _
  have hsum := GlobalTheory.HSApp.cls_common_add (commonLL TF.X) e (AllWt.exOf Dw ρ 0)
  have h0 := GlobalTheory.HSApp.cls_common_add (commonLL TF.X) (0 : Ix Dw → ℤ) 0
  simp only [add_zero] at h0
  have h3 : e + AllWt.exOf Dw ρ 0 = 0 := by rw [hex]; exact add_neg_cancel e
  rw [h3] at hsum
  have hcls : GlobalTheory.CechPic.cls (TF.X.F.LL e) hM = -GlobalTheory.CechPic.cls (TF.X.F.LL (AllWt.exOf Dw ρ 0)) hN := by
    refine eq_neg_of_add_eq_zero_left ?_
    have h4 : GlobalTheory.CechPic.cls (TF.X.F.LL 0) ((commonLL TF.X).isLB 0) = 0 := by
      have := congrArg (· - GlobalTheory.CechPic.cls (TF.X.F.LL 0) ((commonLL TF.X).isLB 0)) h0
      simpa using this.symm
    exact hsum.symm.trans h4
  obtain ⟨n₀, hn⟩ := GlobalTheory.T.isAmple_pullbackPower_div_of_locally_ample TF.X.π A hAmp (TF.X.F.LL (AllWt.exOf Dw ρ 0)) (TF.X.F.LL e) hN hM hcls
    (fun z => GlobalTheory.T.borelWeil_flagModel_detInverse_isAmple_local TF.flag z)
  have h := (hn n₀ le_rfl).pull_of_isOpenImmersion (inc₀ TF.X Z)
  have hAπ := LB.isLB_pull hA TF.X.π
  have hAg := LB.isLB_pull hA (inc₀ TF.X Z ≫ TF.X.π)
  have hP1 := isLB_lbPow hAπ n₀
  have hP2 := isLB_lbPow hAg n₀
  have hD1 := LB.isLB_div hP1 hN
  have hL0 : (L₀ TF.X Z ρ).IsLB := LB.isLB_pull hN _
  have hD2 := LB.isLB_div hP2 hL0
  refine ⟨n₀, IsAmpleLB.of_lbIso h hD2 ((GlobalTheory.CechPic.cls_eq_iff hD2 (LB.isLB_pull hD1 _)).1 ?_)⟩
  rw [GlobalTheory.CechPic.cls_div hP2 hL0, GlobalTheory.CechPic.cls_lbPow hAg, GlobalTheory.CechPic.cls_pull hA _ hAg,
    GlobalTheory.CechPic.cls_pull hD1 _ _, GlobalTheory.CechPic.cls_div hP1 hN hD1, GlobalTheory.CechPic.cls_lbPow hAπ,
    GlobalTheory.CechPic.cls_pull hA _ hAπ, GlobalTheory.CechPic.pull_comp, map_sub, map_nsmul]
  congr 1
end GlobalTheory.RelAmpleComp
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativelyAmple_comp_of_exists_weight : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∃ ρ : AllWt.Weight Dw, ∀ A : LB TF.Y.X, A.IsLB → IsAmpleLB A → ∃ n : ℕ, IsAmpleLB (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)) := by
  first | exact @_root_.GlobalTheory.RelAmpleComp.exists_weight_isAmple_lineBundle_comp | exact _root_.GlobalTheory.RelAmpleComp.exists_weight_isAmple_lineBundle_comp | (intros; apply _root_.GlobalTheory.RelAmpleComp.exists_weight_isAmple_lineBundle_comp <;> assumption)
end
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HodgeDominates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
theorem exists_weight_hodgeBundle_dominates : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∃ χ : AllWt.Weight Dw, ∀ y ∈ U₀ TF.X Z, ∀ A : LB TF.Y.X, A.IsLB → ∃ (m : ℕ) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) (A.pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), 0 < m ∧ y ∈ nonzeroLocus s := by
  intro hP _ hS hF E _ _ _ H Dw l Xo c TF Z _
  obtain ⟨ω, hω, e, h⟩ := exists_lb_dominates hP.p22 hS hF TF
  refine ⟨FlagMod.mu0 Dw, fun y hy A hA => ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, TF.Y.j w = (inc₀ TF.X Z ≫ TF.X.π) y := hy
  obtain ⟨m, hm, s, hs⟩ := h w A hA
  have hD := LB.isLB_div (isLB_lbPow hω m) hA
  have hL := isLB_L₀ TF.X Z (FlagMod.mu0 Dw)
  have hT := LB.isLB_div (isLB_lbPow hL m) (pull_isLB hA (inc₀ TF.X Z ≫ TF.X.π))
  have e' : cls _ hL = CechPic.pull (inc₀ TF.X Z ≫ TF.X.π) (cls ω hω) := by
    rw [CechPic.pull_comp, ← e]
    exact cls_pull (TF.X.isLB_Llam _) _ _
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hT (pull_isLB hD (inc₀ TF.X Z ≫ TF.X.π))
    ((cls_eq_iff hT (pull_isLB hD _)).1 (by
      rw [cls_div (isLB_lbPow hL m) (pull_isLB hA _), cls_lbPow hL, cls_pull hA, cls_pull hD,
        cls_div (isLB_lbPow hω m) hA, cls_lbPow hω, map_sub, map_nsmul, e'])) (lbSecPull _ s _)
  refine ⟨m, t, hm, ?_⟩
  rw [ht, nonzeroLocus_lbSecPull]
  exact (hw ▸ hs : (inc₀ TF.X Z ≫ TF.X.π) y ∈ nonzeroLocus s)
end GlobalTheory.HodgeDominates
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_dominates_of_large_weight : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∃ χ : AllWt.Weight Dw, ∀ y ∈ U₀ TF.X Z, ∀ A : LB TF.Y.X, A.IsLB → ∃ (m : ℕ) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) (A.pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), 0 < m ∧ y ∈ nonzeroLocus s := by
  first | exact @_root_.GlobalTheory.HodgeDominates.exists_weight_hodgeBundle_dominates | exact _root_.GlobalTheory.HodgeDominates.exists_weight_hodgeBundle_dominates | (intros; apply _root_.GlobalTheory.HodgeDominates.exists_weight_hodgeBundle_dominates <;> assumption)
end
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem hodge_bundle_ample_at_regular_point : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ la : AllWt.Weight Dw, GapGe 1 la → ∀ y ∈ U₀ TF.X Z, ∃ mu : AllWt.Weight Dw, GapGe 0 mu ∧ ∃ m : ℕ, 0 < m ∧ AmpleAt (L₀ TF.X Z (m • la - mu)) y := by
  intro hP hN hS hC E _ _ _ H Dw l Xo c TF Z hF la hla y hy
  obtain ⟨A, hA⟩ := GlobalTheory.exists_isAmpleLB_of_isProjOver TF.Y.proj
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.T.relativelyAmple_comp_of_exists_weight hP hN E H Dw l Xo c TF Z hF
  obtain ⟨n, hn⟩ := hρ A hA.isLB hA
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.T.hodgeBundle_dominates_of_large_weight hP hN hS hC E H Dw l Xo c TF Z hF
  obtain ⟨m, s, -, hs⟩ := hχ y hy (lbPow A n) (isLB_lbPow hA.isLB n)
  obtain ⟨mu, hmu, M, hM, e⟩ := exists_dominant_sub la (m • χ - ρ) hla
  exact ⟨mu, hmu, M, hM, e ▸ AmpleTwist.ampleAt_of_sec E H Dw l Xo c TF Z A hA.isLB ρ χ n m hn y s hs⟩
end GlobalTheory.HSApp
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_bundle_ample_on_regular_locus : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ la : AllWt.Weight Dw, GapGe 1 la → ∀ y ∈ U₀ TF.X Z, ∃ mu : AllWt.Weight Dw, GapGe 0 mu ∧ ∃ m : ℕ, 0 < m ∧ AmpleAt (L₀ TF.X Z (m • la - mu)) y := by
  first | exact @_root_.GlobalTheory.HSApp.hodge_bundle_ample_at_regular_point | exact _root_.GlobalTheory.HSApp.hodge_bundle_ample_at_regular_point | (intros; apply _root_.GlobalTheory.HSApp.hodge_bundle_ample_at_regular_point <;> assumption)
end
end
