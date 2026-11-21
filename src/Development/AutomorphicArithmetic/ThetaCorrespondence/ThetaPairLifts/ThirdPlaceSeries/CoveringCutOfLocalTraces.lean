import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringCutOfLocalTraces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupIdempotentCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupIdempotentCoefficients
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowInnerProductInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowInnerProductInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowRepresentationPreservesLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowRepresentationPreservesLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGroupOrderBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGroupOrderBound

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
noncomputable section
namespace GlobalTheory.TieIdem
end GlobalTheory.TieIdem
namespace GlobalTheory.TieIdem
theorem tied_good_idem_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    (∀ k : p.P.Gp, ∑ g, (idemOf p.P.A3.A.X).coeff g * (idemOf p.P.A3.A.X).coeff (g⁻¹ * k) = (idemOf p.P.A3.A.X).coeff k) ∧
    (∀ g h : p.P.Gp, (idemOf p.P.A3.A.X).coeff (h * g * h⁻¹) = (idemOf p.P.A3.A.X).coeff g) ∧
    (∀ g : p.P.Gp, IsIntegral ℤ ((Fintype.card p.P.Gp : D.what₂.LL) * (idemOf p.P.A3.A.X).coeff g)) ∧
    ∀ (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp), σ ((idemOf p.P.A3.A.X).coeff g⁻¹) = starRingEnd ℂ (σ ((idemOf p.P.A3.A.X).coeff g)) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p hr _
  exact idemOf_props p.P.A3.A.X hr.ok.ok2.irr
end GlobalTheory.TieIdem
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_idempotent_coefficients_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    (∀ k : p.P.Gp, ∑ g, (idemOf p.P.A3.A.X).coeff g * (idemOf p.P.A3.A.X).coeff (g⁻¹ * k) = (idemOf p.P.A3.A.X).coeff k) ∧
    (∀ g h : p.P.Gp, (idemOf p.P.A3.A.X).coeff (h * g * h⁻¹) = (idemOf p.P.A3.A.X).coeff g) ∧
    (∀ g : p.P.Gp, IsIntegral ℤ ((Fintype.card p.P.Gp : D.what₂.LL) * (idemOf p.P.A3.A.X).coeff g)) ∧
    ∀ (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp), σ ((idemOf p.P.A3.A.X).coeff g⁻¹) = starRingEnd ℂ (σ ((idemOf p.P.A3.A.X).coeff g)) := by
  atlas_forward_decl _root_.GlobalTheory.TieIdem.tied_good_idem_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
noncomputable section
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem geoUnitary_tied_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp) x y,
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g x))
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g y)) =
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) x)
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) y) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p hp _ i σ g x y
  have hm := p.charW.base.models
  exact GlobalTheory.UnitaryActionTest.geometric_unitary p.R.toRealDat hp.prim.unif hm.HW hm.gW
    (GlobalTheory.UnitaryActionTest.actsUnitarily_of_clauses p.R.toRealDat hm.HE hm.gE hm.ν0 hm.HW hm.gW hm.νW
      p.charW.base.fam.tie hm.cX hm.cV) i _ g x y
end GlobalTheory.CovTop
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_inner_product_invariant_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (g : p.P.Gp) x y,
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g x))
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) ((p.R.toRealDat.FW i).ρ g y)) =
      inner ℂ ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) x)
        ((p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) y) := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.geoUnitary_tied_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TieMK
theorem act_mem_MK_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (g : p.P.Gp) f, f ∈ (p.R.toRealDat.FW i).MK → (p.R.toRealDat.FW i).ρ g f ∈ (p.R.toRealDat.FW i).MK := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p _ _ i g f hf
  exact ((GlobalTheory.RealGeoIn.mkStable_of_rhoGeo p.fw p.pins p.rhoGeo i) g f).2 hf
end GlobalTheory.TieMK
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rho_mem_MK_of_mem_MK : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (g : p.P.Gp) f, f ∈ (p.R.toRealDat.FW i).MK → (p.R.toRealDat.FW i).ρ g f ∈ (p.R.toRealDat.FW i).MK := by
  atlas_forward_decl _root_.GlobalTheory.TieMK.act_mem_MK_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
noncomputable section
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem two_log_card_levels_le_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ PP A : ℝ, GlobalTheory.CovTop.HostNum D L PP A 3 → 2 * Real.log (Fintype.card p.P.Gp : ℕ) ≤ L.sc.b := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p _ _ PP A hN
  have hq : ∀ k, D.host.g k ≠ 0 := by
    intro k h0
    have h := hN.cop
    fin_cases k <;> simp_all [Nat.Coprime]
  have hcard : Nat.card p.P.Gp =
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), Nat.card (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
    rw [Nat.card_congr (p.R.eG.trans p.cG).toEquiv]
    exact Nat.card_pi
  have hleN : Fintype.card p.P.Gp ≤
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), D.host.g kv.1 ^ (D.R.r * D.R.r) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun kv _ => card_GL_zmod_le _ _ (hq kv.1))
  have hpos : (0 : ℝ) < (Fintype.card p.P.Gp : ℝ) := by exact_mod_cast Fintype.card_pos
  have hleR : (Fintype.card p.P.Gp : ℝ) ≤
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℝ) ^ (D.R.r * D.R.r)) := by
    exact_mod_cast hleN
  have hlog : Real.log (Fintype.card p.P.Gp : ℝ) ≤
      (2 * D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by
    refine (Real.log_le_log hpos hleR).trans ?_
    rw [Real.log_prod (fun kv _ => pow_ne_zero _ (by exact_mod_cast hq kv.1))]
    calc ∑ kv : (Σ k : Fin 2, D.nd.PlG k), Real.log ((D.host.g kv.1 : ℝ) ^ (D.R.r * D.R.r))
        ≤ ∑ _kv : (Σ k : Fin 2, D.nd.PlG k), ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by
          refine Finset.sum_le_sum fun kv _ => ?_
          rw [Real.log_pow]
          push_cast
          exact mul_le_mul_of_nonneg_left (hN.logg kv.1) (by positivity)
      _ = (2 * D.R.f : ℝ) * ((D.R.r : ℝ) * D.R.r) * (9 * L.sc.L + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_sigma]
          simp [D.nd.card_PlG, nsmul_eq_mul]
          ring
  obtain ⟨-, hL10, hLx, -⟩ := hN.big
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
  obtain ⟨-, -, hpoly⟩ := hN.poly
  have hroom := hN.room
  have hx0 : 0 < L.sc.x := by linarith
  have hX0 : 0 < L.sc.x ^ A := Real.rpow_pos_of_pos hx0 A
  have h3 : (L.sc.x ^ A) ^ (3 : ℝ) = (L.sc.x ^ A) ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3] at hroom
  have hrn : (D.R.r : ℝ) ≤ D.R.nV := by
    have : D.R.r ≤ D.R.nV := by unfold Formalism.BasicNotions.Ranks.nV; omega
    exact_mod_cast this
  set X := L.sc.x ^ A with hX
  set f : ℝ := (D.R.f : ℝ)
  set r : ℝ := (D.R.r : ℝ)
  set Lr := L.sc.L
  have hr0 : 0 ≤ r := by positivity
  have hY : f * r * r * Lr ≤ X := by
    refine le_trans ?_ hpoly
    have : f * r * r * Lr = (f * r) * Lr * r := by ring
    have : f * r * (D.R.nV : ℝ) * Lr = (f * r) * Lr * D.R.nV := by ring
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ f) hr0) (by linarith : (0:ℝ) ≤ Lr)]
  have key : 2 * ((2 * f) * (r * r) * (9 * Lr + 1)) ≤ L.sc.b := by
    rcases Nat.eq_zero_or_pos D.R.r with h0 | h1
    · have : r = 0 := by simp [r, h0]
      rw [this]; nlinarith [pow_pos hX0 3]
    · have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr h1
      have hY80 : 80 ≤ f * r * r * Lr := by
        have : (1:ℝ) ≤ r * r := by nlinarith
        have : (80:ℝ) ≤ f * Lr := by nlinarith
        nlinarith
      have hX80 : 80 ≤ X := le_trans hY80 hY
      have hA : 2 * ((2 * f) * (r * r) * (9 * Lr + 1)) ≤ 40 * (f * r * r * Lr) := by
        have : 0 ≤ f * r * r := by positivity
        nlinarith
      have hB : 40 * X ≤ X ^ 3 := by
        have hXX : 40 ≤ X * X := by nlinarith
        calc 40 * X ≤ X * X * X := by nlinarith
          _ = X ^ 3 := by ring
      nlinarith
  nlinarith [hlog]
end GlobalTheory.CovTop
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_log_card_Gp_le_b : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → GlobalTheory.CovTop.RecTied D L →
    ∀ PP A : ℝ, GlobalTheory.CovTop.HostNum D L PP A 3 → 2 * Real.log (Fintype.card p.P.Gp : ℕ) ≤ L.sc.b := by
  atlas_forward_decl _root_.GlobalTheory.CovTop.two_log_card_levels_le_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem cutAt_of_rows_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hp : p.PointConditions') (ht : RecTied D L) (i : Fin D.R.m) (PP A : ℝ) (hN : HostNum D L PP A 3) : CutAt p i := by
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.T.group_idempotent_coefficients_alt p hp ht
  have hI := GlobalTheory.T.twistedProjector_idempotent_of_groupAlgebra_idem (p.R.toRealDat.FW i) (fun g => (idemOf p.P.A3.A.X).coeff g) h1
  refine ⟨hI, fun σ x y => ?_, fun x hx => ?_, _root_.GlobalTheory.T.two_mul_log_card_Gp_le_b p hp ht PP A hN⟩
  · exact GlobalTheory.T.twistedProjector_orthogonal_of_unitary_action (p.R.toRealDat.FW i) (fun g => (idemOf p.P.A3.A.X).coeff g) _ hI (_root_.GlobalTheory.T.row_inner_product_invariant_alt p hp ht i σ)
      (fun g => h4 _ g) x y
  · exact GlobalTheory.T.card_smul_twistedProjector_mem_integralForms (p.R.toRealDat.FW i) (fun g => (idemOf p.P.A3.A.X).coeff g) h2 h3 (_root_.GlobalTheory.T.rho_mem_MK_of_mem_MK p hp ht i) _ _ x hx
end GlobalTheory.CovTop
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem covering_cut_of_local_traces_alt (_h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : _root_.GlobalTheory.CovTop.LiftTruncation := by
  refine (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 3).imp fun Fm CH _ h => ?_
  obtain ⟨C, -, x0, hx⟩ := h
  exact ⟨0, le_rfl, x0, fun x hx' hle ι p hp i => _root_.GlobalTheory.CovTop.cutAt_of_rows_alt p hp.1 hp.2 i _ _ (hx x hx' hle ι p hp i)⟩
end GlobalTheory.CovTop
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftTruncation_of_prints : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.LiftTruncation := by
  first | exact @_root_.GlobalTheory.CovTop.covering_cut_of_local_traces_alt | exact _root_.GlobalTheory.CovTop.covering_cut_of_local_traces_alt | (intros; apply _root_.GlobalTheory.CovTop.covering_cut_of_local_traces_alt <;> assumption)
end
end
end
