import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilUnitaryEntriesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilUnitaryEntries
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelColumnsFromTiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelColumnsFromTies
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesTildeGammaValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesTildeGammaValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins

section
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
open scoped ComplexOrder
namespace GlobalTheory.ColEvNorm
end GlobalTheory.ColEvNorm
namespace GlobalTheory.ColEvNorm
end GlobalTheory.ColEvNorm
theorem GlobalTheory.ColEvNorm.ev_ipAt_le_normAt_sq_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [IsTotallyComplex D.what₂.LL] (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P), _root_.Formalism.L2.DIV.ColumnCharactersCompatible K → K.c.mu P.A3.fam3.base3.μ0 = 1 → ∀ X0, IsFrames (P.A3.side3 P.Ps P.ψs P.Zs) X0 → ∀ v F, ((Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu P.A3.fam3.base3.μ0) K.c.Lv).ipAt (K.c.hP P.A3.fam3.base3.μ0) v ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1 ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV P.A3.fam3.base3.μ0))) X0 v F ^ 2 := by
  intro D L hT Gi Gl Kc Y cX ex _ T P K hpin hmu X0 hX0 v F
  have ht : P.I.tup P.A3.fam3.base3.μ0 = D.what₂.mu0 := P.tied.div.tup.mu0
  have hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu P.A3.fam3.base3.μ0 : Formalism.L2.DIV.Chr K.X.F K.X.E D.what₂.LL) = ∅ := by
    rw [hmu]
    have h : Formalism.L2.DIV.Qprime ((1 : Formalism.L2.DIV.Tup K.X.F K.X.E D.what₂.LL K.c.Sg) : Formalism.L2.DIV.Chr K.X.F K.X.E D.what₂.LL) = ∅ := by
      change Formalism.L2.DIV.Qprime (1 : Formalism.L2.DIV.Chr K.X.F K.X.E D.what₂.LL) = ∅
      ext w
      simp [Formalism.L2.DIV.Qprime, MonoidHom.ker_one]
    unfold Formalism.L2.Col.QE
    split_ifs with hf
    · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
      rfl
    · rfl
  obtain ⟨hM, hev⟩ := hpin.columnEvaluationOk
  obtain ⟨ι, h1, h2⟩ := hev D.u₀
  obtain ⟨F', hm, hres, hι1⟩ := h1 _ ht hQ ((Formalism.L2.DIV.rV0 D P.A3.A P.Ps P.ψs P.A3.fam3.base3.μ0).mulVec F)
  obtain ⟨hm2, hι2⟩ := h2 _ ht hQ F
  have hz := hι1.symm.trans hι2
  have hF := congrArg Subtype.val (GlobalTheory.ColEvNorm.zOfRow_injective _ _ _ _ _ _ _ _ hz)
  rw [← hF]
  exact GlobalTheory.ColEvNorm.ipAt_le_of_ties (Xf := fieldsLL D K.X K.e) K.c.Pr K.c.Rk K.c.W K.c.Ch K.c.sel K.c.hX K.c.Lv K.c.Xg
    K.v0 K.TU K.xiVal K.trIv P.A3 P.Ps P.ψs P.Zs K.c.mu K.c.hP K.gEq hpin.grpTie
    (congrArg Ranks.m K.kerTie.2.1) K.plEq K.i0Eq K.tEq K.famEq K.muTie K.ok1 hpin.psTie.1 hpin.psTie.2
    X0 hX0 v F F' hm hres
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_tilde_gamma_values_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [IsTotallyComplex D.what₂.LL] (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P), _root_.Formalism.L2.DIV.ColumnCharactersCompatible K → K.c.mu P.A3.fam3.base3.μ0 = 1 → ∀ X0, IsFrames (P.A3.side3 P.Ps P.ψs P.Zs) X0 → ∀ v F, ((Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu P.A3.fam3.base3.μ0) K.c.Lv).ipAt (K.c.hP P.A3.fam3.base3.μ0) v ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1 ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV P.A3.fam3.base3.μ0))) X0 v F ^ 2 := by
  atlas_forward_decl _root_.GlobalTheory.ColEvNorm.ev_ipAt_le_normAt_sq_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
open scoped ComplexOrder
namespace GlobalTheory.ColRows
set_option maxHeartbeats 2000000 in
theorem rowsU_of_colPins_alt : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [IsTotallyComplex D.what₂.LL] (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) (W : Formalism.L2.Col.Wts T.ker.X T.ker.Pr.Word D.R) (Del h0 : ℕ), _root_.Formalism.L2.DIV.ColumnCharactersCompatible K → HEq K.c.W W → KerTies T.ker W Del h0 → KerSizes T.ker W Del h0 CY CT → DV.NprimeDef D L → D.NuFull → (∀ u, 0 < (D.div.Nu u).rank) → ∀ (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (cf : ConvFace P.A3.fam3.base3) (Cl CHl : ℝ) (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs K.c.face K.Sp Zsc) cf Cl CHl), Pk.Zs = P.Zs → ∀ (u : D.what₂.Word) (lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 c0 ce Ch Sw C1) (w : (K.c.face Pk.Zs).Mem) (e : (Fin ((K.c.face Pk.Zs).a w) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), HEq w u → C0 ≤ Ch → ∃ (ch : ColChain (K.c.face Pk.Zs) w) (Tc : ChainTie ch (K.c.memQ w)), FirstCols K.c.hE Tc ∧ ∃ (X0 : InfinitePlace D.what₂.LL → Matrix (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) ℂ) (_ : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding) (hn : HtNums (RecNums.ofNum (ofRecord D L Del h0) (Equiv.refl _) (letterOf D L Del h0 u) (D.mem u).A.T L.Nc lam0 c0 ce Ch Sw C1 H) (InfinitePlace D.what₂.LL)) (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun D.what₂.LL (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm)) (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn) (cb : CBData ch.X ch.Kj), (∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v) ∧ (∀ v, IsUnit ((K.c.face Pk.Zs).Xc w v).det) ∧ 0 < (K.c.face Pk.Zs).a w ∧ Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) := by
  intro CY CT hCT
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.memberRows_of_kernelDatum_sizes CY CT hCT
  refine ⟨C0, ?_⟩
  intro D L hT Gi Gl Kc Y cX ex _ T P K W Del h0 hPins hW hKT hKS hN hNu hrk Zsc cf Cl CHl Pk hZs u lam0 c0 ce Ch Sw C1 H w e hwu hCh
  have hmu0 : P.I.tup P.A3.fam3.base3.μ0 = D.what₂.mu0 := P.tied.div.tup.mu0
  have hpos : ∀ v : InfinitePlace D.what₂.LL, (((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding).PosDef :=
    fun v => Formalism.L2.DIV.BlockDat.HV_pos (ℓ := P.A3.fam3.F.lvl P.Ps P.ψs) K.ok1.ok2.conj (K.ok1.ok2.what₂ _) K.ok1.ok2.irr v
  have hlat : Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) :=
    nuLat_comap_isLattice D L hN u ⟨(hNu u).1, (hNu u).2⟩ _ e
  have ha : 0 < (K.c.face Pk.Zs).a w := by
    have h := hrk u
    change 0 < Module.finrank D.what₂.LL (Submodule.span D.what₂.LL ((D.div.Nu u).L : Set (D.div.Nu u).V)) at h
    rw [(hNu u).2, finrank_top, ← e.finrank_eq, Module.finrank_fin_fun] at h
    exact h
  have hev := _root_.GlobalTheory.T.frames_tilde_gamma_values_alt D L hT Gi Gl Kc Y cX ex T P K hPins
  rw [← hZs] at hev
  clear hPins hrk hNu
  obtain ⟨X, e', c, Sp, colTie, kerTie, wTie, lvTie, sgTie, v0, TU, xiVal, trIv, famEq, gEq, plEq, i0Eq, tEq, muTie, ok1⟩ := K
  obtain ⟨toS, ker, crd, crd_gram, crd_lat, ker_sharp, ker_frm⟩ := T
  obtain ⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, kX, seam, seam_ok, kPr, pr_ok, g_rec, kCh, ksel, kS, kword, T_rec, ktup, Q_rec, kcst, kidx, km2, kglob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩ := ker
  obtain ⟨Pr, Rk, W', Ch', sel, Sg, hX, Lv, Xg, m2, Gc, mu, cst, Li, hL, hP, Mem, wd, b, hY, Am, hK, hF, hE, ev⟩ := c
  have hXe : kX = fieldsLL D X e' := kerTie.1
  subst hXe
  have hRk : Rk = D.R := kerTie.2.1
  subst hRk
  have hPr : Pr = kPr := eq_of_heq kerTie.2.2.1
  subst hPr
  have hChE : Ch' = kCh := eq_of_heq kerTie.2.2.2.1
  subst hChE
  have hsel : sel = ksel := eq_of_heq kerTie.2.2.2.2.1
  subst hsel
  have hSg : Sg = kS := eq_of_heq kerTie.2.2.2.2.2.1
  subst hSg
  have hmu : mu = fun t => ktup (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.1
  subst hmu
  have hcst : cst = fun t => kcst (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.2.1
  subst hcst
  have hLi : Li = fun t => kidx (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.2.2.1
  subst hLi
  have hm2 : m2 = km2 := kerTie.2.2.2.2.2.2.2.2.2.1
  subst hm2
  have hGc : Gc = kglob := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.1
  subst hGc
  have hAm : Am = Formalism.L2.Ker.ambOf seam B χ cD := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.2.1
  subst hAm
  have hMem : Mem = D.what₂.Word := kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1
  subst hMem
  have hwd : wd = kword := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.2.2.2
  subst hwd
  have hW' : W' = W := eq_of_heq hW
  subst hW'
  have hLv : Lv = Formalism.L2.Col.rPsymF (R := D.R) Ch' := lvTie
  subst hLv
  have hwu' : w = u := eq_of_heq hwu
  subst hwu'
  have hmuOne : ktup (P.I.tup P.A3.fam3.base3.μ0) = 1 := by rw [hmu0]; exact hKT.mu0
  have hev' := hev hmuOne
  dsimp only at hev'
  have key := hC0 D L hT Gi Gl Kc Y cX ex
    (⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, fieldsLL D X e', seam, seam_ok, Pr, pr_ok, g_rec, Ch',
      sel, Sg, wd, T_rec, ktup, Q_rec, kcst, kidx, m2, Gc, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th,
      unf, ent, ent_lam, kf, kf_un, served⟩ : Formalism.L2.Ker.KerEntTied ex) W' Del h0 hX P.A3.fam3.base3
    (P.A3.side3 P.Ps P.ψs Pk.Zs) Xg P.I.tup hP b hY hK hF hE (ev Pk.Zs) w (Equiv.refl _) L.Nc lam0 c0 ce Ch Sw C1 H hmu0
    hKT hKS hCh hpos hev'
  dsimp only at key ha hlat ⊢
  obtain ⟨⟨ch, Tc, h1, X0, hX0, hn, hop, cb, hcb⟩, hXc⟩ := key
  exact ⟨ch, Tc, h1, X0, hX0, hn, hop, cb, hcb, hXc, ha, hlat⟩
end GlobalTheory.ColRows
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_columns_from_ties_alt : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [IsTotallyComplex D.what₂.LL] (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) (W : Formalism.L2.Col.Wts T.ker.X T.ker.Pr.Word D.R) (Del h0 : ℕ), _root_.Formalism.L2.DIV.ColumnCharactersCompatible K → HEq K.c.W W → KerTies T.ker W Del h0 → KerSizes T.ker W Del h0 CY CT → DV.NprimeDef D L → D.NuFull → (∀ u, 0 < (D.div.Nu u).rank) → ∀ (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (cf : ConvFace P.A3.fam3.base3) (Cl CHl : ℝ) (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs K.c.face K.Sp Zsc) cf Cl CHl), Pk.Zs = P.Zs → ∀ (u : D.what₂.Word) (lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 c0 ce Ch Sw C1) (w : (K.c.face Pk.Zs).Mem) (e : (Fin ((K.c.face Pk.Zs).a w) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), HEq w u → C0 ≤ Ch → ∃ (ch : ColChain (K.c.face Pk.Zs) w) (Tc : ChainTie ch (K.c.memQ w)), FirstCols K.c.hE Tc ∧ ∃ (X0 : InfinitePlace D.what₂.LL → Matrix (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) ℂ) (_ : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding) (hn : HtNums (RecNums.ofNum (ofRecord D L Del h0) (Equiv.refl _) (letterOf D L Del h0 u) (D.mem u).A.T L.Nc lam0 c0 ce Ch Sw C1 H) (InfinitePlace D.what₂.LL)) (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun D.what₂.LL (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm)) (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn) (cb : CBData ch.X ch.Kj), (∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v) ∧ (∀ v, IsUnit ((K.c.face Pk.Zs).Xc w v).det) ∧ 0 < (K.c.face Pk.Zs).a w ∧ Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) := by
  atlas_forward_decl _root_.GlobalTheory.ColRows.rowsU_of_colPins_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.RL.DefSide
def PointEvaluationSide : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  (Formalism.L2.Theta.RealTied D ∧ ∃ C : Formalism.L2.Forms.ColsTiedSym D, ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u)) ∧
  _root_.Formalism.L2.DIV.ColumnCharactersCompatible b.C.toS ∧ ∃ W : Formalism.L2.Col.Wts b.R.T.ker.X b.R.T.ker.Pr.Word D.R, HEq b.C.toS.c.W W ∧
    GlobalTheory.ColRows.KerTies b.R.T.ker W b.DH.1.1 b.DH.1.2 ∧
    ∀ CY CT : ℝ, GlobalTheory.CoreHt.HtRowsS O.L CY → 8 ≤ O.L.sc.X' → 2 ≤ O.L.sc.x → (∀ u, 4 * O.L.sc.a < ((D.mem u).A.T : ℝ)) →
      (∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * O.L.sc.L) →
      GlobalTheory.ColRows.KerSizes b.R.T.ker W b.DH.1.1 b.DH.1.2 CY CT
theorem pointEvaluationSide_of_bWit {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide _ _ c b := by
  have hk := b.C.kerTie
  have e : Formalism.L2.Col.Wts _ b.C.c.Pr.Word b.C.c.Rk = Formalism.L2.Col.Wts b.R.T.ker.X b.R.T.ker.Pr.Word (q.w.D q.Z).R :=
    wts_eq hk.1.symm hk.2.2.1 hk.2.1
  have hW : HEq (cast e b.C.c.W) q.B.wts := (cast_heq e _).trans w.cW.1
  refine ⟨⟨q.x.real, GlobalTheory.T.exists_symmetricColumnForms_stepZeroFiniteCharacter q.w.I q.w.ok q.w.pins q.w.l q.Z⟩, w.colPins, cast e b.C.c.W, (cast_heq e _).symm, ?_, ?_⟩
  · exact GlobalTheory.T.kernelCompatibilities_standardKernelData_trueColumns q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex b.R.T.ker _ _ _ q.x.pin.jets w.recPin.k.std hW
      b.DH.2.1 b.DH.2.2 (b.R.T.ker_sharp _)
  · exact GlobalTheory.ColRows.kerSizes_of_stdKer q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex b.R.T.ker _ _ _ w.recPin.k.std hW
      b.DH.2.1 b.DH.2.2
theorem pointEvaluationSide_of_isLinked {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c)
    (h : _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p K β c b) : _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide _ _ c b := by
  obtain ⟨q, b', ⟨w⟩, e⟩ := h
  exact Eq.mpr (congrArg (fun y : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide y.1 y.2.1 c y.2.2) e) (_root_.GlobalTheory.Fc.RL.DefSide.pointEvaluationSide_of_bWit q b' w)
theorem definiteSideCondition_of_nprimeDef_of_nuFull (CY CT : ℝ) (hCT : 0 ≤ CT) : ∃ C0 : ℝ, ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (C CH : ℝ),
    _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide D O c b → GlobalTheory.CoreHt.HtRowsS O.L CY → 8 ≤ O.L.sc.X' → 2 ≤ O.L.sc.x → (∀ u, 4 * O.L.sc.a < ((D.mem u).A.T : ℝ)) →
      (∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * O.L.sc.L) → DV.NprimeDef D O.L → D.NuFull →
      (∀ u, 0 < (D.div.Nu u).rank) → C0 ≤ c → _root_.GlobalTheory.Fc.DefiniteSideCondition D O c b C CH := by
  obtain ⟨C0, hC0⟩ := _root_.GlobalTheory.T.kernel_columns_from_ties_alt CY CT hCT
  refine ⟨C0, fun D O c b C CH hE h1 h2 h3 h4 h5 hN hF hR hc => ?_⟩
  obtain ⟨-, hpin, W, hW, hT, hS⟩ := hE
  intro hok1 hsep hP hI lam0 c0 ce Sw C1 H NuC I _ hII u
  have hZs : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs = b.P.Zs := (_root_.GlobalTheory.Fc.qRealOfBundle b).zs
  have hS0 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.base.toIndefData b.P.S0 := (_root_.GlobalTheory.Fc.qRealOfBundle b).s0
  have hS1 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.cols.toIndefData b.P.S1 := (_root_.GlobalTheory.Fc.qRealOfBundle b).s1
  have hDc : HEq (b.C.toS.c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs) b.P.Dc :=
    (congr_arg_heq b.C.toS.c.face hZs).trans (heq_of_eq b.C.toS.colTie.1)
  have hw : HEq (I.wU u) u := ((Formalism.L2.DIV.divTieDat3_heq hZs hS0 hS1 hDc hII).2.2 u).trans (b.C.wTie u)
  exact hC0 D O.L _ _ _ _ _ _ O.ex b.R.T b.P b.C.toS W _ _ hpin hW hT (hS CY CT h1 h2 h3 h4 h5) hN hF hR _ _ C CH
    (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI) hZs u lam0 c0 ce c Sw C1 (H u) (I.wU u) (I.eNu u) hw hc
theorem linkedAt_df_of_parameters {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowDefectCondition := by
  refine _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (p := p) (H := Ind.EvWC (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ => True) fun C CH D O c b => _root_.GlobalTheory.Fc.DefiniteSideCondition D O c b C CH)
    ⟨fun _ => _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide, RowE.of_all fun _ _ β c b _ _ h => _root_.GlobalTheory.Fc.RL.DefSide.pointEvaluationSide_of_isLinked β c b h, fun 𝒜 σ s => ?_⟩
  choose c0 hc0 using fun (CY CT : ℝ) => _root_.GlobalTheory.Fc.RL.DefSide.definiteSideCondition_of_nprimeDef_of_nuFull CY (max CT 0) (le_max_right _ _)
  refine (Formalism.MainNotions.DIV.closed_Csz_ge_fn (W3 𝒜) fun l => c0 (l.getD 6 0) (l.getD 13 0)).imp ?_
  intro eps Fm CH _ hC hc _
  have hC' : c0 Fm.CYL Fm.CTu ≤ Fm.Csz := hC
  obtain ⟨κ, -, -, hs⟩ := s Fm (w3_a hc)
  have tie : RealPlaceSecondLayerConditions Fm := ⟨Fm.x1 + 1, fun x hx i => (hs x (by linarith) i).2.1⟩
  obtain ⟨CH', hCh⟩ := hc.2.1
  obtain ⟨⟨a1, hF⟩, ⟨a2, hR⟩⟩ := full_rank Fm CH' tie hc.2.2.1 hCh
  obtain ⟨a3, hz⟩ := GlobalTheory.CoreHt.famRowsSizes Fm hc.2.2.1
  refine ⟨0, le_rfl, fun C _ => ⟨max a1 (max a2 a3), fun x hx h0 i => ?_⟩⟩
  have e1 : a1 ≤ x := le_trans (le_max_left _ _) h0
  have e2 : a2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h0
  have e3 : a3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h0
  obtain ⟨z1, z2, z3, z4, z5⟩ := hz x e3 i ⟨_, (σ Fm (w3_a hc) x hx i).DH.2.1⟩
  exact hc0 Fm.CYL Fm.CTu _ _ _ (σ Fm (w3_a hc) x hx i) C CH (hs x hx i).2 z1 z2 z3 z4 z5 (Fm.nprimeDef x hx i)
    (hF x e1 i) (hR x e2 i) hC'
end GlobalTheory.Fc.RL.DefSide
theorem GlobalTheory.Fc.RL.linkedAt_prmR_df_of_cuspRapidDecay : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowDefectCondition :=
  fun _ _ _ _ _ N S Γ => _root_.GlobalTheory.Fc.RL.DefSide.linkedAt_df_of_parameters (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_unitary_entries' : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowDefectCondition := by
  atlas_forward_decl _root_.GlobalTheory.Fc.RL.linkedAt_prmR_df_of_cuspRapidDecay
end
end
