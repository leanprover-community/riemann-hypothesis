import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HostTieTrueCols
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeightTieTrueCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormParametersEqNatStepGap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharTieTrueCols
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnalyticTiesTrueCols
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColRows

theorem hostTie_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.HostTie (ofRecord (I.rec7 l Z) L Del h0) t.seam t.Pr := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W Del h0 hS
  obtain ⟨hX, hseam, hPr, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hS
  cases t
  dsimp only at *
  subst hX
  obtain rfl := eq_of_heq hPr
  obtain rfl := eq_of_heq hseam
  exact GlobalTheory.CoreHt.host_tie_trueCols I hOk l Z L

end GlobalTheory.ColRows

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.HostTie (ofRecord (I.rec7 l Z) L Del h0) t.seam t.Pr := by
  atlas_forward_decl GlobalTheory.ColRows.hostTie_stdKer
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)

noncomputable section

namespace GlobalTheory.ColRows

set_option maxHeartbeats 1000000 in

theorem weightTie_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∃ pl : RPl (I.rec7 l Z).R ≃ t.X.Tau, ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (ofRecord (I.rec7 l Z) L Del h0) W pl (t.word u) (letterOf (I.rec7 l Z) L Del h0 u) := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta
  obtain ⟨hX, -, hPr, -, -, -, hword, -, -, -, -, -, -, -, -⟩ := hS
  cases t
  subst hX
  cases hPr
  cases hword
  cases hW
  have hN := GlobalTheory.T.columnNormParameters_eq_natStepGap (I.rec7 l Z) L Del h0 hDel hEta
  refine ⟨plRec (I.rec7 l Z), fun u => ?_⟩
  have key := GlobalTheory.CoreHt.weightTie_trueCols I hOk l Z L ⟨Del, hDel⟩ u
  have gen : ∀ N : NumDatum, numDatumOfParameters (I.rec7 l Z) L = N → ∀ (W' : Wts B.fields (B.primes X).Word N.R), HEq B.wts W' →
      ∀ (pl' : RPl N.R ≃ B.fields.Tau), HEq (plRec (I.rec7 l Z)) pl' → ∀ δ : Code N, HEq (codeRec L u) δ →
      GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie N (X := B.fields) (Pr := B.primes X) W' pl' u δ := by
    intro N hN W' hW' pl' hpl δ hδ
    subst hN
    cases hW'
    cases hpl
    cases hδ
    exact key
  exact gen _ hN _ HEq.rfl _ HEq.rfl _ HEq.rfl

end GlobalTheory.ColRows

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∃ pl : RPl (I.rec7 l Z).R ≃ t.X.Tau, ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.WeightTie (ofRecord (I.rec7 l Z) L Del h0) W pl (t.word u) (letterOf (I.rec7 l Z) L Del h0 u) := by
  atlas_forward_decl GlobalTheory.ColRows.weightTie_of_stdKer
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColRows

theorem charTie_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.CharTie (ofRecord (I.rec7 l Z) L Del h0) t.seam W t.Ch t.glob t.sel := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW
  obtain ⟨hX, hseam, hPr, hCh, hsel, -, -, -, -, -, -, hglob, -, -, -⟩ := hS
  cases t
  dsimp only at *
  subst hX
  obtain rfl := eq_of_heq hPr
  obtain rfl := eq_of_heq hseam
  obtain rfl := eq_of_heq hCh
  rw [eq_of_heq hsel, eq_of_heq hglob, eq_of_heq hW]
  exact GlobalTheory.CoreHt.charTie_trueCols I hOk l Z L

end GlobalTheory.ColRows

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.CharTie (ofRecord (I.rec7 l Z) L Del h0) t.seam W t.Ch t.glob t.sel := by
  atlas_forward_decl GlobalTheory.ColRows.charTie_stdKer
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ColRows.analyticTie_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.AnalyticTie (I.rec7 l Z) t.δ t.χ t.cD ∧ t.tup (I.rec7 l Z).what₂.mu0 = 1 ∧ t.m2 = (I.rec7 l Z).R.m - 2 := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t hJ hS
  obtain ⟨-, -, hDg, -⟩ := GlobalTheory.Core.Ht2.analyticTies_trueCols I hOk (GlobalTheory.Mem.Col2.base_fields_primes_ok B X).1 l Z hJ

  have hcD : t.cD = I.J.cD := (t.O_dgen B.u₀ I.mu0).symm.trans (hS.O.dgen B.u₀ I.mu0)
  refine ⟨⟨t.cc_rec ▸ t.δ_ok, t.χ_ok, hcD ▸ hDg⟩, ?_, hS.m2⟩

  obtain ⟨hX, -, -, -, -, hSS, -, htup, -⟩ := hS
  cases t
  subst hX
  subst hSS
  cases htup
  exact I.trueColumn_tuple_trivial_eq_one
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticCompatibility_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.AnalyticTie (I.rec7 l Z) t.δ t.χ t.cD ∧ t.tup (I.rec7 l Z).what₂.mu0 = 1 ∧ t.m2 = (I.rec7 l Z).R.m - 2 := by
  atlas_forward_decl GlobalTheory.ColRows.analyticTie_of_stdKer
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows.FldDef

theorem sd_of_isSdLat {B : Base} {n : ℕ} {L : Submodule (𝓞 B.host.E) (Fin n → B.host.E)}
    (h : Formalism.L2.Col.IsSdLat (E := B.fields.E) L) : letI := B.host.cmStar; IsSDLat B.host.E n L := by
  letI := B.host.cmStar
  refine ⟨h.1.1, h.1.2, fun y => ?_⟩
  have h2 : y ∈ Formalism.HermitianLatticesTheory.dual (hStd B.fields.E n) L ↔ y ∈ L := by rw [h.2]
  rw [← h2, Formalism.L2.Col.mem_dual]
  refine forall₂_congr fun x _ => ?_
  rw [Submodule.mem_one]
  rfl

theorem sd_stdL (D : D7) (n : ℕ) : StandardLatticesGL3.SD D (Th.stdL D.host n) := by
  exact GlobalTheory.Glob.IntegralWittCoefficients.Model.isSDLat_std _ _

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem chiRec_detId {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)}
    (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl) (n : ℕ) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E))
    (hL : StandardLatticesGL3.SD (I.rec7 l Z) L) :
    TaylorLogMetric.chiRec (I.rec7 l Z) idl (Th.detId B.host (Th.stdL B.host n) L) = I.chi (Th.detId B.host (Th.stdL B.host n) L) := by
  letI := B.host.cmStar
  let S0 : SDLat B.host.E n := ⟨Th.stdL B.host n, sd_stdL (I.rec7 l Z) n⟩
  let L1 : SDLat B.host.E n := ⟨L, hL⟩
  have h2 : idl ((I.rec7 l Z).relDet n S0 L1) = TaylorLogMetric.detId (I.rec7 l Z) S0.1 L1.1 := hidl.2.2.2.2 n S0 L1
  have e : TaylorLogMetric.detId (I.rec7 l Z) S0.1 L1.1 = Th.detId B.host (Th.stdL B.host n) L := rfl
  have hl : TaylorLogMetric.chiRec (I.rec7 l Z) idl (Th.detId B.host (Th.stdL B.host n) L) =
      ((TaylorLogMetric.chiQ (I.rec7 l Z) ((I.rec7 l Z).relDet n S0 L1) : ℂˣ) : ℂ) := by
    rw [← e, ← h2, TaylorLogMetric.chiRec_idl _ _ hidl.1]
  rw [hl]
  obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective ((I.rec7 l Z).relDet n S0 L1)
  rw [← ht]
  have hχ := I.C.isChi
  have hK := (GlobalTheory.Mem.KerDet.kernel_open_and_factor B.R B.host).2.2.2 I.C.chiPsi hχ.triv (fun v y hy _ => hχ.unr v y hy)
    fun v _ => hχ.unr v
  have hr : (QuotientGroup.mk (toDtT B.host I.SQ t) : DtT B.host ⧸ UOT B.host) = relDetT B.host n (Th.stdL B.host n) L := by
    have h1 := toDtTMod_mk B.host I.SQ (t : DtQ B.host I.SQ)
    have h3 := toDtTMod_relDetQ B.host I.SQ n (Th.stdL B.host n) L
    have h6 : (QuotientGroup.mk (t : DtQ B.host I.SQ) : DtQ B.host I.SQ ⧸ UOQ B.host I.SQ) = relDetQ B.host I.SQ n (Th.stdL B.host n) L := ht
    rw [← h1, h6, h3]
  have h5 : ((tildeQ B.host I.SQ I.C.chiPsi t : ℂˣ) : ℂ) = ((tildeD B.host I.C.chiPsi (toDtT B.host I.SQ t) : ℂˣ) : ℂ) := by
    rw [tildeQ_eq_comp B.host I.SQ hK]; rfl
  exact h5.trans (GlobalTheory.Mem.ChiDet.tildeD_eq_chiId B.R B.host I.C.chiPsi hχ n L ⟨hL.1, hL.2.1⟩ _ hr)
end GlobalTheory.ColRows.FldDef

namespace GlobalTheory.ColRows.FldDef
open GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

theorem fieldOfDefinition_congr {B : Base} (J : AmbIn B.host) (χ₁ χ₂ : Submodule (𝓞 B.host.E) B.host.E → ℂ)
    (hχ : ∀ (n : ℕ) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E)), Formalism.L2.Col.IsSdLat (E := B.fields.E) L →
      χ₁ (Th.detId B.host (Th.stdL B.host n) L) = χ₂ (Th.detId B.host (Th.stdL B.host n) L))
    {Pr : Primes B.fields} {R : Ranks} (W : Formalism.L2.Col.Wts B.fields Pr.Word R)
    (sel : HeightOneSpectrum (𝓞 B.fields.F) → HeightOneSpectrum (𝓞 B.fields.E)) {Sg : Set ℕ}
    (mu : Tup B.fields.F B.fields.E B.fields.K Sg) (cst : LocCst B.fields (rowSG Pr sel mu)) (u : Pr.Word) :
    FieldOfDefinition W sel mu cst u (J.amb B χ₁) → FieldOfDefinition W sel mu cst u (J.amb B χ₂) := by
  intro h i hi L L' c x hR e hdeg
  obtain ⟨y, hy⟩ := h i hi L L' c x hR e hdeg
  have hc : Th.chiFac B.host χ₁ (R.N i) (R.N (i + 1)) L L' = Th.chiFac B.host χ₂ (R.N i) (R.N (i + 1)) L L' := by
    unfold Th.chiFac
    rw [hχ _ L hR.1, hχ _ L' hR.2.1]
  have he : (J.amb B χ₁).e (R.N i) (R.N (i + 1)) L L' = (J.amb B χ₂).e (R.N i) (R.N (i + 1)) L L' := by
    funext z
    show Th.chiFac B.host χ₁ _ _ L L' * _ = Th.chiFac B.host χ₂ _ _ L L' * _
    rw [hc]
  have hth : (J.amb B χ₁).thInd (Sall sel mu u) L L' c x = (J.amb B χ₂).thInd (Sall sel mu u) L L' c x := by
    unfold Amb.thInd
    rw [he]
    rfl
  refine ⟨y, hy.trans ?_⟩
  rw [hth]
  show (Th.chiFac B.host χ₁ _ _ L L')⁻¹ * _ = (Th.chiFac B.host χ₂ _ _ L L')⁻¹ * _
  rw [hc]
  rfl
end GlobalTheory.ColRows.FldDef

open GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds in

theorem GlobalTheory.ColRows.fieldOfDefinition_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → ∀ u a, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.FieldOfDefinition W t.sel (t.tup a) (t.cst a) (t.word u) t.amb := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W hJ hS hW u a
  obtain ⟨-, -, -, hFD⟩ := GlobalTheory.Core.Ht2.analyticTies_trueCols I hOk (GlobalTheory.Mem.Col2.base_fields_primes_ok B X).1 l Z hJ
  have hχ : ∀ (n : ℕ) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E)), Formalism.L2.Col.IsSdLat (E := B.fields.E) L →
      I.chi (Th.detId B.host (Th.stdL B.host n) L) = t.χ (Th.detId B.host (Th.stdL B.host n) L) := fun n L hL => by
    have h1 := GlobalTheory.ColRows.FldDef.chiRec_detId I l Z t.idl_ok n L (GlobalTheory.ColRows.FldDef.sd_of_isSdLat hL)
    have h2 := congrFun t.χ_rec (Th.detId B.host (Th.stdL B.host n) L)
    exact h1.symm.trans h2.symm
  have hF : ∀ (u' : (B.primes X).Word) (a' : I.ι), FieldOfDefinition (Pr := B.primes X) B.wts I.sel (I.tup a') (I.cst a') u' (I.J.amb B t.χ) :=
    fun u' a' => by
      have h3 := GlobalTheory.ColRows.FldDef.fieldOfDefinition_congr (R := B.R) I.J I.chi t.χ hχ B.wts I.sel (I.tup a') (I.cst a') u'
      have h4 : FieldOfDefinition (Pr := B.primes X) B.wts I.sel (I.tup a') (I.cst a') u' (I.J.amb B I.chi) := hFD u' a'
      exact h3 h4
  clear hFD hχ
  obtain ⟨hX, -, hPr, -, hsel, hS', hword, htup, hcst, -, -, -, hamb, -, -⟩ := hS
  cases t
  subst hX
  obtain rfl := eq_of_heq hPr
  subst hS'
  obtain rfl := eq_of_heq hsel
  obtain rfl := eq_of_heq htup
  obtain rfl := eq_of_heq hcst
  obtain rfl := eq_of_heq hword
  obtain rfl := eq_of_heq hW
  have hamb' := eq_of_heq hamb
  rw [hamb']
  exact hF u a
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientField_isFieldOfDefinition_chainSteps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → ∀ u a, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.FieldOfDefinition W t.sel (t.tup a) (t.cst a) (t.word u) t.amb := by
  atlas_forward_decl GlobalTheory.ColRows.fieldOfDefinition_of_stdKer
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows

theorem kerTies_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → (t.cst (I.rec7 l Z).what₂.mu0).sharp = true → GlobalTheory.ColRows.KerTies t W Del h0 := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hJ hS hW hDel hEta hSharp
  obtain ⟨hAn, hMu, hM2⟩ := GlobalTheory.T.analyticCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t hJ hS
  exact
    { host := GlobalTheory.T.hostCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS
      wts := GlobalTheory.T.weightCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta
      chr := GlobalTheory.T.characterCompatibility_standardKernelData_trueColumns I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW
      an := hAn
      mu0 := hMu
      sharp := hSharp
      m2 := hM2
      fld := fun u => GlobalTheory.T.coefficientField_isFieldOfDefinition_chainSteps I hOk hP l Z L hT Gi Gl K Y cX ex t W hJ hS hW u _ }

end GlobalTheory.ColRows
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelCompatibilities_standardKernelData_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → (t.cst (I.rec7 l Z).what₂.mu0).sharp = true → GlobalTheory.ColRows.KerTies t W Del h0 := by
  atlas_forward_decl GlobalTheory.ColRows.kerTies_of_stdKer
end
