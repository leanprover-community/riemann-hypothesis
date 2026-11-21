import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PenXiIsLocFac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocXiEqMulMidXi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowChoiceValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowCharacterIdAddQSmulLatticePreservingEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFiniteFamilyStatement

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.PenPsiInv

open GlobalTheory.CongLevel

section Ext

variable {E : Type} [Field E]

theorem resX_extE {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (v : Fin (n + c) → E) :
    resX c (extE c κ v) = κ (resX c v) := by
  rw [extE_apply, map_add, resX_inX]
  abel

theorem atNL_inX {n : ℕ} (c : ℕ) (w : Fin n → E) : atNL E (n + c) n (Loc.inX E n c w) = 0 := by
  unfold atNL
  split_ifs with h
  · rw [LinearMap.proj_apply, inX_apply, dif_neg (lt_irrefl n)]
  · rfl

theorem atNL_extE {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (v : Fin (n + c) → E) :
    atNL E (n + c) n (extE c κ v) = atNL E (n + c) n v := by
  rw [extE_apply, map_add, atNL_inX, add_zero]

theorem joinCol_inFr {n' c' n c : ℕ} (f : Sp E n' ≃ₗ[E] Sp E n') (f' : Sp E n ≃ₗ[E] Sp E n) (x : HomE E n' n)
    (y : Sp E n) :
    joinCol (c' := c') (c := c) (inFr f f' x) (f'.symm y) =
      (extE c f'.symm).toLinearMap ∘ₗ joinCol (c' := c') (c := c) x y ∘ₗ (extE c' f).toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [joinCol, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [extE_inX]
  congr 1
  have h1 : LinearMap.funLeft E E (Fin.castAdd c') (extE c' f v) = f (LinearMap.funLeft E E (Fin.castAdd c') v) :=
    resX_extE c' f v
  rw [h1, atNL_extE, map_add, map_smul]
  rfl

end Ext

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem extE_mem_Jat (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E)))
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w)
    (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    extE (cOf R j) κ ∈ Jat (Pr := Pr) sharp j w := by
  have h := (Subgroup.mem_inf.1
    (GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe (Pr := Pr) sharp j w hw hd 1 (one_mem _) κ hκ hr)).2
  rw [Subgroup.mem_comap, inv_one, map_one] at h
  exact h

theorem lamRow_extE (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E)))
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w)
    (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    lamRow Ch mu sharp j w (extE (cOf R j) κ).toLinearMap = 1 := by
  have hq : ((qOf w : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have e : (extE (cOf R j) κ).toLinearMap = LinearMap.id + ((qOf w : ℕ) : X.E) •
      (((qOf w : ℕ) : X.E)⁻¹ • ((extE (cOf R j) κ).toLinearMap - LinearMap.id)) := by
    rw [smul_inv_smul₀ hq, add_sub_cancel]
  rw [e]
  refine GlobalTheory.LamRowCong.lamRow_one_add_q Ch mu sharp j w hw _ fun v hv => ?_
  unfold lamYat at hv ⊢
  rw [if_pos hw] at hv ⊢
  exact extE_cong w (qOf w) (cOf R j) (fun i => i + 1) hd κ hκ hr v hv

theorem muAt_det_extE (i : ℕ) {n : ℕ} (c : ℕ)
    (hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)))
    (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (hκ : κ ∈ GLint X.E n P.1)
    (hr : ∀ x ∈ stdAt X.E n P.1, redV P.1 (κ x) = redV P.1 x) :
    muAt Ch sel mu cst i P ((LinearEquiv.det (extE c κ) : X.Eˣ) : X.E) = 1 := by
  refine GlobalTheory.TwU.MidIndep.muAt_det_cong Ch sel mu cst i P (n + c) 1 le_rfl _ fun v hv => ?_
  rw [pow_one]
  rw [GlobalTheory.DatumLaw.stdAt_eq] at hv ⊢
  exact extE_cong P.1 (qOf P.1) c 0 hd κ hκ hr v hv

end Main

theorem psiAt_one_inFr : ∀ {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu), P.1 ∈ Pr.vGs → R.m = s + 2 → (∀ a : X.E, Formalism.L2.Col.IntAt P.1 a → Formalism.L2.Col.redP P.1 a = 0 → Formalism.L2.Col.IntAt P.1 (a / (Formalism.L2.Col.qOf P.1 : X.E))) → ∀ (f : Formalism.L2.Col.Sp X.E (R.N s) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N s)) (f' : Formalism.L2.Col.Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N (s + 1))), f ∈ Formalism.L2.Col.GLint X.E (R.N s) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N s) P.1, Formalism.L2.Col.redV P.1 (f x) = Formalism.L2.Col.redV P.1 x) → f' ∈ Formalism.L2.Col.GLint X.E (R.N (s + 1)) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N (s + 1)) P.1, Formalism.L2.Col.redV P.1 (f' x) = Formalism.L2.Col.redV P.1 x) → ∀ (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))), Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 (Formalism.L2.Col.inFr f f' x) (f'.symm y) = Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y := by
  intro X Pr R Ch sel S₀ mu cst s P hP hm hd f f' hf hr hf' hr' x y
  have hi : s + 2 ≤ R.m := hm.ge
  have hg : f'.symm ∈ GLint X.E (R.N (s + 1)) P.1 := inv_mem hf'
  have hgr : ∀ v ∈ stdAt X.E (R.N (s + 1)) P.1, redV P.1 (f'.symm v) = redV P.1 v := fun v hv => by
    have h := hr' _ ((hg v).2 hv)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have h1 := GlobalTheory.DatumLaw.phiAt_target Ch sel mu cst cst.sharp hi P (extE_mem_Jat cst.sharp (s + 1) P.1 hP hd _ hg hgr)
    (joinCol x y ∘ₗ (extE (cOf R s) f).toLinearMap)
  have h2 := GlobalTheory.DatumLaw.phiAt_source Ch sel mu cst cst.sharp hi P (extE_mem_Jat cst.sharp s P.1 hP hd _ hf hr) (joinCol x y)
  rw [muAt_det_extE Ch sel mu cst P s _ hd _ hg hgr, lamRow_extE Ch mu cst.sharp (s + 1) P.1 hP hd _ hg hgr, mul_one, one_mul] at h1
  rw [muAt_det_extE Ch sel mu cst P s _ hd _ hf hr, lamRow_extE Ch mu cst.sharp s P.1 hP hd _ hf hr, mul_one, one_mul] at h2
  unfold PsiAt
  rw [GlobalTheory.SymBridge.PsiStep.omPhi_one_one, GlobalTheory.SymBridge.PsiStep.omPhi_one_one, joinCol_inFr, h1, h2]

end GlobalTheory.PenPsiInv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.penultimateDatum_unchanged_frames_congruent_one : ∀ {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu), P.1 ∈ Pr.vGs → R.m = s + 2 → (∀ a : X.E, Formalism.L2.Col.IntAt P.1 a → Formalism.L2.Col.redP P.1 a = 0 → Formalism.L2.Col.IntAt P.1 (a / (Formalism.L2.Col.qOf P.1 : X.E))) → ∀ (f : Formalism.L2.Col.Sp X.E (R.N s) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N s)) (f' : Formalism.L2.Col.Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N (s + 1))), f ∈ Formalism.L2.Col.GLint X.E (R.N s) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N s) P.1, Formalism.L2.Col.redV P.1 (f x) = Formalism.L2.Col.redV P.1 x) → f' ∈ Formalism.L2.Col.GLint X.E (R.N (s + 1)) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N (s + 1)) P.1, Formalism.L2.Col.redV P.1 (f' x) = Formalism.L2.Col.redV P.1 x) → ∀ (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))), Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 (Formalism.L2.Col.inFr f f' x) (f'.symm y) = Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y := by
  atlas_forward_decl GlobalTheory.PenPsiInv.psiAt_one_inFr
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.Fam.PenLoc

theorem psiAt_one_eq {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ S₁ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀)
    (mu' : Formalism.L2.DIV.Tup X.F X.E X.K S₁) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu))
    (cst' : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu')) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu)
    (P' : Formalism.L2.Col.rowSG Pr sel mu') (hPP : P.1 = P'.1) (hmem : P.1 ∈ Pr.vGs) (hsh : cst.sharp = cst'.sharp)
    (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))) :
    Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y = Formalism.L2.Col.PsiAt Ch sel mu' cst' s P' 1 x y := by
  have hmem' : P'.1 ∈ Pr.vGs := hPP ▸ hmem
  unfold Formalism.L2.Col.PsiAt
  rw [GlobalTheory.SymBridge.PsiStep.omPhi_one_one, GlobalTheory.SymBridge.PsiStep.omPhi_one_one]
  unfold Formalism.L2.Col.PhiAt
  rw [if_pos hmem, if_pos hmem', hsh, hPP]

theorem lastStepPoints_sub_integral_of_uniformiser_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S S' : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
    (h : valuation k (((S'.ϖ⁻¹ : kˣ) : k) - ((S.ϖ⁻¹ : kˣ) : k)) ≤ 1) (r : GlobalTheory.StepData.XIx (Fin κ) t (s + 1)) :
    S.y0 t r - S'.y0 t r ∈ 𝒪[k] := by
  unfold GlobalTheory.SymChain.SymData.y0
  by_cases hr : r = Sum.inl (Sum.inr 0)
  · subst hr
    simp only [Pi.single_eq_same]
    have h3 := neg_mem (show ((S'.ϖ⁻¹ : kˣ) : k) - ((S.ϖ⁻¹ : kˣ) : k) ∈ 𝒪[k] from h)
    rwa [neg_sub] at h3
  · simp [Pi.single_eq_of_ne hr]

theorem pen_match : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (n : Fin a.n) (hj : (a.G n).s + 1 ≤ B.R.m),
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (t : W.P.T) (J : QJ a t), J.Reads →
    ∀ (α : J.Ch (a.G n).s) (γ : J.Ch ((a.G n).s + 1)) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z,
      B.embLL (Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P 1
        (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 (a.G n).s (J.ι _ α)).1.1 P)
          (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.1 P) (GlobalTheory.QTw.homOf I l Z (a.G n).s hj z))
        ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.1 P).symm
          (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2))) = c * GlobalTheory.Fam.PenLoc.penXi a n z := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a hIs hTr row col n hj
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hd := GlobalTheory.TypePrimeUnif.intAt_div_qOf B.fields (B.primes X) (GlobalTheory.Mem.FieldsLaws.fields_ok B) (GlobalTheory.BasePrimes.primes_ok B X).1
  have hR := (hIs.tie row col).2
  have hϖ := GlobalTheory.T.valuation_uniformizer_sub_qOf_lt_of_gRead W hW u a row col hR n
  obtain ⟨S', hSame, hA'⟩ := GlobalTheory.Fam.MidLoc.exists_atType hW a hR n hϖ
  have hA : ∀ t (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → GlobalTheory.SymBridge.AtType I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL P (GlobalTheory.Fam.TopLoc.emb a n) S' :=
    fun t P hP => hA' _ P hP
  obtain ⟨e'₀, he'₀⟩ := GlobalTheory.QTw.exists_xOrd B.R (a.G n).s
  obtain ⟨e₀, he₀⟩ := GlobalTheory.QTw.exists_xOrd B.R ((a.G n).s + 1)
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℂ, C ≠ 0 ∧ ∀ (e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) (a.G n).s ≃ Fin (B.R.N (a.G n).s))
      (e : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))),
      GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e →
      ∀ (t : W.P.T) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 →
      ∀ (x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N (a.G n).s) (B.R.N ((a.G n).s + 1))) (y' : Formalism.L2.Col.Sp B.fields.E (B.R.N ((a.G n).s + 1))),
        (S'.T (Fin B.R.t)).Psi 1 (GlobalTheory.SymBridge.toLoc (GlobalTheory.Fam.TopLoc.emb a n) e e' x₀) (fun r => GlobalTheory.Fam.TopLoc.emb a n (y' (e r))) =
          C * B.embLL (Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) (a.G n).s P 1 x₀ y') := by
    by_cases h0 : ∃ (t : W.P.T) (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1
    · obtain ⟨t₀, P₀, hP₀⟩ := h0
      have hA₀ := hA t₀ P₀ hP₀
      obtain ⟨C, hC0, hC⟩ := GlobalTheory.SymBridge.psiAgree_of_atType _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a.G n).ν (a.G n).unitVol hA₀ e'₀ e₀ he'₀ he₀
      refine ⟨C, hC0, fun e' e he' he t P hP x₀ y' => ?_⟩
      obtain rfl : e' = e'₀ := Equiv.ext fun r => Fin.ext ((he' r).trans (he'₀ r).symm)
      obtain rfl : e = e₀ := Equiv.ext fun r => Fin.ext ((he r).trans (he₀ r).symm)
      rw [hC x₀ y']
      congr 2
      exact psiAt_one_eq I.Ch I.sel _ _ _ _ _ P₀ P (hP₀.trans hP.symm) hA₀.mem (hA₀.sharp.trans (hA t P hP).sharp.symm) x₀ y'
    · exact ⟨1, one_ne_zero, fun _ _ _ _ t P hP => absurd ⟨t, P, hP⟩ h0⟩
  refine ⟨C⁻¹, inv_ne_zero hC0, fun t J hJ α γ P hP z => ?_⟩
  have hAt := hA t P hP
  obtain ⟨hf1, hf2⟩ := GlobalTheory.T.true_geometry_finite_family W hW u a hIs hTr n t J hJ (a.G n).s (by omega) (J.ι _ α) P hP
  obtain ⟨hg1, hg2⟩ := GlobalTheory.T.true_geometry_finite_family W hW u a hIs hTr n t J hJ ((a.G n).s + 1) (by omega) (J.ι _ γ) P hP
  refine (congrArg B.embLL (GlobalTheory.T.penultimateDatum_unchanged_frames_congruent_one I.Ch I.sel _ _ (a.G n).s P hAt.mem hAt.steps (hd P.1 hAt.mem) _ _ hf1 hf2 hg1 hg2 (homOf I l Z _ hj z) (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2))).trans ?_
  rw [eq_inv_mul_iff_mul_eq₀ hC0]
  obtain ⟨e₁, he₁, hβ₁⟩ := (hIs.stdG n).1 (a.G n).s (Nat.le_succ _)
  obtain ⟨e₂, he₂, hβ₂⟩ := (hIs.stdG n).1 ((a.G n).s + 1) le_rfl
  have hr1 : ((I.rec7 l Z).sp.X (a.G n).s).rank = B.R.N (a.G n).s := rankN (I.rec7 l Z) _ (Nat.le_of_succ_le hj)
  have hr2 : ((I.rec7 l Z).sp.X ((a.G n).s + 1)).rank = B.R.N ((a.G n).s + 1) := rankN (I.rec7 l Z) _ hj
  set e' : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) (a.G n).s ≃ Fin (B.R.N (a.G n).s) := e₁.trans (finCongr hr1) with he'd
  set e : GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1)) := e₂.trans (finCongr hr2) with hed
  have ho' : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e' := fun r => he₁ r
  have ho : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e := fun r => he₂ r
  refine Eq.trans (hC e' e ho' ho t P hP (homOf I l Z _ hj z) (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2)).symm ?_
  have hq : ((S'.ϖ : (a.G n).kˣ) : (a.G n).k) = ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k) := by
    rw [hAt.tie.compl.unif, map_natCast]
    exact congrArg (fun Q => ((Formalism.L2.Col.qOf Q : ℕ) : (a.G n).k)) hP
  have hnear : valuation (a.G n).k (((S'.ϖ : (a.G n).kˣ) : (a.G n).k) - (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k)) <
      valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
    rw [hq, Valuation.map_sub_swap]; exact hϖ
  have hinv := GlobalTheory.SymChain.UnifChange.inv_sub_inv_mem (a.G n).S.unif hnear
  have hcos : (fun r => GlobalTheory.Fam.TopLoc.emb a n (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ γ)).1.2 (e r))) -
      S'.y0 (Fin B.R.t) ∈ box (GlobalTheory.StepData.XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1)) (1 : (a.G n).kˣ) := fun r => by
    have h1 := hJ.cosG n γ e ho r
    have h2 := lastStepPoints_sub_integral_of_uniformiser_inv (a.G n).S S' (Fin B.R.t) hinv r
    have h4 := add_mem h1 h2
    rw [sub_add_sub_cancel] at h4
    exact h4
  refine ((GlobalTheory.SymChain.atMostOne_holds (a.G n).k (a.G n).ν (a.G n).unitVol _ _ S' (Fin B.R.t)).2.2.2.1 _ _ hcos).trans ?_
  refine (hSame.2.1 _).trans ?_

  have hb : ∀ {j : ℕ} (hjj : j ≤ (a.G n).s + 1) (hr : ((I.rec7 l Z).sp.X j).rank = B.R.N j) (e₃ : GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin B.R.t) j ≃ Fin ((I.rec7 l Z).sp.X j).rank),
      ((a.G n).FX j hjj).β = (1 : Matrix _ _ (a.G n).k).submatrix id e₃ → ∀ r c,
      ((a.G n).FX j hjj).β r c = GlobalTheory.Fam.TopLoc.emb a n ((LinearEquiv.refl B.fields.E (Formalism.L2.Col.Sp B.fields.E (B.R.N j))) (Pi.single ((e₃.trans (finCongr hr)) c) 1) (finCongr hr r)) := by
    intro j hjj hr e₃ hβ r c
    rw [hβ]
    change (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (a.G n).k) r (e₃ c) = _
    rw [Matrix.one_apply, LinearEquiv.refl_apply, Pi.single_apply]
    show _ = GlobalTheory.Fam.TopLoc.emb a n (if (finCongr hr) r = (finCongr hr) (e₃ c) then 1 else 0)
    by_cases h : r = e₃ c
    · rw [if_pos h, if_pos (by rw [h]), map_one]
    · rw [if_neg h, if_neg (fun h' => h ((finCongr hr).injective h')), map_zero]
  have hfr : GlobalTheory.SymBridge.toLoc (GlobalTheory.Fam.TopLoc.emb a n) e e' (homOf I l Z _ hj z) =
      ((a.G n).FX ((a.G n).s + 1) le_rfl).γ * z.map (ofSplit (a.G n).q).pr * ((a.G n).FX (a.G n).s (Nat.le_succ _)).β := by
    have h5 := GlobalTheory.SeeSaw.StdMatch.mul_toLoc (GlobalTheory.Fam.TopLoc.emb a n) hr1 hr2 (LinearEquiv.refl _ _) (LinearEquiv.refl _ _) e' e _ _
      (hb (Nat.le_succ _) hr1 e₁ hβ₁) (hb le_rfl hr2 e₂ hβ₂) z
    let T : Matrix (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((a.G n).s + 1)) (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) (a.G n).s) (a.G n).k :=
      GlobalTheory.SymBridge.toLoc (GlobalTheory.Fam.TopLoc.emb a n) e e' (homOf I l Z _ hj z)
    have h5' : ((a.G n).FX ((a.G n).s + 1) le_rfl).β * T =
        z.map (ofSplit (a.G n).q).pr * ((a.G n).FX (a.G n).s (Nat.le_succ _)).β := h5
    have h6 : ((a.G n).FX ((a.G n).s + 1) le_rfl).γ * (((a.G n).FX ((a.G n).s + 1) le_rfl).β * T) = T := by
      rw [← Matrix.mul_assoc, Frame.γβ, Matrix.one_mul]
    refine h6.symm.trans ?_
    refine (congrArg _ h5').trans ?_
    exact (Matrix.mul_assoc _ _ _).symm
  unfold penXi
  exact congrArg (fun x => ((a.G n).S.T (Fin B.R.t)).Psi 1 x ((a.G n).S.y0 (Fin B.R.t))) hfr

end GlobalTheory.Fam.PenLoc
end
end
