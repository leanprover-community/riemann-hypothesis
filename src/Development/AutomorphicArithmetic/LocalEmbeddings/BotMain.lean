import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlicesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergStableRelationOfVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerFixedFunctionsProportionalOfSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
import Development.AutomorphicArithmetic.DivisorFrames.ExistsMaxCompactEqFrameGramSplitBasis
import Development.AutomorphicArithmetic.DivisorFrames.LocalCharConductorLeOfHeckeExponent
import Development.AutomorphicArithmetic.DivisorFrames.ExistsScaledStandardPairSectionsOfMaxCompactTran
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawCharacterConductorAtRamifiedPlace
import Development.AutomorphicArithmetic.DivisorFrames.ThetaTransformFockModelEqOfStandardChar
import Development.AutomorphicArithmetic.DivisorFrames.StdSectionFirstEqProdLocal
import Development.AutomorphicArithmetic.DivisorFrames.StdSectionSecondEqProdLocal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.BotMatch

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model SplitsFully Chars HasExp)
open GlobalTheory.TripleDarboux
open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat)

theorem exists_isHerm_lat {D : D7} (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hB : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (hsd : IsSelfDualC S Λ) (s : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D S τ) (s τ)) {p q : ℕ} (hsig : ∀ τ, Formalism.UG.HasSignature (gramAt D S τ) p q) :
    ∃ bas, Spc.IsHerm D.sp.cm.sig B (Spc.mk ((-1 : D.host.E) • S.gram) (conjSub Λ) (fun w => -s (τf w)) bas) q p := by
  have hlat := GlobalTheory.TripleSpaceW.conjSub_isLattice hsd.1
  obtain ⟨bas, hbas⟩ := exists_bas B _ hlat
  have eJ : ∀ w, ((-1 : D.host.E) • S.gram).map (B.emb w).1 = -((gramAt D S (τf w)).map star) := fun w => by
    ext a b; simp [gramAt, hB]
  refine ⟨bas, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => GlobalTheory.TripleSpace.mem_starLat_iff_form S hsd y, fun w => ?_, hbas⟩⟩
  · show star (((-1 : D.host.E) • S.gram) b a) = ((-1 : D.host.E) • S.gram) a b
    simp only [Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, star_one, GlobalTheory.TripleSpace.star_gram]
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((-1 : D.host.E) • S.gram).map (B.emb w).1) _ _
    rw [eJ]
    exact GlobalTheory.TripleSpace.hasSig_neg_of_hasSignature (hasSignature_map_conj (hsig _))
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((-1 : D.host.E) • S.gram).map (B.emb w).1) _
    rw [eJ]
    exact GlobalTheory.TripleSpace.isCartan_neg_conj (hs _)

open scoped ComplexOrder in

theorem exists_isSkew_lat {D : D7} (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hB : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) (X : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E))
    (hA : IsSelfDualC X Λ) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (s : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D X τ) (s τ)) {p q : ℕ} (hsig : ∀ τ, Formalism.UG.HasSignature (gramAt D X τ) p q) :
    ∃ (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (bas : _),
      (∀ y : Fin k → D.host.E, (fun a => y (e.symm a)) ∈ scLat D.host.AA Λ → y ∈ L) ∧
      Spc.IsSkew D.sp.cm.sig B (Spc.mk (D.host.xi0 • (X.gramᵀ).submatrix e e) L
      (fun w => ((s (τf w)).submatrix e e).map conj) bas) p q := by
  let e' : Fin X.rank ⊕ Fin (zeroSp D).rank ≃ Fin k := (Equiv.sumEmpty (Fin X.rank) (Fin 0)).trans e.symm
  have hJ : D.host.xi0 • (X.gramᵀ).submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram X (zeroSp D) e' :=
    congrArg (D.host.xi0 • ·) (blk_empty e _ _).symm
  have hZ := GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D (zeroSp D)
  have hlat := GlobalTheory.SkewLat.isLattice_pairLat GlobalTheory.SkewLat.DualPair.AA_ne hA.1 hZ.1 e'
  obtain ⟨bas, hbas⟩ := exists_bas B _ hlat
  have hsub : Subsingleton (Matrix (Fin (zeroSp D).rank) (Fin (zeroSp D).rank) ℂ) :=
    inferInstanceAs (Subsingleton (Matrix (Fin 0) (Fin 0) ℂ))
  refine ⟨_, bas, fun y hy => ?_, ⟨fun a b => ?_, fun w => ?_, hlat, fun y => ?_, fun w => ?_, hbas⟩⟩
  · refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨hy, ?_⟩
    have : (fun k => y (e' (.inr k))) = 0 := funext fun k => Fin.elim0 k
    rw [this]
    exact zero_mem _
  · show star (D.host.xi0 * X.gram (e a) (e b)) = -(D.host.xi0 * X.gram (e b) (e a))
    rw [star_mul', GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, GlobalTheory.TripleSpace.star_gram, neg_mul]
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (Complex.I • (D.host.xi0 • (X.gramᵀ).submatrix e e).map (B.emb w).1) _ _
    rw [hJ, GlobalTheory.SkewLat.I_smul_skewGram_map _ _ e' (τf w) (B.emb w).1 (hB w)]
    have h0 : Formalism.UG.HasSignature (gramAt D (zeroSp D) (τf w)) 0 0 :=
      ⟨(Equiv.sumEmpty (Fin 0) (Fin 0)).symm, 1, by ext (a | a) <;> exact a.elim0⟩
    exact GlobalTheory.SkewLat.hasSig_blk e' _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (hsig _) h0
  · show y ∈ _ ↔ ∀ x ∈ _, ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E
      (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (D.host.xi0 • (X.gramᵀ).submatrix e e) y x))
    rw [hJ]
    exact GlobalTheory.SkewLat.dual_pairLat (fun c hc => GlobalTheory.SkewLat.star_mem_AA hc) _ _ hA hZ e' y
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • (D.host.xi0 • (X.gramᵀ).submatrix e e).map (B.emb w).1)
      (((s (τf w)).submatrix e e).map conj)
    rw [hJ, GlobalTheory.SkewLat.I_smul_skewGram_map _ _ e' (τf w) (B.emb w).1 (hB w), ← blk_empty e (s (τf w)) 1]
    have h0 : IsCartanInv (gramAt D (zeroSp D) (τf w)) 1 :=
      ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, by
        rw [Subsingleton.elim (gramAt D (zeroSp D) (τf w) * 1) 1]; exact Matrix.PosDef.one⟩
    exact GlobalTheory.SkewLat.isCartan_blk e' _ _ _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (hs _) h0

theorem exists_reading_lat {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X) {α β : (AE D)ˣ →* Circle} (h : IsTriple W W₁ X α β)
    {ωA : WRep W X} {ωB : WRep W₁ X} (hA : IsWeil ψ true W X β (β / α) ωA) (hB : IsWeil ψ false W₁ X α (α / β) ωB)
    {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)} {ΛW₁ : Submodule (𝓞 D.host.E) (Fin W₁.rank → D.host.E)}
    {ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)} (sW : IsSelfDualC (sgn true W) ΛW) (sW₁ : IsSelfDualC W₁ ΛW₁)
    (sX : IsSelfDualC X ΛX) (Pw : Finset (Pl D.host.E))
    (hτ : ∀ v : Pl D.host.F, (∃ w ∈ Pw, w.under (𝓞 D.host.F) = v) → ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∀ w ∈ Pw, w.under (𝓞 D.host.F) = v → GlobalTheory.AdelicU.splitPrime τ = w)
    (hram : ∀ w ∈ Pw, ¬ GlobalTheory.LFun.UnrAt (α / β) w)
    (hunr : ∀ w : Pl D.host.E, (∀ w' ∈ Pw, w'.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) →
      GlobalTheory.LFun.UnrAt α w ∧ GlobalTheory.LFun.UnrAt β w) :
    ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (hr : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β (finCongr h.rank.symm) Bs Γ Xc), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' ∧
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA (finCongr h.rank.symm) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hr.JW)
        (GlobalTheory.TripleRead.toUX X (finCongr h.rank.symm) hr.JX) ∧
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB (finCongr h.rank.symm) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hr.JW₁)
        (GlobalTheory.TripleRead.toUX X (finCongr h.rank.symm) hr.JX) ∧
      Γ.V.L = conjSub ΛW ∧ Γ.V'.L = conjSub ΛW₁ ∧
      (∀ y : Fin (W.rank + W₁.rank) → D.host.E,
        (fun a => y ((finCongr h.rank.symm).symm a)) ∈ scLat D.host.AA ΛX → y ∈ Γ.W.L) ∧
      Xc.T = Bs.P ∧ ∀ w, w ∈ Pw ↔ ∃ v : Bs.P, GlobalTheory.AdelicU.splitPrime (Bs.τ v) = w := by
  classical
  let e : Fin (W.rank + W₁.rank) ≃ Fin X.rank := finCongr h.rank.symm
  choose τf hτf using (GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))
  choose a b ha hb hab using h.gap
  obtain ⟨mα, hα, eα⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp α a ha τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp β b hb τf hτf
  obtain ⟨T, hT1, hT2, hT3⟩ := exists_ram_set h
  have hdiv : ∀ w, GlobalTheory.LFun.UnrAt α w ∧ GlobalTheory.LFun.UnrAt β w → GlobalTheory.LFun.UnrAt (α / β) w := fun w hw => by
    rw [div_eq_mul_inv]; exact hw.1.mul hw.2.inv
  have hTP : ∀ v ∈ T, ∃ w ∈ Pw, w.under (𝓞 D.host.F) = v := fun v hv => by
    by_contra hc
    push Not at hc
    obtain ⟨τ₀⟩ := (hT1 v hv).1
    have hu := GlobalTheory.AdelicU.splitPrime_under τ₀
    exact hT2 _ (hu.symm ▸ hv) (hdiv _ (hunr _ fun w' hw' => hu.symm ▸ hc w' hw'))
  have hPT : ∀ w ∈ Pw, w.under (𝓞 D.host.F) ∈ T := fun w hw => by
    by_contra hc
    exact hram w hw (hdiv w (hT3 w hc))
  choose τP hτP using fun v : T => hτ v.1 (hTP v.1 v.2)
  obtain ⟨v₁, hv₁, hv₁s, ⟨τ₁⟩⟩ := exists_good_place D T
  let Bs : Base D.host.F D.host.E := ⟨ψ, fun w => ⟨_, hτf w⟩, mα, mβ, T, τP, v₁, τ₁⟩
  have hBs : Bs.IsGood D.sp.cm.sig := base_isGood Bs hψ fun v hv => (hT1 v hv).2
  have hemb : ∀ w x, (Bs.emb w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  obtain ⟨p, q, hsig, hn1, hn2⟩ := h.sig
  have hneg : ∀ τ, gramAt D (sgn true W) τ = -gramAt D W τ := fun τ => by ext i j; simp [gramAt, neg_gram]
  obtain ⟨basV, hV⟩ := exists_isHerm_lat Bs τf hemb (sgn true W) ΛW sW (fun τ => sgnM true (A.cart τ))
    (fun τ => isCartanInv_sgn true W τ (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ))
    (fun τ => by rw [hneg]; exact hasSignature_neg (hsig τ).1)
  have eJ : (-1 : D.host.E) • (sgn true W).gram = (1 : D.host.E) • W.gram := by
    rw [neg_gram, neg_smul, one_smul, one_smul, neg_neg]
  have eθ : (fun w => -sgnM true (A.cart (τf w))) = fun w => A.cart (τf w) := funext fun w => neg_neg _
  rw [eJ, eθ] at hV
  obtain ⟨basV', hV'⟩ := exists_isHerm_lat Bs τf hemb W₁ ΛW₁ sW₁ A₁.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A₁)
    fun τ => (hsig τ).2.1
  obtain ⟨LX, basX, hLX, hX⟩ := exists_isSkew_lat Bs τf hemb X ΛX sX e B.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B)
    fun τ => (hsig τ).2.2
  have e3 : X.rank - (p + q) = W.rank + W₁.rank - (p + q) := by rw [h.rank]
  rw [e3] at hX
  obtain ⟨Mo, hMo⟩ := exists_model Bs hBs W _ _ hV hX 1 one_ne_zero rfl
  obtain ⟨Mo', hMo'⟩ := exists_model Bs hBs W₁ _ _ hV' hX (-1) (neg_ne_zero.2 one_ne_zero) rfl
  obtain ⟨om, hom, htr⟩ := exists_weil Bs hBs true W X e _ _ hV hX 1 rfl (by rw [neg_gram, one_smul, neg_neg]) rfl Mo hMo hA
  obtain ⟨om', hom', htr'⟩ := exists_weil Bs hBs false W₁ X e _ _ hV' hX (-1) rfl (neg_one_smul _ _) rfl Mo' hMo' hB
  have hr := h.rank
  have hev := h.even
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  have hTe : (⟨α, β, T, ∅⟩ : Chars D.host.F D.host.E).T = T := by simp [Chars.T]
  refine ⟨Bs, ⟨p, q, _, _, _, Mo, Mo'⟩, ⟨α, β, T, ∅⟩, om, om',
    ⟨rfl, rfl, rfl, rfl, fun w => ⟨τf w, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, ⟨hBs, ?_, ?_, hom, hom'⟩, htr, htr',
    rfl, rfl, hLX, hTe, fun w => ⟨fun hw => ⟨⟨_, hPT w hw⟩, hτP _ w hw rfl⟩, ?_⟩⟩
  · refine ⟨by omega, hr ▸ hev, fun w => ?_, ?_, hn2, hV, hV', hX, hMo, hMo'⟩
    · have h1 := eα w
      have h3 := eβ w
      have h4 := hab (τf w)
      rw [hr] at h4
      have : (((W.rank + W₁.rank : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ) := by
        push_cast at h4 ⊢
        rw [h1, h3]
        linarith
      exact_mod_cast this
    · obtain ⟨m, hm⟩ := hev
      show 2 * (p + q) + 1 < (W.rank - W₁.rank) / 2
      omega
  · refine ⟨h.hecA, h.hecB, GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resA),
      GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resB), hα, hβ, Finset.disjoint_empty_right _,
      hTe.le, fun w hw => hT2 w (hTe ▸ hw), fun w hw => (hT3 w fun h0 => hw ?_).1, fun w hw => (hT3 w fun h0 => hw ?_).2,
      ⟨hTe.symm ▸ hv₁, hv₁s⟩⟩
    · rw [hTe]; exact h0
    · rw [hTe]; exact h0
  · rintro ⟨v, rfl⟩
    obtain ⟨w, hw, hwv⟩ := hTP v.1 v.2
    exact (hτP v w hw hwv).symm ▸ hw

end GlobalTheory.BotMatch

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BotMatch

open GlobalTheory.LatVac (liftV)

variable {D : D7} {S T : HSp D} {n k : ℕ} (m : Matrix (Fin n) (Fin k) (AE D) ≃ₗ[AE D] WO S T) (Λ : AddSubgroup (WO S T))

theorem m_smul (c : AF D.host.F) (u : Matrix (Fin n) (Fin k) (AE D)) : m (c • u) = c • m u := by
  rw [← algebraMap_smul (AE D) c u, map_smul, algebraMap_smul]

theorem isHalf_m {a : AE D} {u : Matrix (Fin n) (Fin k) (AE D)} : IsHalf a (m u) ↔ IsHalf a u := by
  have h1 : IsHalf a (m u) ↔ a • m u = m u := ⟨fun h => Matrix.ext h, fun h p q => congrFun (congrFun h p) q⟩
  have h2 : IsHalf a u ↔ a • u = u := ⟨fun h => Matrix.ext h, fun h p q => congrFun (congrFun h p) q⟩
  rw [h1, h2, ← map_smul, m.injective.eq_iff]

def lattice₂ (v : Pl D.host.F) : AddSubgroup (Matrix (Fin n) (Fin k) (AE D)) where
  carrier := {u | At (evFin D.host.F v) u ∧ m u ∈ Λ}
  zero_mem' := ⟨fun u _ => smul_zero u, by rw [map_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero],
    by rw [map_add]; exact add_mem ha.2 hb.2⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by rw [map_neg]; exact neg_mem ha.2⟩

def genP (v : Pl D.host.F) : Set (Matrix (Fin n) (Fin k) (AE D)) :=
  {γ | (∃ γ' ∈ lattice₂ m Λ v, γ = 2 • γ') ∨ γ ∈ lattice₂ m Λ v ∧ ∃ a, IsSplitIdem D a ∧ IsHalf a γ}

theorem genP_subset (v : Pl D.host.F) : genP m Λ v ⊆ lattice₂ m Λ v := by
  rintro _ (⟨γ, h, rfl⟩ | h)
  exacts [nsmul_mem h 2, h.1]

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

variable (ΛS ΛT) in

abbrev latA : AddSubgroup (WO S T) := latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True

theorem cut_mem (v : Pl D.host.F) {x : WO S T} (hx : x ∈ latA ΛS ΛT) :
    liftV v (1 : Fv D.host.F v) • m.symm x ∈ lattice₂ m (latA ΛS ΛT) v :=
  ⟨GlobalTheory.BigDatLat.at_smul v _, by rw [m_smul, m.apply_symm_apply]; exact GlobalTheory.BigDatLat.smul_mem v hx⟩

theorem localLattice_le_closure_generators (v : Pl D.host.F) : lattice₂ m (latA ΛS ΛT) v ≤ AddSubgroup.closure (genP m (latA ΛS ΛT) v) := by
  intro u hu
  let f : WO S T →+ Matrix (Fin n) (Fin k) (AE D) :=
    (DistribMulAction.toAddMonoidHom _ (liftV v (1 : Fv D.host.F v))).comp m.symm.toLinearMap.toAddMonoidHom
  have hf : ∀ x, f x = liftV v (1 : Fv D.host.F v) • m.symm x := fun _ => rfl
  have e : u = f (m u) := by rw [hf, m.symm_apply_apply, GlobalTheory.BigDatLat.smul_eq_of_at hu.1]
  rw [e]
  refine GlobalTheory.LatVac.le_of_two_of_half ((AddSubgroup.closure (genP m (latA ΛS ΛT) v)).comap f) (fun x hx => ?_)
    (fun a ha x hx hx' => ?_) hu.2
  · rw [AddSubgroup.mem_comap, map_nsmul]
    exact AddSubgroup.subset_closure (Or.inl ⟨_, cut_mem m v hx, rfl⟩)
  · refine AddSubgroup.subset_closure (Or.inr ⟨cut_mem m v hx, a, ha, GlobalTheory.BigDatLat.isHalf_smul _ ?_⟩)
    exact (isHalf_m m (u := m.symm x)).1 (by rwa [m.apply_symm_apply])

theorem mem_localLattice_iff_forall_addChar_eq_one (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (B : Matrix (Fin n) (Fin k) (AE D) → Matrix (Fin n) (Fin k) (AE D) → AF D.host.F)
    (hB : ∀ x y, B x y = symplO S T (m x) (m y)) (v : Pl D.host.F) (z : Matrix (Fin n) (Fin k) (AE D))
    (hz : At (evFin D.host.F v) z) : z ∈ lattice₂ m (latA ΛS ΛT) v ↔ ∀ γ ∈ lattice₂ m (latA ΛS ΛT) v, ψ (B z γ) = 1 := by
  constructor
  · intro h γ hγ
    rw [hB, GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT h.2 hγ.2]
  · intro h
    have hz' : liftV v (1 : Fv D.host.F v) • m z = m z := by rw [← m_smul, GlobalTheory.BigDatLat.smul_eq_of_at hz]
    refine ⟨hz, GlobalTheory.LatVac.mem_of_char hψ hS hT ?_ fun x hx => ?_⟩
    · rw [← hz']
      exact Matrix.ext fun _ _ => GlobalTheory.BigDatLat.infPart_smul v _
    · have := h _ (cut_mem m v hx)
      rwa [hB, m_smul, m.apply_symm_apply, GlobalTheory.BigDatLat.symplO_swap, hz'] at this

theorem hTens_half {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {n d : ℕ}
    (JA : Matrix (Fin n) (Fin n) A) (JB : Matrix (Fin d) (Fin d) A) (a : A) (ha : a * c a = 0)
    (x : Matrix (Fin n) (Fin d) A) (hx : ∀ p q, a * x p q = x p q) : hTens c JA JB x x = 0 := by
  unfold hTens
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun r _ =>
    Finset.sum_eq_zero fun l _ => ?_
  have u := congrArg c (hx r l)
  rw [map_mul] at u
  rw [← u, ← hx p q]
  linear_combination (x p q * JA p r * JB q l * c (x r l)) * ha

variable {Xs : Spc D.host.F D.host.E n} {Ws : Spc D.host.F D.host.E k} (Mo : Model D.sp.cm.sig Xs Ws)

abbrev sy (Xs : Spc D.host.F D.host.E n) (Ws : Spc D.host.F D.host.E k) (u u' : Matrix (Fin n) (Fin k) (AE D)) : AF D.host.F :=
  symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Xs.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) u u'

def thM (ψ : AddChar (AF D.host.F) ℂ) (Φ : (Fin n × Fin k → AF D.host.F) → ℂ) (x : WO S T) : ℂ :=
  thetaSum D.host.F (Mo.co.rho ψ (m.symm x) Φ)

theorem thM_rho (hB : ∀ x y, sy Xs Ws x y = symplO S T (m x) (m y)) (ψ : AddChar (AF D.host.F) ℂ)
    (Φ : (Fin n × Fin k → AF D.host.F) → ℂ) (u : Matrix (Fin n) (Fin k) (AE D)) :
    thM m Mo ψ (Mo.co.rho ψ u Φ) = heisO ψ S T (m u) (thM m Mo ψ Φ) := by
  funext x
  refine ((congrArg (thetaSum D.host.F) (GlobalTheory.BigDat.rho_rho Mo.co ψ (m.symm x) u Φ)).trans tsum_mul_left).trans ?_
  have h := hB (m.symm x) u
  rw [m.apply_symm_apply] at h
  unfold heisO symplOH thM
  rw [map_add, m.symm_apply_apply, ← h, GlobalTheory.BigDat.invOf_two]
  rfl

theorem thM_smul (ψ : AddChar (AF D.host.F) ℂ) (c : ℂ) (Φ : (Fin n × Fin k → AF D.host.F) → ℂ) :
    thM m Mo ψ (c • Φ) = c • thM m Mo ψ Φ :=
  funext fun _ => (tsum_congr fun _ => mul_left_comm _ _ _).trans tsum_mul_left

theorem vac_acts {Bs : Base D.host.F D.host.E} (hBs : Bs.IsGood D.sp.cm.sig) {r s r' s' : ℕ}
    (hX : Xs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s') (hM : Mo.IsGood Bs.ψ) {v : Pl D.host.F}
    (hle : ∀ u ∈ lattice₂ m Λ v, u ∈ latAtV Xs Ws v) :
    ∀ γ ∈ genP m Λ v, Acts (evFin D.host.F v) (Mo.co.rho Bs.ψ γ) (Mo.vac v) (Mo.vac v) := by
  intro γ hγ
  obtain ⟨-, -, θ, -, hθ⟩ := hM.vac v
  have h1 := hθ γ (hle γ (genP_subset m Λ v hγ))
  have h2 : Bs.ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Xs.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) γ γ) = 1 := by
    rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨-, a, ha, hγ⟩
    · exact GlobalTheory.BigDat.VacFix.psi_double _ Bs Xs Ws _ _ _ _ hBs hX hW v θ γ' (hle γ' hγ')
    · unfold symp
      rw [hTens_half (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) _ _ a ha.2.1 γ hγ, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one]
  rw [h2, one_smul] at h1
  exact h1

theorem exists_vac (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {Bs : Base D.host.F D.host.E}
    (hψ : IsStdChar D Bs.ψ (-1)) (hBs : Bs.IsGood D.sp.cm.sig) {r s r' s' : ℕ}
    (hX : Xs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s') (hM : Mo.IsGood Bs.ψ)
    (hB : ∀ x y, sy Xs Ws x y = symplO S T (m x) (m y))
    (hle : ∀ v, ∀ u ∈ lattice₂ m (latA ΛS ΛT) v, u ∈ latAtV Xs Ws v)
    (hinj : ∀ Φ ∈ schA D.host.F _, ∀ Φ' ∈ schA D.host.F _, thM m Mo Bs.ψ Φ = thM m Mo Bs.ψ Φ' → Φ = Φ')
    {Φ : (Fin n × Fin k → AF D.host.F) → ℂ} (hΦ : Φ ∈ schA D.host.F _)
    (hv : IsLatVac (heisO Bs.ψ S T) (latA ΛS ΛT) (thM m Mo Bs.ψ Φ)) :
    ∃ f, Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Mo.vac := by
  have hstd := hBs.std
  refine GlobalTheory.T.adelicSchwartz_eq_pureTensor_of_finite_slices Mo.vac (fun v => (hM.vac v).2.1) hM.std Φ hΦ fun v y hy => ?_
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded Xs Ws v Mo.co hX.lat hW.lat
  obtain ⟨a, ha⟩ := GlobalTheory.T.schroedinger_fixed_functions_proportional_of_selfDual v (GlobalTheory.LatVac.psiAt Bs.ψ v) (GlobalTheory.VacAny.continuous_psiV hstd.1 v)
    (GlobalTheory.PsiNontriv.psiAt_ne_one Bs.ψ hstd v) (GlobalTheory.LatVac.locCo Mo.co v '' genP m (latA ΛS ΛT) v)
    ((lattice₂ m (latA ΛS ΛT) v).map (GlobalTheory.LatVac.locCo Mo.co v)) c
    (by rw [← AddMonoidHom.map_closure]; exact AddSubgroup.map_mono (localLattice_le_closure_generators m v)) hc0
    (GlobalTheory.LatVac.DualLoc.map_selfDual v Mo.co Bs.ψ _ (fun γ hγ => hγ.1) (mem_localLattice_iff_forall_addChar_eq_one m hS hT hψ _ hB v))
    (by rintro _ ⟨γ, hγ, rfl⟩; exact hc γ (hle v γ hγ)) (Mo.vac v)
    (fun ξ => Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)))
    (by
      rintro _ ⟨γ, hγ, rfl⟩
      exact GlobalTheory.BigDat.schr_eq_of_acts _ _ (genP_subset m _ v hγ).1 (hM.vac v).1
        (vac_acts m _ Mo hBs hX hW hM (hle v) γ hγ))
    (by
      rintro _ ⟨γ, hγ, rfl⟩
      refine GlobalTheory.BigDat.schr_slice _ _ (genP_subset m _ v hγ).1
        (hinj _ (GlobalTheory.HeisSchA.rho_mem_schA Mo Bs.ψ hstd γ Φ hΦ) _ hΦ ?_) hy
      rw [thM_rho m Mo hB]
      rcases hγ with ⟨γ', h, rfl⟩ | ⟨h, a, ha, hh⟩
      · rw [map_nsmul]; exact hv.1 _ h.2
      · exact hv.2 a ha _ h.2 ((isHalf_m m).2 hh)) (hM.vac v).2.1
  exact ⟨a, congrFun ha⟩

def halfP (n k : ℕ) (ε : AE D) : AddSubgroup (Matrix (Fin n) (Fin k) (AE D)) where
  carrier := {u | IsHalf ε u}
  zero_mem' := fun _ _ => mul_zero _
  add_mem' := fun {a b} ha hb p q => by rw [Matrix.add_apply, mul_add, ha p q, hb p q]
  neg_mem' := fun {a} ha p q => by rw [Matrix.neg_apply, mul_neg, ha p q]

def graphP (ε : AE D) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) : Submodule ℂ ((WO S T → ℂ) × (WO S T → ℂ)) :=
  Submodule.span ℂ {p | ∃ Φ, IsSBHalf ε Λ Φ ∧ p = (Φ, Tm Φ)}

theorem graphP_snd {ε : AE D} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {p} (hp : p ∈ graphP Λ ε Tm) : p.2 = Tm p.1 := by
  induction hp using Submodule.span_induction with
  | mem p h => obtain ⟨Φ, -, rfl⟩ := h; rfl
  | zero => exact (map_zero Tm).symm
  | add p q _ _ hp hq => rw [Prod.snd_add, Prod.fst_add, map_add, hp, hq]
  | smul c p _ hp => rw [Prod.smul_snd, Prod.smul_fst, map_smul, hp]

theorem mem_graphP_of_intertwines {ε : AE D} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (ψ : AddChar (AF D.host.F) ℂ) (χ : WO S T → ℂ)
    (x y : WO S T) (h : ∀ Φ, IsSBHalf ε Λ Φ → IsSBHalf ε Λ (fun t => χ t * Φ (t + x)) ∧
      Tm (fun t => χ t * Φ (t + x)) = heisO ψ S T y (Tm Φ)) {p} (hp : p ∈ graphP Λ ε Tm) :
    ((fun t => χ t * p.1 (t + x)), heisO ψ S T y p.2) ∈ graphP Λ ε Tm := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨Φ, hΦ, rfl⟩ := hp
    exact Submodule.subset_span ⟨_, (h Φ hΦ).1, by rw [(h Φ hΦ).2]⟩
  | zero =>
    convert (graphP Λ ε Tm).zero_mem using 1
    exact Prod.ext (funext fun _ => mul_zero _) (funext fun _ => mul_zero _)
  | add p q _ _ hp hq =>
    convert (graphP Λ ε Tm).add_mem hp hq using 1
    exact Prod.ext (funext fun _ => mul_add _ _ _) (funext fun _ => mul_add _ _ _)
  | smul c p _ hp =>
    convert (graphP Λ ε Tm).smul_mem c hp using 1
    exact Prod.ext (funext fun _ => mul_left_comm _ _ _) (funext fun _ => mul_left_comm _ _ _)

theorem idem_facts {v : Pl D.host.F} {a : AE D} (ha : IsSplitIdem D a)
    (hsum : a + cA D a = algebraMap (AF D.host.F) (AE D) (liftV v 1)) :
    a * a = a ∧ cA D a * cA D a = cA D a ∧ a * algebraMap (AF D.host.F) (AE D) (liftV v 1) = a ∧
      cA D a * algebraMap (AF D.host.F) (AE D) (liftV v 1) = cA D a ∧ finPart D a ∈ intAE D ∧ finPart D (cA D a) ∈ intAE D ∧
      infPart D a = 0 := by
  obtain ⟨haa, hac, -⟩ := ha
  have hcc : cA D a * cA D a = cA D a := by rw [← map_mul, haa]
  have hca : cA D a * a = 0 := by rw [mul_comm, hac]
  have h1 : a * algebraMap (AF D.host.F) (AE D) (liftV v 1) = a := by rw [← hsum, mul_add, haa, hac, add_zero]
  refine ⟨haa, hcc, h1, by rw [← hsum, mul_add, hca, hcc, zero_add],
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, haa]), GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc]), ?_⟩
  rw [← h1, map_mul, GlobalTheory.BigDat.infPart_algebraMap_liftV, mul_zero]

theorem mem_localLattice_of_forall_addChar_eq_one (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) (hB : ∀ x y, sy Xs Ws x y = symplO S T (m x) (m y)) {v : Pl D.host.F} {a : AE D}
    (ha : IsSplitIdem D a) (hsum : a + cA D a = algebraMap (AF D.host.F) (AE D) (liftV v 1))
    {x : Matrix (Fin n) (Fin k) (AE D)} (hx : IsHalf a x)
    (h : ∀ y ∈ lattice₂ m (latA ΛS ΛT) v, IsHalf (cA D a) y → ψ (sy Xs Ws x y) = 1) : x ∈ lattice₂ m (latA ΛS ΛT) v := by
  obtain ⟨haa, hcc, ha1, hc1, hfa, hfc, -⟩ := idem_facts ha hsum
  have hx' := (isHalf_m m).2 hx
  refine ⟨GlobalTheory.BigDat.smul_eq_zero_of_isHalf v ha1 hx,
    GlobalTheory.LatVac.mem_of_char hψ hS hT (GlobalTheory.BigDat.map_infPart_of_isHalf v ha1 hx') fun l hl => ?_⟩
  have hy : IsHalf (cA D a) (cA D a • m.symm l) := GlobalTheory.BigDat.isHalf_smul_self hcc _
  have := h _ ⟨GlobalTheory.BigDat.smul_eq_zero_of_isHalf v hc1 hy, by
    rw [map_smul, m.apply_symm_apply]; exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc l hl⟩ hy
  rwa [hB, map_smul, m.apply_symm_apply, GlobalTheory.BigDat.symplO_cA_smul, GlobalTheory.BigDat.smul_of_isHalf hx'] at this

set_option maxHeartbeats 1600000 in

theorem exists_pure (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {Bs : Base D.host.F D.host.E}
    (hψ : IsStdChar D Bs.ψ (-1)) (hBs : Bs.IsGood D.sp.cm.sig) {r s r' s' : ℕ}
    (hX : Xs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s') (hM : Mo.IsGood Bs.ψ)
    (hB : ∀ x y, sy Xs Ws x y = symplO S T (m x) (m y))
    (hle : ∀ v, ∀ u ∈ lattice₂ m (latA ΛS ΛT) v, u ∈ latAtV Xs Ws v)
    (hadd : ∀ Φ ∈ schA D.host.F _, ∀ Φ' ∈ schA D.host.F _, thM m Mo Bs.ψ (Φ + Φ') = thM m Mo Bs.ψ Φ + thM m Mo Bs.ψ Φ')
    (hinj : ∀ Φ ∈ schA D.host.F _, ∀ Φ' ∈ schA D.host.F _, thM m Mo Bs.ψ Φ = thM m Mo Bs.ψ Φ' → Φ = Φ')
    {vac : WO S T → ℂ} (hon : ∃ Φ ∈ schA D.host.F _, thM m Mo Bs.ψ Φ = vac) (hv0 : vac ≠ 0)
    (hv : IsLatVac (heisO Bs.ψ S T) (latA ΛS ΛT) vac)
    {ι : Type} [Fintype ι] (pl : ι → Pl D.host.F) (hpl : Function.Injective pl) (a : ι → AE D)
    (ha : ∀ i, IsSplitIdem D (a i) ∧ a i + cA D (a i) = algebraMap (AF D.host.F) (AE D) (liftV (pl i) 1))
    {ε : AE D} (hε : ε = ∑ i, a i) (Z : ι → Type) [∀ i, TopologicalSpace (Z i)] [∀ i, AddCommGroup (Z i)]
    (A A' : ι → Set (Matrix (Fin n) (Fin k) (AE D))) (hA : ∀ i u, u ∈ A i ↔ IsHalf (a i) u)
    (hA' : ∀ i u, u ∈ A' i ↔ IsHalf (cA D (a i)) u) (co : ∀ i, Matrix (Fin n) (Fin k) (AE D) → Z i)
    (hco : ∀ i u x, co i (u + x) = co i u + co i x) (hcoa : ∀ i u, co i (a i • u) = co i u)
    (hcos : ∀ i z, ∃ x, co i x = z) (I : ∀ i, ((Fin n × Fin k → Fv D.host.F (pl i)) → ℂ) →ₗ[ℂ] (Z i → ℂ))
    (hI : ∀ i, IsLagrModel Mo Bs.ψ (pl i) (A i) (A' i) (co i) (I i)) {Φ f : WO S T → ℂ}
    (hf : IsThetaAt Bs.ψ (symplO S T) (heisO Bs.ψ S T) ε (latA ΛS ΛT) 1 vac Φ f) (hΦ : ∀ x, Φ x ≠ 0 → IsHalf ε x)
    (φ : ∀ v : Pl D.host.F, (Fin n × Fin k → Fv D.host.F v) → ℂ) (hφ : ∀ v, φ v ∈ SB _)
    (hφv : ∀ v, (∀ i, pl i ≠ v) → φ v = Mo.vac v) {κ : ℂ} (hκ : κ ≠ 0)
    (hloc : ∀ x, IsHalf ε x → ∏ i, I i (φ (pl i)) (co i (m.symm x)) = κ * Φ x) :
    ∃ f₀, f₀ ≠ 0 ∧ thM m Mo Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) = f := by
  classical
  have hstd := hBs.std
  obtain ⟨Φ₀, hΦ₀, rfl⟩ := hon
  obtain ⟨g, rfl⟩ := exists_vac m Mo hS hT hψ hBs hX hW hM hB hle hinj hΦ₀ hv
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  have hid := fun i => idem_facts (ha i).1 (ha i).2
  have horth : ∀ i j, i ≠ j → a i * a j = 0 := fun i j hij => by
    have h0 : liftV (pl i) (1 : Fv D.host.F (pl i)) * liftV (pl j) (1 : Fv D.host.F (pl j)) = 0 :=
      GlobalTheory.LatVac.at_liftV (pl j) 1 _ (evalV_singleFin_ne (fun h => hij (hpl h).symm) _)
    rw [← (hid i).2.2.1, ← (hid j).2.2.1, mul_mul_mul_comm, ← map_mul, h0, map_zero, mul_zero]
  have hεa : ∀ i, ε * a i = a i := fun i => by
    rw [hε, Finset.sum_mul, Finset.sum_eq_single i (fun j _ h => horth j i h) (fun h => absurd (Finset.mem_univ _) h), (hid i).1]
  have hinf : infPart D ε = 0 := by
    rw [hε, map_sum]; exact Finset.sum_eq_zero fun i _ => (hid i).2.2.2.2.2.2
  have hinf' : infPart D (cA D ε) = 0 := GlobalTheory.PlaceVec.infPart_cA hinf
  have hco0 : ∀ i, co i 0 = 0 := fun i => by simpa using hco i 0 0
  have hsm : ∀ i u, a i • u ∈ A i := fun i u => (hA i _).2 (GlobalTheory.BigDat.isHalf_smul_self (hid i).1 u)
  have hvac := fun i => GlobalTheory.BigDat.lagr_vac (hI i) (hM.vac _).1 (hM.vac _).2.1 (lattice₂ m (latA ΛS ΛT) (pl i) : Set _)
    (fun γ hγ hγ' => vac_acts m _ Mo hBs hX hW hM (hle _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (ha i).1, (hA i _).1 h⟩) fun h => ⟨_, GlobalTheory.BigDat.splitIdem_conj (ha i).1, (hA' i _).1 h⟩⟩))
    (fun z => by obtain ⟨x, rfl⟩ := hcos i z; exact ⟨_, hsm i x, hcoa i x⟩)
    (fun x hx h => mem_localLattice_of_forall_addChar_eq_one m hS hT hψ hB (ha i).1 (ha i).2 ((hA i _).1 hx) fun y hy hy' => h y hy ((hA' i _).2 hy'))
  set c := ∏ i, I i (Mo.vac _) 0 with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hvac i).1
  have hps : ∀ (z : ℂ) (g : SInf D.host.F (Fin n × Fin k)) (φ : ∀ v : Pl D.host.F, (Fin n × Fin k → Fv D.host.F v) → ℂ),
      thM m Mo Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (z • g) φ) = z • thM m Mo Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) := fun z g φ => by
    rw [← thM_smul]
    exact congrArg _ (funext fun _ => mul_assoc _ _ _)
  let R : Submodule ℂ ((Matrix (Fin n) (Fin k) (AE D) → ℂ) × ((Fin n × Fin k → AF D.host.F) → ℂ)) :=
    { carrier := {p | p.2 ∈ schA D.host.F _ ∧ ((fun t => p.1 (m.symm t)), thM m Mo Bs.ψ p.2) ∈ graphP (latA ΛS ΛT) ε Tm}
      zero_mem' := ⟨zero_mem _, by
        have : thM m Mo Bs.ψ 0 = 0 := by simpa using thM_smul m Mo Bs.ψ 0 0
        rw [Prod.snd_zero, this]; exact zero_mem _⟩
      add_mem' := fun {p q} hp hq => ⟨add_mem hp.1 hq.1, by
        rw [Prod.snd_add, hadd _ hp.1 _ hq.1]; exact add_mem hp.2 hq.2⟩
      smul_mem' := fun z p hp => ⟨Submodule.smul_mem _ z hp.1, by
        rw [Prod.smul_snd, thM_smul]
        exact Submodule.smul_mem _ z hp.2⟩ }
  have hbase : (fun t => Set.indicator (halfP n k ε : Set _) (fun u => ∏ i, I i (Mo.vac _) (co i u)) (m.symm t)) =
      c • halfInd ε (latA ΛS ΛT) := by
    funext t
    obtain ⟨u, rfl⟩ := m.surjective t
    rw [m.symm_apply_apply, Pi.smul_apply, smul_eq_mul, halfInd]
    by_cases hu : IsHalf ε u
    · rw [Set.indicator_of_mem (show u ∈ halfP n k ε from hu), Finset.prod_congr rfl fun i _ =>
        (congrArg _ (hcoa i u).symm).trans ((hvac i).2 _ (hsm i u))]
      by_cases hl : m u ∈ latA ΛS ΛT
      · rw [if_pos ⟨hl, (isHalf_m m).2 hu⟩, mul_one]
        refine Finset.prod_congr rfl fun i _ => Set.indicator_of_mem ?_ _
        exact ⟨GlobalTheory.BigDat.smul_eq_zero_of_isHalf _ (hid i).2.2.1 ((hA i _).1 (hsm i u)), by
          rw [map_smul]; exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ (hid i).2.2.2.2.1 _ hl⟩
      · have : ∃ i, a i • u ∉ lattice₂ m (latA ΛS ΛT) (pl i) := by
          by_contra! hall
          exact hl (GlobalTheory.BigDat.mem_of_sum_smul (P := Finset.univ) (a := a) (hε ▸ (isHalf_m m).2 hu) fun i _ => by
            rw [← map_smul]; exact (hall i).2)
        obtain ⟨i, hn⟩ := this
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hn _), if_neg fun h => hl h.1, mul_zero]
    · rw [Set.indicator_of_notMem (show u ∉ halfP n k ε from hu), if_neg fun h => hu ((isHalf_m m).1 h.2), mul_zero]
  have hR := GlobalTheory.T.heisenbergStableRelation_of_vacua Mo Bs.ψ hstd hM Finset.univ pl hpl.injOn Z A A' co I (halfP n k ε) R (c • g)
    (fun i _ => hI i)
    (fun i _ u hu => ⟨GlobalTheory.BigDat.smul_eq_zero_of_isHalf _ (hid i).2.2.1 ((hA i _).1 hu),
      GlobalTheory.BigDat.isHalf_mono (hεa i) ((hA i _).1 hu)⟩)
    (fun i _ u hu => GlobalTheory.BigDat.smul_eq_zero_of_isHalf _ (hid i).2.2.2.1 ((hA' i _).1 hu))
    (fun i _ u hu => ⟨_, hsm i u, cA D (a i) • u, (hA' i _).2 (GlobalTheory.BigDat.isHalf_smul_self (hid i).2.1 u), by
      rw [← add_smul, (ha i).2, algebraMap_smul, GlobalTheory.BigDatLat.smul_eq_of_at hu]⟩)
    (fun i _ x _ u => hco i u x)
    (fun i _ j _ hne x hx u => by
      rw [hco, ← hcoa j x, ← GlobalTheory.BigDat.smul_of_isHalf ((hA i _).1 hx), smul_smul, horth j i hne, zero_smul, hco0, add_zero])
    (fun i _ u => ⟨_, hsm i u, hcoa i u, fun y hy => by
      refine (hB u y).trans (Eq.trans ?_ (hB _ y).symm)
      rw [map_smul, ← GlobalTheory.BigDat.symplO_cA_smul, GlobalTheory.BigDat.smul_of_isHalf ((isHalf_m m).2 ((hA' i _).1 hy))]⟩)
    (fun i _ x hx p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Mo Bs.ψ hstd x _ hp.1, by
      have hx' : IsHalf ε (m x) := (isHalf_m m).2 (GlobalTheory.BigDat.isHalf_mono (hεa i) ((hA i _).1 hx))
      have := mem_graphP_of_intertwines _ Bs.ψ (fun _ => 1) (m x) (m x) (fun Φ hΦ => by
        simp only [one_mul]
        exact ⟨GlobalTheory.BigDat.GraphHeis.sb_trans_latO hS.1 hT.1 hinf hΦ hx', hTm.trans Φ hΦ _ hx'⟩) hp.2
      simp only [one_mul, map_add, LinearEquiv.symm_apply_apply] at this
      rwa [← thM_rho m Mo hB] at this⟩)
    (fun i _ y hy p hp => ⟨GlobalTheory.HeisSchA.rho_mem_schA Mo Bs.ψ hstd y _ hp.1, by
      have hy' : IsHalf (cA D ε) (m y) := (isHalf_m m).2
        (GlobalTheory.BigDat.isHalf_mono (by rw [← RingHom.map_mul, hεa i]) ((hA' i _).1 hy))
      have := mem_graphP_of_intertwines _ Bs.ψ (fun t => Bs.ψ (symplO S T t (m y))) 0 (m y) (fun Φ hΦ => by
        simp only [add_zero]
        exact ⟨GlobalTheory.BigDat.GraphHeis.sb_modul_latO hψ hS hT hinf' hΦ hy', hTm.modul Φ hΦ _ hy'⟩) hp.2
      simp only [add_zero] at this
      rw [← thM_rho m Mo hB] at this
      convert this using 3 with t
      exact congrArg (fun z => Bs.ψ z * p.1 (m.symm t)) ((hB _ y).trans (by rw [m.apply_symm_apply]))⟩)
    ⟨(isFinPart_vac hM ∅).fam.mem hM _, by
      have := (graphP (latA ΛS ΛT) ε Tm).smul_mem c (Submodule.subset_span ⟨_, GlobalTheory.isSBHalf_halfInd ε _, rfl⟩)
      rw [(congrArg Tm (one_smul ℂ _).symm).trans hTm.vac] at this
      show (_, thM m Mo Bs.ψ _) ∈ _
      rw [hps]
      convert this using 1
      exact Prod.ext hbase rfl⟩
    φ hφ fun v hv => hφv v fun i => hv i (Finset.mem_univ _)
  have hfst : (fun t => Set.indicator (halfP n k ε : Set _) (fun u => ∏ i, I i (φ _) (co i u)) (m.symm t)) = κ • Φ := by
    funext t
    by_cases ht : IsHalf ε t
    · rw [Set.indicator_of_mem (show m.symm t ∈ halfP n k ε from (isHalf_m m).1 (by rwa [m.apply_symm_apply]))]
      exact hloc t ht
    · rw [Set.indicator_of_notMem (show m.symm t ∉ halfP n k ε from fun h => ht (by
        have := (isHalf_m m).2 h
        rwa [m.apply_symm_apply] at this)), Pi.smul_apply, of_not_not (mt (hΦ t) ht), smul_zero]
  have key : thM m Mo Bs.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • g) φ) = κ • f := by
    rw [hall Tm hTm, ← map_smul, ← hfst]
    exact graphP_snd _ hR.2
  refine ⟨κ⁻¹ • c • g, smul_ne_zero (inv_ne_zero hκ) (smul_ne_zero hc0 fun h0 => hv0 ?_), ?_⟩
  · rw [h0, ← zero_smul ℂ (0 : SInf D.host.F (Fin n × Fin k)), hps, zero_smul]
  · rw [hps, key, smul_smul, inv_mul_cancel₀ hκ, one_smul]

end GlobalTheory.BotMatch

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.Grid (sgn)

noncomputable section

namespace GlobalTheory.BotMatch

open GlobalTheory.LatVac (liftV)
open GlobalTheory.RealDict.FockMap

variable {D : D7}

def mapO (S T : HSp D) : Matrix (Fin S.rank) (Fin T.rank) (AE D) ≃ₗ[AE D] WO S T where
  toFun := toO S.gram
  invFun := GlobalTheory.TripleRead.ptO S.gram (Equiv.refl _)
  left_inv := ptO_toO (Formalism.L2.Theta.gram_det_ne S).isUnit
  right_inv := toO_ptO (Formalism.L2.Theta.gram_det_ne S).isUnit
  map_add' u v := by simp only [toO, transpose_add, Matrix.add_mul]
  map_smul' c u := by simp only [toO, transpose_smul, Matrix.smul_mul, RingHom.id_apply]

theorem localLattice_le_latticeAtPlace {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {Xs : Spc D.host.F D.host.E S.rank} {Ws : Spc D.host.F D.host.E T.rank}
    (hLS : ∀ s ∈ ΛS, star s ∈ Xs.L) (hLT : ∀ y ∈ GlobalTheory.SkewLat.scLat D.host.AA ΛT, y ∈ Ws.L) (v : Pl D.host.F) :
    ∀ u ∈ lattice₂ (mapO S T) (latA ΛS ΛT) v, u ∈ latAtV Xs Ws v := by
  intro u hu
  have e : u = liftV v (1 : Fv D.host.F v) • (mapO S T).symm (mapO S T u) := by
    rw [LinearEquiv.symm_apply_apply, GlobalTheory.BigDatLat.smul_eq_of_at hu.1]
  rw [e]
  refine GlobalTheory.BigDat.map_mem_of_closure ((DistribMulAction.toAddMonoidHom _ (liftV v (1 : Fv D.host.F v))).comp
    (mapO S T).symm.toLinearMap.toAddMonoidHom) ?_ hu.2
  rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
  have e2 : (mapO S T).symm (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      pairA D.host.F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (a • t)) := by
    ext p q
    refine (GlobalTheory.BigDat.divG_gen S (pairA D.host.F 0 α) a s t q p).trans ?_
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, mul_comm]
    rfl
  exact (congrArg (fun z => liftV v (1 : Fv D.host.F v) • z ∈ latAtV Xs Ws v) e2).mpr
    (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (hLS s hs) (hLT _ (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha ht)))

set_option maxHeartbeats 800000 in

theorem exists_pure_pair (ε : Bool) (M X : HSp D) {k : ℕ} (hk : k = X.rank) {Xs : Spc D.host.F D.host.E M.rank}
    {Ws : Spc D.host.F D.host.E k} (Mo : Model D.sp.cm.sig Xs Ws) (hJ : Xs.J = GlobalTheory.RealDict.sgE (D := D) ε • M.gram)
    (hJW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (finCongr hk) (finCongr hk))
    {ΛS : Submodule (𝓞 D.host.E) (Fin M.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)}
    (hS : IsSelfDualC (sgn ε M) ΛS) (hT : IsSelfDualC X ΛT) {Bs : Base D.host.F D.host.E}
    (hψ : IsStdChar D Bs.ψ (-1)) (hBs : Bs.IsGood D.sp.cm.sig) {r s r' s' : ℕ}
    (hX : Xs.IsHerm D.sp.cm.sig Bs r s) (hW : Ws.IsSkew D.sp.cm.sig Bs r' s') (hM : Mo.IsGood Bs.ψ)
    (hLS : ∀ s ∈ ΛS, star s ∈ Xs.L)
    (hLT : ∀ y : Fin k → D.host.E, (fun a => y ((finCongr hk).symm a)) ∈ GlobalTheory.SkewLat.scLat D.host.AA ΛT → y ∈ Ws.L)
    {θ : InfFam D} (hθ : IsInfFam θ) {vac : WO (sgn ε M) X → ℂ} (hth : IsThetaFunO Bs.ψ (sgn ε M) X vac) (hv0 : vac ≠ 0)
    (hv : IsLatVac (heisO Bs.ψ (sgn ε M) X) (latA (S := sgn ε M) ΛS ΛT) vac)
    {ι : Type} [Fintype ι] (pl : ι → Pl D.host.F) (hpl : Function.Injective pl) (a : ι → AE D)
    (ha : ∀ i, IsSplitIdem D (a i) ∧ a i + cA D (a i) = algebraMap (AF D.host.F) (AE D) (liftV (pl i) 1))
    {η : AE D} (hη : η = ∑ i, a i) (Z : ι → Type) [∀ i, TopologicalSpace (Z i)] [∀ i, AddCommGroup (Z i)]
    (A A' : ι → Set (Matrix (Fin M.rank) (Fin k) (AE D))) (hA : ∀ i u, u ∈ A i ↔ IsHalf (a i) u)
    (hA' : ∀ i u, u ∈ A' i ↔ IsHalf (cA D (a i)) u) (co : ∀ i, Matrix (Fin M.rank) (Fin k) (AE D) → Z i)
    (hco : ∀ i u x, co i (u + x) = co i u + co i x) (hcoa : ∀ i u, co i (a i • u) = co i u)
    (hcos : ∀ i z, ∃ x, co i x = z) (I : ∀ i, ((Fin M.rank × Fin k → Fv D.host.F (pl i)) → ℂ) →ₗ[ℂ] (Z i → ℂ))
    (hI : ∀ i, IsLagrModel Mo Bs.ψ (pl i) (A i) (A' i) (co i) (I i)) {Φ f : WO (sgn ε M) X → ℂ}
    (hf : IsThetaAt Bs.ψ (symplO (sgn ε M) X) (heisO Bs.ψ (sgn ε M) X) η (latA (S := sgn ε M) ΛS ΛT) 1 vac Φ f)
    (hΦ : ∀ x, Φ x ≠ 0 → IsHalf η x)
    (φ : ∀ v : Pl D.host.F, (Fin M.rank × Fin k → Fv D.host.F v) → ℂ) (hφ : ∀ v, φ v ∈ SB _)
    (hφv : ∀ v, (∀ i, pl i ≠ v) → φ v = Mo.vac v) {κ : ℂ} (hκ : κ ≠ 0)
    (hloc : ∀ x, IsHalf η x →
      ∏ i, I i (φ (pl i)) (co i (GlobalTheory.TripleRead.ptO (sgn ε M).gram (finCongr hk) x)) = κ * Φ x) :
    ∃ f₀, f₀ ≠ 0 ∧ GlobalTheory.TripleRead.thO Mo Bs.ψ (sgn ε M).gram (finCongr hk) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) = f := by
  subst hk
  obtain ⟨t1, -, t3, t4, -⟩ := th_laws Mo hψ hθ hJ hJW hM
  obtain ⟨co', hco'⟩ := exists_co Mo hJ hJW
  have hB : ∀ x y, sy Xs Ws x y = symplO (sgn ε M) X (mapO (sgn ε M) X x) (mapO (sgn ε M) X y) := fun x y => by
    rw [GlobalTheory.ThetaTransform.symplO_eq_symp (ξ := 1) rfl (one_smul _ _), co'.form, hco', hco']
    refine (Mo.co.form x y).trans ?_
    have h1 := (mapO (sgn ε M) X).symm_apply_apply x
    have h2 := (mapO (sgn ε M) X).symm_apply_apply y
    exact congrArg₂ (fun x y => (Mo.co.e x).1 ⬝ᵥ (Mo.co.e y).2 - (Mo.co.e y).1 ⬝ᵥ (Mo.co.e x).2) h1.symm h2.symm
  exact exists_pure (mapO (sgn ε M) X) Mo hS hT hψ hBs hX hW hM hB (localLattice_le_latticeAtPlace hLS hLT) t1 t3 ((t4 vac).1 hth) hv0 hv
    pl hpl a ha hη Z A A' hA hA' co hco hcoa hcos I hI hf hΦ φ hφ hφv hκ hloc

end GlobalTheory.BotMatch

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BotMatch

section Mat

variable {K : Type} [CommRing K] {a d k : Type} [Fintype a] [Fintype d] [Fintype k] [DecidableEq a] [DecidableEq d]
  [DecidableEq k]

theorem coord_fst (e : k ≃ d) (x : Matrix d a K) {G G' : Matrix a a K} (hG : G' * G = 1) (β : Matrix a a K) {b b' : Matrix a a K}
    (hb : b * b' = 1) {c c' : Matrix k k K} (hc : c * c' = 1) (γ : Matrix d d K) :
    (βᵀ * Gᵀ * b) * (b' * ((x * G')ᵀ.submatrix id e) * c'ᵀ) * (γ.submatrix e e * c)ᵀ = (γ * x * β)ᵀ.submatrix id e := by
  have h1 : c'ᵀ * cᵀ = 1 := by rw [← transpose_mul, hc, transpose_one]
  have h2 : Gᵀ * G'ᵀ = 1 := by rw [← transpose_mul, hG, transpose_one]
  have h3 : (x * G')ᵀ.submatrix id e = G'ᵀ * xᵀ.submatrix id e := by
    rw [transpose_mul]; ext i j; simp [Matrix.mul_apply]
  have h4 : (γ * x * β)ᵀ.submatrix id e = βᵀ * (xᵀ.submatrix id e * (γ.submatrix e e)ᵀ) := by
    rw [transpose_submatrix, Matrix.submatrix_mul_equiv, transpose_mul, transpose_mul]
    ext i j; simp [Matrix.mul_apply]
  rw [h3, h4, transpose_mul]
  calc _ = βᵀ * (Gᵀ * (b * b') * G'ᵀ) * xᵀ.submatrix id e * (c'ᵀ * cᵀ) * (γ.submatrix e e)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hb, Matrix.mul_one, h2, h1]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]

theorem coord_snd (e : k ≃ d) (y : Matrix a d K) {G G' : Matrix a a K} (hG : G * G' = 1) (β : Matrix a a K) {b b' : Matrix a a K}
    (hb : b * b' = 1) {c c' : Matrix k k K} (hc : c * c' = 1) (H γ : Matrix d d K) (ξ : K) :
    (β * G' * b'ᵀ) * (-(bᵀ * (-G) * ((G' * y).submatrix id e) * (ξ • Hᵀ.submatrix e e)ᵀ * c)) * (c' * γ.submatrix e e) =
      (ξ • (β * (G' * y * H) * γ)).submatrix id e := by
  have h1 : b'ᵀ * bᵀ = 1 := by rw [← transpose_mul, hb, transpose_one]
  have h3 : (G' * y).submatrix id e = G' * y.submatrix id e := by ext i j; simp [Matrix.mul_apply]
  have h4 : (ξ • (β * (G' * y * H) * γ)).submatrix id e = ξ • (β * G' * (y.submatrix id e * H.submatrix e e * γ.submatrix e e)) := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    simp only [Matrix.mul_assoc]
    ext i j; simp [Matrix.mul_apply]
  have h5 : (ξ • Hᵀ.submatrix e e)ᵀ = ξ • H.submatrix e e := rfl
  rw [h3, h4, h5]
  calc _ = ξ • (β * G' * ((b'ᵀ * bᵀ) * (G * G') * y.submatrix id e * H.submatrix e e * (c * c') * γ.submatrix e e)) := by
        simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, neg_neg, smul_neg, Matrix.mul_smul, Matrix.smul_mul]
    _ = _ := by rw [h1, hG, hc]; simp only [Matrix.mul_one, Matrix.one_mul]

end Mat

variable {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem piW_atPl (y : Fv D.host.F v) : piW τ (atPl (splitPrime τ) (complEquiv τ (splitPrime_under τ) y)) = y := by
  classical
  exact (complEquiv τ (splitPrime_under τ)).injective
    (by rw [GlobalTheory.FlipMatch.isPlaceIso_complEquiv τ, (atPl_spec _ _).2, Pi.single_eq_same])

theorem piW_atPl_one : piW τ (atPl (D := D) (splitPrime τ) 1) = 1 := by
  have := piW_atPl τ 1
  rwa [map_one] at this

theorem piW_conj_atPl_one : piW (τ.comp D.sp.cm.sig) (atPl (D := D) (splitPrime τ) 1) = 0 := by
  classical
  exact (complEquiv (τ.comp D.sp.cm.sig) (splitPrime_under _)).injective (by
    rw [GlobalTheory.FlipMatch.isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), (atPl_spec _ _).2,
      Pi.single_eq_of_ne (splitPrime_comp_ne (isCMExt_host D) τ), map_zero])

theorem atPl_mul_eq_zero {z : AE D} (h : piW τ z = 0) : atPl (splitPrime τ) 1 * z = 0 := by
  classical
  refine ae_ext (by rw [RingHom.map_mul, (atPl_spec _ _).1, zero_mul, map_zero]) fun Q => ?_
  rw [RingHom.map_mul, RingHom.map_mul, (atPl_spec _ _).2, map_zero, map_zero]
  by_cases hQ : Q = splitPrime τ
  · subst hQ
    rw [← GlobalTheory.FlipMatch.isPlaceIso_complEquiv τ z, h, map_zero, mul_zero]
  · rw [Pi.single_eq_of_ne hQ, zero_mul]

theorem exists_map_piW {m n : Type} (U : Matrix m n (Fv D.host.F v)) : ∃ u : Matrix m n (AE D), u.map (piW τ) = U :=
  ⟨U.map fun y => atPl (splitPrime τ) (complEquiv τ (splitPrime_under τ) y), Matrix.ext fun _ _ => piW_atPl τ _⟩

theorem piW_incA (x : D.host.E) : piW τ (incA D x) = τ x :=
  (GlobalTheory.FlipMatch.piW_tmul τ 1 x).trans (by rw [map_one, one_mul])

theorem evW_eToEAf (x : D.host.E) : evW τ (eToEAf D x) = τ x := (evW_toEAf τ (incA D x)).trans (piW_incA τ x)

theorem half_iff {m n : ℕ} (hsum : atPl (D := D) (splitPrime τ) 1 + cA D (atPl (splitPrime τ) 1) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) (u : Matrix (Fin m) (Fin n) (AE D)) :
    ((At (evFin D.host.F v) u ∧ u.map (piW (τ.comp D.sp.cm.sig)) = 0) ↔ IsHalf (atPl (splitPrime τ) 1) u) ∧
    ((At (evFin D.host.F v) u ∧ u.map (piW τ) = 0) ↔ IsHalf (cA D (atPl (splitPrime τ) 1)) u) := by
  have hat := GlobalTheory.FlipMatch.at_atPl τ 1
  have hat' := GlobalTheory.FlipMatch.RowChart.at_cA hat
  have hone : At (evFin D.host.F v) u → ∀ p q, atPl (splitPrime τ) 1 * u p q + cA D (atPl (splitPrime τ) 1) * u p q = u p q :=
    fun h p q => by
      have h1 := h (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
      rw [sub_smul, one_smul, sub_eq_zero] at h1
      rw [← add_mul, hsum, ← Algebra.smul_def]
      exact (congrFun (congrFun h1 p) q).symm
  have hAt : ∀ b : AE D, At (evFin D.host.F v) b → IsHalf b u → At (evFin D.host.F v) u := fun b hb h c hc => by
    ext p q
    rw [Matrix.smul_apply, ← h p q, ← smul_mul_assoc, hb c hc, zero_mul, Matrix.zero_apply]
  refine ⟨⟨fun h p q => ?_, fun h => ⟨hAt _ hat h, Matrix.ext fun p q => ?_⟩⟩,
    ⟨fun h p q => ?_, fun h => ⟨hAt _ hat' h, Matrix.ext fun p q => ?_⟩⟩⟩
  · have h1 := congrArg (cA D) (atPl_mul_eq_zero τ (z := cA D (u p q))
      ((GlobalTheory.FlipMatch.RowChart.piW_cA_eq τ _).trans (congrFun (congrFun h.2 p) q)))
    rw [RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA, map_zero] at h1
    have h2 := hone h.1 p q
    rwa [h1, add_zero] at h2
  · rw [Matrix.map_apply, ← h p q, RingHom.map_mul, piW_conj_atPl_one, zero_mul, Matrix.zero_apply]
  · have h2 := hone h.1 p q
    rwa [atPl_mul_eq_zero τ (congrFun (congrFun h.2 p) q), zero_add] at h2
  · rw [Matrix.map_apply, ← h p q, RingHom.map_mul, GlobalTheory.FlipMatch.RowChart.piW_cA_eq, piW_conj_atPl_one, zero_mul,
      Matrix.zero_apply]

theorem gram_inv_map (S : HSp D) : (S.gram⁻¹).map τ * S.gram.map τ = 1 := by
  have := Matrix.map_mul (L := S.gram⁻¹) (M := S.gram) (f := (τ : D.host.E →+* Fv D.host.F v))
  rw [Matrix.nonsing_inv_mul _ (Formalism.L2.Theta.gram_det_ne S).isUnit, Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this.symm

theorem frMapO_coX (S X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βX : GL (Fin X.rank) (Lev.EAf D)) (b : GL (Fin S.rank) (Fv D.host.F v)) (c : GL (Fin k) (Fv D.host.F v)) (x : WO S X) :
    ((βS.val.map (evW τ))ᵀ * (S.gram.map τ)ᵀ * b.val) * ((b⁻¹).val * (GlobalTheory.TripleRead.ptO S.gram e x).map (piW τ) * (c⁻¹).valᵀ) *
      ((((βX⁻¹).val.map (evW τ)).submatrix e e) * c.val)ᵀ = (((frMapO S X βS βX x).map (evW τ))ᵀ).submatrix id e := by
  have h1 : (GlobalTheory.TripleRead.ptO S.gram e x).map (piW τ) = (x.map (piW τ) * (S.gram⁻¹).map τ)ᵀ.submatrix id e := by
    have : (S.gram⁻¹).map τ = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹).map (piW τ) := Matrix.ext fun _ _ => (piW_incA τ _).symm
    rw [this, ← Matrix.map_mul]
    rfl
  have h2 : (frMapO S X βS βX x).map (evW τ) = (βX⁻¹).val.map (evW τ) * x.map (piW τ) * βS.val.map (evW τ) := by
    have : x.map (piW τ) = (x.map (toEAf D)).map (evW τ) := Matrix.ext fun _ _ => (evW_toEAf τ _).symm
    rw [this, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  rw [h1, h2]
  exact coord_fst e _ (gram_inv_map τ S) _ b.mul_inv c.mul_inv _

theorem dualCoord_coY (S X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βX : GL (Fin X.rank) (Lev.EAf D)) (b : GL (Fin S.rank) (Fv D.host.F v)) (c : GL (Fin k) (Fv D.host.F v)) (y : WO S X) :
    ((βS⁻¹).val.map (evW τ) * (S.gram⁻¹).map τ * (b⁻¹).valᵀ) *
      (-(b.valᵀ * ((-1 : D.host.E) • S.gram).map τ * (GlobalTheory.TripleRead.ptO S.gram e y).map (piW (τ.comp D.sp.cm.sig)) *
        ((D.host.xi0 • (X.gramᵀ).submatrix e e).map τ)ᵀ * c.val)) * ((c⁻¹).val * (βX.val.map (evW τ)).submatrix e e) =
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S X βS βX y).map (evW τ)).submatrix id e := by
  have hs : (S.gram⁻¹).map star = (S.gram⁻¹)ᵀ := by
    have h0 : S.gramᴴ = S.gram := Matrix.ext fun a b => S.herm.eq _ _
    have := Matrix.conjTranspose_nonsing_inv S.gram
    rw [h0] at this
    ext a b
    exact congrFun (congrFun this b) a
  have h1 : (GlobalTheory.TripleRead.ptO S.gram e y).map (piW (τ.comp D.sp.cm.sig)) =
      ((S.gram⁻¹).map τ * ((y.map (cA D)).map (piW τ))ᵀ).submatrix id e := by
    have e1 : (S.gram⁻¹).map τ = ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹).map (piW (τ.comp D.sp.cm.sig)))ᵀ :=
      Matrix.ext fun a b => ((piW_incA (τ.comp D.sp.cm.sig) _).trans (congrArg τ (congrFun (congrFun hs b) a))).symm
    have e2 : (y.map (cA D)).map (piW τ) = y.map (piW (τ.comp D.sp.cm.sig)) :=
      Matrix.ext fun _ _ => GlobalTheory.FlipMatch.RowChart.piW_cA_eq τ _
    rw [e1, e2, ← transpose_mul, ← Matrix.map_mul]
    rfl
  have h2 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S X βS βX y).map (evW τ) = τ D.host.xi0 • ((βS⁻¹).val.map (evW τ) *
      ((S.gram⁻¹).map τ * ((y.map (cA D)).map (piW τ))ᵀ * X.gram.map τ) * βX.val.map (evW τ)) := by
    have e1 : ∀ {p : ℕ} (M : Matrix (Fin p) (Fin p) D.host.E), M.map τ = (M.map (incA D)).map (piW τ) := fun M =>
      Matrix.ext fun _ _ => (piW_incA τ _).symm
    have e2 : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) (AE D)), M.map (piW τ) = (M.map (toEAf D)).map (evW τ) := fun M =>
      Matrix.ext fun _ _ => (evW_toEAf τ _).symm
    rw [e1, e1 X.gram, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, e2, ← Matrix.map_mul, ← Matrix.map_mul,
      ← evW_eToEAf]
    exact Matrix.ext fun _ _ => map_mul (evW τ) _ _
  have h3 : ((-1 : D.host.E) • S.gram).map τ = -S.gram.map τ := Matrix.ext fun _ _ => by simp
  have h4 : (D.host.xi0 • (X.gramᵀ).submatrix e e).map τ = τ D.host.xi0 • (X.gram.map τ)ᵀ.submatrix e e :=
    Matrix.ext fun _ _ => map_mul τ _ _
  rw [h1, h2, h3, h4]
  exact coord_snd e _ (mul_eq_one_comm.1 (gram_inv_map τ S)) _ b.mul_inv c.mul_inv _ _ _

end GlobalTheory.BotMatch

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

namespace GlobalTheory.BotMatch

variable {D : D7}

set_option maxHeartbeats 1600000 in
theorem local_pair {ψ : AddChar (AF D.host.F) ℂ} {W W₁ X : HSp D} {A : GlobalTheory.ChainFr.Fr W} {A₁ : GlobalTheory.ChainFr.Fr W₁}
    {B : GlobalTheory.ChainFr.Fr X} {α β : (AE D)ˣ →* Circle} {e : Fin (W.rank + W₁.rank) ≃ Fin X.rank} {Bs : Base D.host.F D.host.E}
    {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank} {Xc : Chars D.host.F D.host.E} {om : Rep D.sp.cm.sig Γ.V Γ.W}
    {om' : Rep D.sp.cm.sig Γ.V' Γ.W} (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc) {R Rf}
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf) {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (sW : IsSelfDualC (GlobalTheory.Grid.sgn true W) ΛW) {βW : GL (Fin W.rank) (Lev.EAf D)} (fW : Formalism.L2.DIV.IsFrame βW ΛW)
    (hL : Γ.V.L = GlobalTheory.TripleSpaceW.conjSub ΛW) (βW₁ : GL (Fin W₁.rank) (Lev.EAf D)) (βX : GL (Fin X.rank) (Lev.EAf D))
    {νH : Formalism.L2.Host.HChar D.host.E} (hν : ChrEq (α / β) νH) (i : Bs.P) (hi : i.1 ∈ Xc.T) {c : ℕ}
    (hc : GlobalTheory.CMVal.ExpAt νH (splitPrime (Bs.τ i)) c) :
    ∃ (I : ((Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ) →ₗ[ℂ]
        (Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (Fv D.host.F i.1) → ℂ))
      (I' : ((Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ) →ₗ[ℂ]
        (Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (Fv D.host.F i.1) → ℂ))
      (φ : (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ)
      (φ' : (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ) (lam : ℂ),
      Γ.M.IsLinW Bs.ψ (Bs.τ i) (Γ.V.bas i) (Γ.W.bas i) I ∧ Γ.M'.IsLinBar Bs.ψ (Bs.τ i) (Γ.V'.bas i) (Γ.W.bas i) I' ∧
      φ ∈ GlobalTheory.WeilM.SB _ ∧ φ' ∈ GlobalTheory.WeilM.SB _ ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ lam ≠ 0 ∧ Rf.p i φ = Rf.p' i φ' ∧
      (∀ x : WO W X, I φ (((Γ.V.bas i)⁻¹).1 * (GlobalTheory.TripleRead.ptO (GlobalTheory.Grid.sgn true W).gram e x).map (piW (Bs.τ i)) *
          ((Γ.W.bas i)⁻¹).1ᵀ) =
        GlobalTheory.StdPairCone.stdA (chrW (α / β) (Bs.τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt i.1) c W.rank W₁.rank
          ((((frMapO W X βW βX x).map (evW (Bs.τ i)))ᵀ).submatrix id e)) ∧
      ∀ y : WO W₁ X, I' φ' (-((Γ.V'.bas i).1ᵀ * Γ.V'.J.map (Bs.τ i) *
          (GlobalTheory.TripleRead.ptO W₁.gram e y).map (piW ((Bs.τ i).comp D.sp.cm.sig)) * (Γ.W.J.map (Bs.τ i))ᵀ * (Γ.W.bas i).1)) =
        lam * GlobalTheory.StdPairCone.stdB (chrW (α / β) (Bs.τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt i.1) c W.rank W₁.rank
          (((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord W₁ X βW₁ βX y).map (evW (Bs.τ i))).submatrix id e) := by
  have hXν : Xc.ν = α / β := by
    show Xc.α / Xc.β = _
    rw [h.α, h.β]
  obtain ⟨I, I', hI, hI', -, -, hiff⟩ := hM.fin.zeta i hi
  obtain ⟨-, -, hquot, ⟨m, hmα, hmβ⟩, hua, hub⟩ := GlobalTheory.T.seesawCharacter_conductor_at_ramified_place _ _ _ Bs _ _ Γ Xc om om' hM.triple i hi
  obtain ⟨hcond, hc1⟩ := UpperTheory.localChar_conductor_le_of_heckeExponent D (α / β) νH hν i.1 (Bs.τ i) c hc
  have hram := hM.triple.chars.ram (splitPrime (Bs.τ i)) ((splitPrime_under (Bs.τ i)).symm ▸ hi)
  rw [hXν] at hram
  obtain ⟨gA, hgA, egA⟩ := UpperTheory.exists_maxCompact_eq_frame_gram_splitBasis D (GlobalTheory.Grid.sgn true W) ΛW βW sW fW i.1 (Bs.τ i) (Γ.V.bas i)
    (hL ▸ hM.triple.geo.hV.bas i)
  have hx1 : (βX.val.map (evW (Bs.τ i))).submatrix e e * ((βX⁻¹).val.map (evW (Bs.τ i))).submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.submatrix_one_equiv]
  let bX : GL (Fin (W.rank + W₁.rank)) (Fv D.host.F i.1) := ⟨_, _, hx1, mul_eq_one_comm.1 hx1⟩
  have hy1 : (βW₁⁻¹).val.map (evW (Bs.τ i)) * βW₁.val.map (evW (Bs.τ i)) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hy2 := gram_inv_map (Bs.τ i) W₁
  have hy3 : ((Γ.V'.bas i)⁻¹).valᵀ * (Γ.V'.bas i).valᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  let gB : GL (Fin W₁.rank) (Fv D.host.F i.1) :=
    ⟨_, _, hy1, mul_eq_one_comm.1 hy1⟩ * ⟨_, _, hy2, mul_eq_one_comm.1 hy2⟩ * ⟨_, _, hy3, mul_eq_one_comm.1 hy3⟩
  rw [← hXν] at hcond ⊢
  obtain ⟨lam, Ξ, Ψ, hlam, eΞ, eΨ, sΞ, sΨ, nΞ, nΨ, hz⟩ := UpperTheory.exists_scaled_standardPairSections_of_maxCompact_translate (Fv D.host.F i.1) _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt i.1) c m
    W.rank W₁.rank (GlobalTheory.SplitFlip.exists_isUnif).choose_spec hquot (hc1 hram) hcond hmα hmβ hua hub gA gB
    ((Γ.W.bas i)⁻¹ * bX) hgA
  obtain ⟨φ, sφ, rfl⟩ := hI.bij.surjOn sΞ
  obtain ⟨φ', sφ', rfl⟩ := hI'.bij.surjOn sΨ
  refine ⟨I, I', φ, φ', lam, hI, hI', sφ, sφ', fun h0 => nΞ (by rw [h0, map_zero]), fun h0 => nΨ (by rw [h0, map_zero]), hlam,
    (hiff φ sφ φ' sφ').2 hz, fun x => ?_, fun y => ?_⟩
  · rw [eΞ, egA]
    exact congrArg _ (frMapO_coX (Bs.τ i) (GlobalTheory.Grid.sgn true W) X e βW βX (Γ.V.bas i) (Γ.W.bas i) x)
  · rw [eΨ, h.JW₁, h.JX]
    exact congrArg (fun z => lam * GlobalTheory.StdPairCone.stdB _ _ c _ _ z)
      (dualCoord_coY (Bs.τ i) W₁ X e βW₁ βX (Γ.V'.bas i) (Γ.W.bas i) y)

end GlobalTheory.BotMatch

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BotMatch

variable {D : D7}

set_option maxHeartbeats 3200000 in

theorem match_of_tri (hH : GlobalTheory.Published.HoweDualityReal) (hPr : GlobalTheory.FunPr.Hypotheses₂) (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {T : Type} {A A' WW : HSp D}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri T A A' WW) {α β : T → ((AE D)ˣ →* Circle)} {νH : T → Formalism.L2.Host.HChar D.host.E}
    {S : T → Finset (Pl D.host.E)} (hX : X.Is ψ θ α β νH S) (t : T) (hT : GlobalTheory.SquareComm.IsTriple A A' WW (α t) (β t))
    (hν : ChrEq (α t / β t) (νH t))
    (hτ : ∀ v : Pl D.host.F, (∃ w ∈ S t, w.under (𝓞 D.host.F) = v) → ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      ∀ w ∈ S t, w.under (𝓞 D.host.F) = v → splitPrime τ = w)
    (hram : ∀ w ∈ S t, ¬ GlobalTheory.LFun.UnrAt (α t / β t) w)
    (hunr : ∀ w : Pl D.host.E, (∀ w' ∈ S t, w'.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) →
      GlobalTheory.LFun.UnrAt (α t) w ∧ GlobalTheory.LFun.UnrAt (β t) w)
    (hid : ∀ w ∈ S t, IsSplitIdem D (atPl w 1) ∧ atPl w 1 + cA D (atPl w 1) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV (w.under (𝓞 D.host.F)) 1))
    (hε : X.e t = ∑ w ∈ S t, atPl w 1) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (hf : GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t)) (hf' : GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW (X.f' t)) :
    ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi)
      (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi)
      (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW (α t) (β t) (X.ω t) (X.ω' t) Pi rf rl p p' ∧
      ((∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW (X.f t) P) = 0) ∨
        ∃ (P : PolF D WW.rank A.rank) (P' : PolF D WW.rank A'.rank) (κ : ℂ),
          p (GlobalTheory.SquareComm.fockF ψ θ true FA FW (X.f t) P) ≠ 0 ∧
          p (GlobalTheory.SquareComm.fockF ψ θ true FA FW (X.f t) P) = κ • p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW (X.f' t) P')) := by
  classical
  have hA := hX.weil t
  have hB := hX.weil' t
  have sA : IsSelfDualC (GlobalTheory.Grid.sgn true A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.rigA.1
  obtain ⟨Bs, Γ, Xc, om, om', h, hTr, hTA, hTB, hLV, hLV', hLW, hP, hPw⟩ :=
    exists_reading_lat hψ FA FA' FW hT hA hB sA hX.rigA'.1 hX.rigW.1 (S t) hτ hram hunr
  obtain rfl := h.ψ
  obtain ⟨R, Rf, hM⟩ := hLM _ _ _ Bs _ _ Γ Xc om om' hTr
  have hg := hTr.geo
  have hinj : Function.Injective fun i : Bs.P => splitPrime (Bs.τ i) := fun i j hij =>
    Subtype.ext ((splitPrime_under (Bs.τ i)).symm.trans ((congrArg (fun w : Pl D.host.E => w.under (𝓞 D.host.F)) hij).trans
      (splitPrime_under (Bs.τ j))))
  have hmem : ∀ i : Bs.P, splitPrime (Bs.τ i) ∈ S t := fun i => (hPw _).2 ⟨i, rfl⟩
  have ha : ∀ i : Bs.P, IsSplitIdem D (atPl (splitPrime (Bs.τ i)) 1) ∧
      atPl (splitPrime (Bs.τ i)) 1 + cA D (atPl (splitPrime (Bs.τ i)) 1) =
        algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV i.1 1) := fun i => by
    have := hid _ (hmem i)
    rwa [splitPrime_under] at this
  have he : X.e t = ∑ i : Bs.P, atPl (splitPrime (Bs.τ i)) 1 := by
    have : S t = Finset.univ.image fun i : Bs.P => splitPrime (Bs.τ i) := by
      ext w; simp [hPw]
    rw [hε, this, Finset.sum_image fun i _ j _ hij => hinj hij]
  choose I I' φ φ' lam hI hI' sφ sφ' nφ nφ' nlam hφφ' eφ eφ' using fun i : Bs.P =>
    local_pair h hM sA hX.rigA.2.1 hLV X.rA'.β X.rW.β hν i (by rw [hP]; exact i.2) (hX.expo t _ (hmem i))
  let Φ : ∀ v : Pl D.host.F, (Fin A.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ :=
    fun v => if hv : v ∈ Bs.P then φ ⟨v, hv⟩ else Γ.M.vac v
  let Φ' : ∀ v : Pl D.host.F, (Fin A'.rank × Fin (A.rank + A'.rank) → Fv D.host.F v) → ℂ :=
    fun v => if hv : v ∈ Bs.P then φ' ⟨v, hv⟩ else Γ.M'.vac v
  have e1 : ∀ i : Bs.P, Φ i = φ i := fun i => dif_pos i.2
  have e1' : ∀ i : Bs.P, Φ' i = φ' i := fun i => dif_pos i.2
  have e2 : ∀ v ∉ Bs.P, Φ v = Γ.M.vac v := fun v hv => dif_neg hv
  have e2' : ∀ v ∉ Bs.P, Φ' v = Γ.M'.vac v := fun v hv => dif_neg hv
  have hall : ∀ v, (Φ v ∈ GlobalTheory.WeilM.SB _ ∧ Φ v ≠ 0) ∧ (Φ' v ∈ GlobalTheory.WeilM.SB _ ∧ Φ' v ≠ 0) ∧ Rf.p v (Φ v) = Rf.p' v (Φ' v) := by
    intro v
    by_cases hv : v ∈ Bs.P
    · rw [e1 ⟨v, hv⟩, e1' ⟨v, hv⟩]
      exact ⟨⟨sφ _, nφ _⟩, ⟨sφ' _, nφ' _⟩, hφφ' ⟨v, hv⟩⟩
    · rw [e2 v hv, e2' v hv]
      exact ⟨⟨(hg.hM.vac v).1, (hg.hM.vac v).2.1⟩, ⟨(hg.hM'.vac v).1, (hg.hM'.vac v).2.1⟩, (hM.fin.sph v (by rw [hP]; exact hv)).1⟩
  have ev : ∀ᶠ v in Filter.cofinite, Φ v = Γ.M.vac v := Bs.P.eventually_cofinite_notMem.mono e2
  have ev' : ∀ᶠ v in Filter.cofinite, Φ' v = Γ.M'.vac v := Bs.P.eventually_cofinite_notMem.mono e2'
  obtain ⟨f₀, nf₀, ef₀⟩ := exists_pure_pair true A WW hT.rank.symm Γ.M h.JW h.JX sA hX.rigW.1 hψ hTr.base hg.hV hg.hW hg.hM
    (fun s hs => hLV ▸ GlobalTheory.BigDat.star_mem_conjSub hs) hLW hθ hX.isVac.2.theta (GlobalTheory.BigDat.vac_ne_zero (S := GlobalTheory.Grid.neg A) hX.isVac) hX.isVac.2.lat
    (Subtype.val : Bs.P → _) Subtype.val_injective _ ha he _ _ _ (fun i u => (half_iff (Bs.τ i) (ha i).2 u).1)
    (fun i u => (half_iff (Bs.τ i) (ha i).2 u).2)
    (fun i u => ((Γ.V.bas i)⁻¹).1 * u.map (piW (Bs.τ i)) * ((Γ.W.bas i)⁻¹).1ᵀ)
    (fun i u x => by rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul])
    (fun i u => by
      congr 2
      exact Matrix.ext fun p q => (map_mul (piW (Bs.τ i)) _ _).trans (by rw [piW_atPl_one, one_mul]; rfl))
    (fun i z => by
      obtain ⟨u, hu⟩ := exists_map_piW (Bs.τ i) ((Γ.V.bas i).1 * z * (Γ.W.bas i).1ᵀ)
      refine ⟨u, ?_⟩
      beta_reduce
      rw [hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul,
        Units.inv_mul, transpose_one, Matrix.mul_one])
    I (fun i => GlobalTheory.BigNZ.isLagrModel_of_isLin (hI i)) (hX.fst t)
    (fun x hx => by
      by_contra hn
      exact hx (if_neg fun h' => hn h'.1))
    Φ (fun v => (hall v).1.1) (fun v hv => e2 v fun h' => hv ⟨v, h'⟩ rfl) one_ne_zero
    (fun x hx => by
      rw [one_mul]
      refine Eq.trans ?_ (UpperTheory.stdSectionFirst_eq_prod_local D _ _ (hX.idem t) Bs.P Subtype.val Bs.τ hPw hinj (X.c t) (α t / β t) A WW X.rA.β X.rW.β
        A'.rank hT.rank.symm x hx).symm
      exact Finset.prod_congr rfl fun i _ => by rw [e1 i]; exact eφ i x)
  have dV' : ∀ i : Bs.P, IsUnit ((Γ.V'.bas i).1ᵀ * Γ.V'.J.map (Bs.τ i)) := fun i => by
    refine ((Matrix.isUnit_transpose _).2 (Γ.V'.bas i).isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).2 ?_)
    have := RingHom.map_det (Bs.τ i : D.host.E →+* Fv D.host.F i.1) Γ.V'.J
    refine (this ▸ IsUnit.map _ (Ne.isUnit ?_) : IsUnit ((Bs.τ i : D.host.E →+* Fv D.host.F i.1).mapMatrix Γ.V'.J).det)
    rw [h.JW₁, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Formalism.L2.Theta.gram_det_ne A')
  have dW : ∀ i : Bs.P, IsUnit ((Γ.W.J.map (Bs.τ i))ᵀ * (Γ.W.bas i).1) := fun i => by
    refine ((Matrix.isUnit_transpose _).2 ((Matrix.isUnit_iff_isUnit_det _).2 ?_)).mul (Γ.W.bas i).isUnit
    have := RingHom.map_det (Bs.τ i : D.host.E →+* Fv D.host.F i.1) Γ.W.J
    refine (this ▸ IsUnit.map _ (Ne.isUnit ?_) : IsUnit ((Bs.τ i : D.host.E →+* Fv D.host.F i.1).mapMatrix Γ.W.J).det)
    rw [h.JX, Matrix.det_smul, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)) (Formalism.L2.Theta.gram_det_ne WW)
  obtain ⟨f₁, nf₁, ef₁⟩ := exists_pure_pair false A' WW hT.rank.symm Γ.M' h.JW₁ h.JX hX.rigA'.1 hX.rigW.1 hψ hTr.base hg.hV' hg.hW
    hg.hM' (fun s hs => hLV' ▸ GlobalTheory.BigDat.star_mem_conjSub hs) hLW hθ hX.isVac'.2.theta (GlobalTheory.BigDat.vac_ne_zero hX.isVac')
    hX.isVac'.2.lat (Subtype.val : Bs.P → _) Subtype.val_injective (fun i => cA D (atPl (splitPrime (Bs.τ i)) 1))
    (fun i => ⟨GlobalTheory.BigDat.splitIdem_conj (ha i).1, by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, (ha i).2]⟩)
    (η := cA D (X.e t)) (by rw [he, map_sum]) _ _ _ (fun i u => (half_iff (Bs.τ i) (ha i).2 u).2)
    (fun i u => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact (half_iff (Bs.τ i) (ha i).2 u).1)
    (fun i u => -((Γ.V'.bas i).1ᵀ * Γ.V'.J.map (Bs.τ i) * u.map (piW ((Bs.τ i).comp D.sp.cm.sig)) * (Γ.W.J.map (Bs.τ i))ᵀ *
      (Γ.W.bas i).1))
    (fun i u x => by rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, neg_add])
    (fun i u => by
      congr 4
      exact Matrix.ext fun p q => (map_mul (piW ((Bs.τ i).comp D.sp.cm.sig)) _ _).trans (by
        rw [← GlobalTheory.FlipMatch.RowChart.piW_cA_eq, GlobalTheory.DualPairCheck.cA_cA, piW_atPl_one, one_mul]; rfl))
    (fun i z => by
      obtain ⟨g₁, h₁⟩ := dV' i
      obtain ⟨g₂, h₂⟩ := dW i
      obtain ⟨u, hu⟩ := exists_map_piW ((Bs.τ i).comp D.sp.cm.sig) ((g₁⁻¹).1 * (-z) * (g₂⁻¹).1)
      refine ⟨u, ?_⟩
      beta_reduce
      rw [hu, Matrix.mul_assoc _ _ (Γ.W.bas i).1, ← h₁, ← h₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv,
        Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, neg_neg])
    I' (fun i => GlobalTheory.BigNZ.isLagrModel_of_isLin (hI' i)) (hX.snd t)
    (fun x hx => by
      by_contra hn
      exact hx (if_neg fun h' => hn h'.1))
    Φ' (fun v => (hall v).2.1.1) (fun v hv => e2' v fun h' => hv ⟨v, h'⟩ rfl) (κ := ∏ i, lam i)
    (Finset.prod_ne_zero_iff.2 fun i _ => nlam i)
    (fun x hx => by
      refine Eq.trans ?_ (congrArg (_ * ·) (UpperTheory.stdSectionSecond_eq_prod_local D _ _ (hX.idem t) Bs.P Subtype.val Bs.τ hPw hinj (X.c t) (α t / β t)
        A.rank A' WW X.rA'.β X.rW.β hT.rank.symm x hx).symm)
      beta_reduce
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [e1' i]; exact eφ' i x)
  obtain ⟨L, rL, eL⟩ := UpperTheory.theta_transform_fock_model_eq_of_standard_char D Bs.ψ θ hψ hθ true A WW _ hT.rank.symm Γ.V Γ.W Γ.M h.JW h.JX hg.hM FA FW Bs.emb
    (fun w => by obtain ⟨τ, h1, h2, -, h4⟩ := h.cart w; exact ⟨τ, h1, by rw [h2]; simp, h4⟩) f₀ Φ nf₀
    (fun v => (hall v).1.1) ev (fun v => (hall v).1.2) (ef₀.symm ▸ hf)
  obtain ⟨L', rL', eL'⟩ := UpperTheory.theta_transform_fock_model_eq_of_standard_char D Bs.ψ θ hψ hθ false A' WW _ hT.rank.symm Γ.V' Γ.W Γ.M' h.JW₁ h.JX hg.hM' FA' FW Bs.emb
    (fun w => by obtain ⟨τ, h1, -, h3, h4⟩ := h.cart w; exact ⟨τ, h1, by rw [h3]; simp, h4⟩) f₁ Φ' nf₁
    (fun v => (hall v).2.1.1) ev' (fun v => (hall v).2.1.2) (ef₁.symm ▸ hf')
  rw [ef₀] at eL
  rw [ef₁] at eL'
  have pA : ∀ P, GlobalTheory.TripleAssembly.mapA Bs.ψ (finCongr hT.rank.symm) Bs Γ R Rf
      (GlobalTheory.SquareComm.fockF Bs.ψ θ true FA FW (X.f t) P) =
      R.p (L P) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) (fun v => Rf.p v (Φ v)) := fun P => by
    have := GlobalTheory.T.seesaw_weil_zeta_factor hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM 1
      (fun _ => L P) (fun _ => Φ) (fun _ => ⟨fun v => (hall v).1.1, ev⟩) (by
        rw [Fin.sum_univ_one]
        exact Submodule.subset_span ⟨L P, Φ, rL ▸ ⟨P, rfl⟩, fun v => (hall v).1.1, ev, rfl⟩)
    rwa [Fin.sum_univ_one, Fin.sum_univ_one, eL] at this
  have pB : ∀ P, GlobalTheory.TripleAssembly.mapB Bs.ψ (finCongr hT.rank.symm) Bs Γ R Rf
      (GlobalTheory.SquareComm.fockF Bs.ψ θ false FA' FW (X.f' t) P) =
      R.p' (L' P) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) (fun v => Rf.p' v (Φ' v)) := fun P => by
    have := GlobalTheory.T.seesaw_weil_zeta_archimedean hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM 1
      (fun _ => L' P) (fun _ => Φ') (fun _ => ⟨fun v => (hall v).2.1.1, ev'⟩) (by
        rw [Fin.sum_univ_one]
        exact Submodule.subset_span ⟨L' P, Φ', rL' ▸ ⟨P, rfl⟩, fun v => (hall v).2.1.1, ev', rfl⟩)
    rwa [Fin.sum_univ_one, Fin.sum_univ_one, eL'] at this
  have tA := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hψ hθ true A WW FA FW _ _ _ hA
  have tB := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hψ hθ false A' WW FA' FW _ _ _ hB
  obtain ⟨oA, oB⟩ := GlobalTheory.T.algF_map_mapA_and_mapB_eq_top hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨iA, iB⟩ := GlobalTheory.T.mapA_mapB_invariant_under_finite_group hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨lA, lB⟩ := GlobalTheory.T.seesaw_weil_local_factor_eq hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨fA, fB⟩ := GlobalTheory.T.seesaw_weil_archimedean_factor hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨dA, dB⟩ := GlobalTheory.T.seesaw_weil_unramified_factor hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  have ir := GlobalTheory.T.seesaw_weil_global_factor hH hPr D Bs.ψ θ hψ hθ A A' WW FA FA' FW _ _ hT _ _ hA hB _ Bs Γ Xc om om' h hTA hTB R Rf hM
  refine ⟨ModuleCat.of ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf), _, _, GlobalTheory.TripleAssembly.mapA Bs.ψ (finCongr hT.rank.symm) Bs Γ R Rf,
    GlobalTheory.TripleAssembly.mapB Bs.ψ (finCongr hT.rank.symm) Bs Γ R Rf,
    ⟨hA, hB, ir, ⟨tA.1, tA.2, oA, iA, lA, fA, dA⟩, ⟨tB.1, tB.2, oB, iB, lB, fB, dB⟩⟩, ?_⟩
  refine (em _).imp id fun hn => ?_
  obtain ⟨P, hP0⟩ := not_forall.1 hn
  obtain ⟨g, hg', eg⟩ : R.p (L P) ∈ (Γ.M'.Pol Bs.ψ Bs.emb).map R.p' := hM.real.quot'.onto ▸ Submodule.mem_top
  obtain ⟨P', rfl⟩ : g ∈ LinearMap.range L' := rL' ▸ hg'
  refine ⟨P, P', 1, hP0, ?_⟩
  rw [one_smul]
  refine (pA P).trans (Eq.trans ?_ (pB P').symm)
  rw [eg, funext fun v => (hall v).2.2]

end GlobalTheory.BotMatch

end
end
