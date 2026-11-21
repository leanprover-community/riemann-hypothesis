import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFamilyEstimateStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFamilyEstimate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GBigAtTiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemPrimeAwayFromMuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemPrimeAwayFromMu
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianFieldDataOfToricRatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianFieldDataOfToricRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataAbelian
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
namespace GlobalTheory.ThmAUpper
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ChiGrid in
theorem qn_not_mem_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ)
    (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → ∀ w : HeightOneSpectrum (𝓞 D.what₂.LL), p.R.mu w ≠ p.P.A3.A.μ0 →
      ((Qn d.G (p.R.mu w) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d _ hfit w hw
  classical
  obtain ⟨htw, hxi⟩ := xiH_twisted p w hw
  have hl : D.ntw.l (ex.nch.twI (D.plEq.symm w)) = D.what₂.places.resChar (D.plEq.symm w) :=
    (hfit.1.setting.1 _ htw).1
  have hQ := hfit.1.cond _ htw
  have hlev := p.charW.base.lev
  have key : ∀ PP ∈ twPl d.G (p.R.mu w),
      ((D.what₂.places.resChar (D.plEq.symm w) : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hlP
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hPP
    obtain ⟨hloc, hW0⟩ := hPP
    have hQt : PP ∈ p.R.toRealDat.toLevCh.Q (p.R.mu w) := hloc.resolve_left hW0
    have hS1 : PP.under (𝓞 D.host.F) ∉ S1 D := fun h => hW0 (by
      rw [d.G.pl.w_Q _ PP hQt h]
      exact Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem h))
    have hram : ¬ (p.R.toRealDat.toLevCh.xiH (p.R.mu w)).UnrAt PP := (hlev.Q_ram _ PP).2 (Or.inl hQt)
    rw [hxi] at hram
    by_cases hd : (p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w))).UnrAt PP
    · have hψ : ¬ (p.Tp.psi (D.plEq.symm w)).UnrAt PP := fun h => hram (hd.mul h)
      have hmem : PP ∈ ex.nch.Q (D.plEq.symm w) := by
        by_contra hn
        exact hψ (((p.Tp.psi_is _ htw).ram PP).2 hn)
      have hS0 : PP ∈ D.ntw.S0 (ex.nch.twI (D.plEq.symm w)) := D.ntw.twistExcludedPlaces_contains_residueChar _ (by rw [hl]; exact hlP)
      exact Finset.disjoint_left.1 hQ.2.1 hmem hS0
    · have hover : ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∨ ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        unfold Formalism.L2.Host.CharFrame.delAt at hd
        split_ifs at hd
        · by_contra h
          exact hd (p.R.C.isDel'.unr PP fun h' => h (Or.inr h'))
        · by_contra h
          exact hd (p.R.C.isDel.unr PP fun h' => h (Or.inl h'))
      apply hS1
      rw [S1_mem_OmF]
      rcases hover with h | h
      · right; right; left
        show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
        simpa using h
      · right; right; right
        show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
        simpa using h
  intro hmem
  rw [Qn, Nat.cast_prod] at hmem
  obtain ⟨PP, hPP, hin⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hmem
  have : NeZero PP.asIdeal := ⟨PP.ne_bot⟩
  have hq : (Ideal.absNorm (PP.asIdeal.under ℤ)).Prime := Nat.absNorm_under_prime PP.asIdeal
  have : PP.asIdeal.LiesOver (Ideal.span {((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : ℤ)}) :=
    Int.liesOver_span_absNorm PP.asIdeal
  rw [Ideal.absNorm_eq_pow_inertiaDeg' PP.asIdeal hq, Nat.cast_pow] at hin
  have hqw := w.isPrime.mem_of_pow_mem _ hin
  have hqP : ((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h : algebraMap ℤ (𝓞 D.host.E) ((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : ℤ) ∈ PP.asIdeal :=
      Ideal.absNorm_mem (PP.asIdeal.under ℤ)
    rw [eq_intCast, Int.cast_natCast] at h
    exact h
  have e := resChar_eq (D.plEq.symm w) hq (by rw [Equiv.apply_symm_apply]; exact hqw)
  exact key PP hPP (e ▸ hqP)
end GlobalTheory.ThmAUpper
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qn_not_mem_asIdeal_of_mu_ne : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → ∀ w : HeightOneSpectrum (𝓞 D.what₂.LL), p.R.mu w ≠ p.P.A3.A.μ0 → ((Qn d.G (p.R.mu w) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
  atlas_forward_decl _root_.GlobalTheory.ThmAUpper.qn_not_mem_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
noncomputable section
namespace GlobalTheory.ThmARatio
open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols Formalism.L2.Host
end GlobalTheory.ThmARatio
theorem GlobalTheory.ThmARatio.values_as_toric_sums_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL ((nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) * p.Tp.psi w) Λ → GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    ∃ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ∧
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ ∧ T₀ ≠ 0 ∧ Λd s = T₀ ∧
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) ∧
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) ∧ Λ s = T ψc := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d _ hfit _ hF hTor w hw i j s Λ Λd hs1 hs2 hΛ hΛd
  obtain ⟨_, _, hfd, hb, -⟩ := hF
  have hχ : fam d.G p.P.A3.A.μ0 i j (some (decide (D.what₂.places.resChar w = D.host.pde))) =
      nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) := by
    unfold fam GlobalTheory.FunObj.SqNum.delOf Formalism.L2.Host.CharFrame.delAt
    by_cases h : D.what₂.places.resChar w = D.host.pde
    · simp only [h, decide_true, cond_true, if_true]
    · simp only [h, decide_false, cond_false, if_false]
  obtain ⟨T₀, ⟨hv, h0⟩, hne, hL, -⟩ := hTor i j s hs1 hs2 (some (decide (D.what₂.places.resChar w = D.host.pde)))
  rw [hχ] at hv h0 hL
  have hP := p.Tp.psi_is w hw
  obtain ⟨a, ha⟩ := hP.ord
  have hQ := (GlobalTheory.ToricDenom.placesBelow_splitCoprimeConductor_of_admissible (hfit.1.cond w hw) (𝔣 := GlobalTheory.FunObj.SqNum.condF d.G.pl) fun P h =>
    (hfit.1.list _ (hfit.1.setting.inW1 hw)).1 P (GlobalTheory.ThmARatio.dvd_cond0 d.G.pl _ h)).1
  obtain ⟨ψc, T, h1, h2, h3⟩ := GlobalTheory.ThmARatio.twisted_value hfd.2.2.2.2.2.2.1 hfd.2.2.1 hs1 hb hQ hv
    (pow_ne_zero a (D.what₂.places.resChar_prime w).ne_zero) ha hP.triv hP.tame hP.ram hΛ
  exact ⟨T₀, ψc, T, hv, h0, hne, (hL Λd hΛd).symm, h1, h2, h3⟩
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_ratio_field_data_conjugate_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL ((nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) * p.Tp.psi w) Λ → GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    ∃ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ∧
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ ∧ T₀ ≠ 0 ∧ Λd s = T₀ ∧
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) ∧
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) ∧ Λ s = T ψc := by
  atlas_forward_decl _root_.GlobalTheory.ThmARatio.values_as_toric_sums_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
noncomputable section
namespace GlobalTheory.ThmAMove
open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems
variable {D : D7}
private theorem val_pos_iff_pz (w : D.what₂.places.Pl) (y : D.what₂.LL) :
    0 < D.what₂.places.val w y ↔ (D.plEq w).valuation D.what₂.LL y < 1 := by
  by_cases hy : y = 0
  · simp [hy]
  have h0 : (D.plEq w).valuation D.what₂.LL y ≠ 0 := by simpa using hy
  rw [D.val_eq w y hy, vAdd, ← WithZero.log_lt_log h0 one_ne_zero, WithZero.log_one]
  norm_cast
  omega
private theorem val_zero_iff_pz (w : D.what₂.places.Pl) (y : D.what₂.LL) :
    D.what₂.places.val w y = 0 ↔ (D.plEq w).valuation D.what₂.LL y = 1 := by
  by_cases hy : y = 0
  · simp [hy]
  have h0 : (D.plEq w).valuation D.what₂.LL y ≠ 0 := by simpa using hy
  rw [D.val_eq w y hy, vAdd]
  norm_cast
  rw [neg_eq_zero]
  exact ⟨fun h => by rw [← WithZero.exp_log h0, h, WithZero.exp_zero], fun h => by rw [h, WithZero.log_one]⟩
private theorem val_resChar_lt_pz (w : D.what₂.places.Pl) :
    (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) < 1 := by
  rw [← val_pos_iff_pz, D.what₂.places.val_resChar w]
  exact_mod_cast D.what₂.places.ramIdx_pos w
private theorem exists_place_pz (C : NChoice D) (w w' : D.what₂.places.Pl) (hw' : LiesUnder D (C.twI w) w')
    (ι : ℂ →+* Kbar D.ntw (C.twI w))
    (hι : ∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar D.ntw (C.twI w) (D.ntw.emb0 (C.twI w) x))
    (jk : FractionRing (D.ntw.Ok (C.twI w) (C.k' w)) →+* Kbar D.ntw (C.twI w))
    (hjk : jk.comp (BlochKatoReduction.Gen.kMap D.ntw (C.twI w) (C.k' w)) = algebraMap _ (Kbar D.ntw (C.twI w))) :
    ∃ (je : FractionRing (C.Oe w) →+* Kbar D.ntw (C.twI w)) (A : ValuationSubring (Kbar D.ntw (C.twI w))) (g : ℂ ≃+* ℂ),
      (∀ x, je (C.kMapE w x) = jk x) ∧
      (∀ x y, A.valuation (je x) = A.valuation (je y) → ∃ u : (C.Oe w)ˣ, x = algebraMap _ _ (u : C.Oe w) * y) ∧
      (∀ y, (D.plEq w).valuation D.what₂.LL y = 1 → A.valuation (je (C.embW w y)) = 1) ∧
      (∀ x : D.LL0, g (D.what₂.embLL x) = D.what₂.embLL x) ∧
      ∀ y, (D.plEq w').valuation D.what₂.LL y = 1 → A.valuation (ι (g (D.what₂.embLL y))) = 1 := by
  haveI := C.Oe_fin w
  haveI := D.galLL
  obtain ⟨je, hje⟩ := exists_ext (C.Oe_inj w) jk
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing (je.comp (algebraMap (C.Oe w) (FractionRing (C.Oe w))))
  have hu : ∀ a : C.Oe w, A.valuation (je (algebraMap _ _ a)) = 1 → IsUnit a := fun a h =>
    hloc.1 a ((A.valuation_eq_one_iff ⟨_, hA a⟩).2 h)
  have hα : ∀ y, (D.plEq w).valuation D.what₂.LL y = 1 → A.valuation (je (C.embW w y)) = 1 := by
    have key : ∀ y, (D.plEq w).valuation D.what₂.LL y = 1 → A.valuation (je (C.embW w y)) ≤ 1 := fun y hy => by
      obtain ⟨a, ha⟩ := (C.embW_w w y).1 ((val_zero_iff_pz w y).2 hy).ge
      rw [← ha, A.valuation_le_one_iff]
      exact hA a
    intro y hy
    refine le_antisymm (key y hy) ?_
    have h1 := key y⁻¹ (by rw [map_inv₀, hy, inv_one])
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    rwa [map_inv₀, map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 (by simpa using hy0))] at h1
  have hp := D.what₂.places.resChar_prime w
  have hl : A.valuation ((D.what₂.places.resChar w : ℕ) : Kbar D.ntw (C.twI w)) < 1 := by
    refine lt_of_le_of_ne ((A.valuation_le_one_iff _).2 (natCast_mem A _)) fun h => ?_
    obtain ⟨u, hu'⟩ := hu ((D.what₂.places.resChar w : ℕ) : C.Oe w) (by rwa [map_natCast, map_natCast])
    have h1 : 0 ≤ D.what₂.places.val w (((D.what₂.places.resChar w : ℕ) : D.what₂.LL)⁻¹) :=
      (C.embW_w w _).2 ⟨(u⁻¹ : (C.Oe w)ˣ), by rw [map_units_inv, hu', map_inv₀, map_natCast, map_natCast]⟩
    have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have h2 := (D.what₂.places.val w).map_mul ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)
      (((D.what₂.places.resChar w : ℕ) : D.what₂.LL)⁻¹)
    rw [mul_inv_cancel₀ hne, AddValuation.map_one] at h2
    exact absurd h2 (add_pos_of_pos_of_nonneg ((val_pos_iff_pz w _).2 (val_resChar_lt_pz w)) h1).ne
  have hl0 : ((D.what₂.places.resChar w : ℕ) : Kbar D.ntw (C.twI w)) ≠ 0 := by
    rw [← map_natCast ι, map_ne_zero]
    exact Nat.cast_ne_zero.2 hp.ne_zero
  let f0 : D.ntw.O0 (C.twI w) →+* Kbar D.ntw (C.twI w) := (toBar D.ntw (C.twI w)).comp (algebraMap _ _)
  have hf0 : ∀ r, f0 r ∈ A := fun r => by
    have e1 := GlobalTheory.ToricRational.toBar_algebraMap (X := D.ntw) (C.twI w) r
    have e2 := DFunLike.congr_fun hjk (algebraMap (D.ntw.O (C.twI w)) _ (algebraMap _ _ r))
    rw [RingHom.comp_apply, BlochKatoReduction.Gen.kMap, IsFractionRing.lift_algebraMap, RingHom.comp_apply, ← hje] at e2
    replace e2 := e2.trans e1.symm
    have e3 := hA (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) _ (algebraMap (D.ntw.O (C.twI w)) _ (algebraMap _ _ r)))
    show toBar D.ntw (C.twI w) (algebraMap _ _ r) ∈ A
    rw [← e2]
    simpa [IsFractionRing.map] using e3
  obtain ⟨σ, hσ⟩ := exists_aut_centre A D.LL0 (ι.comp D.what₂.embLL) (D.plEq w') fun x => by
    have hi : IsIntegral (D.ntw.O0 (C.twI w)) (D.ntw.emb0 (C.twI w) x) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom _) (D.ntw.emb0 (C.twI w)) (RingHom.ext_int _ _) x.isIntegral_coe
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    have e1 : (ι.comp D.what₂.embLL) ((x : D.LL0) : D.what₂.LL) = f0 a := by
      rw [RingHom.comp_apply, hι, ← ha]; rfl
    rw [e1, ← mem_max_iff A f0 hf0 hl0 hl, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.what₂.LL), ← val_pos_iff_pz]
    refine Iff.trans ⟨fun h => ⟨a, h, ha⟩, fun ⟨y, hy, e⟩ => ?_⟩ (hw' x)
    rwa [← IsFractionRing.injective _ (FractionRing (D.ntw.O0 (C.twI w))) (e.trans ha.symm)]
  haveI : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.symm
  obtain ⟨g, hg⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq D.what₂.embLL (D.what₂.embLL.comp σ.toRingEquiv.toRingHom)
  refine ⟨je, A, g, hje, fun x y h => exists_unit A je hA hu h, hα, fun x => ?_, fun y hy => ?_⟩
  · rw [hg]
    exact congrArg D.what₂.embLL (σ.commutes x)
  · rw [hg]
    exact unit_of_centre A (ι.comp (D.what₂.embLL.comp σ.toRingEquiv.toRingHom)) _ hσ y hy
private theorem exists_side_pz (C : NChoice D) (w : D.what₂.places.Pl)
    (hw : LiesUnder D (C.twI w) w ∨ LiesUnder D (C.twI w) (D.what₂.places.conj w)) : ∃ b : Bool,
    ∀ (ι : ℂ →+* Kbar D.ntw (C.twI w))
      (_ : ∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar D.ntw (C.twI w) (D.ntw.emb0 (C.twI w) x))
      (jk : FractionRing (D.ntw.Ok (C.twI w) (C.k' w)) →+* Kbar D.ntw (C.twI w))
      (_ : jk.comp (BlochKatoReduction.Gen.kMap D.ntw (C.twI w) (C.k' w)) = algebraMap _ (Kbar D.ntw (C.twI w))),
    ∃ (je : FractionRing (C.Oe w) →+* Kbar D.ntw (C.twI w)) (A : ValuationSubring (Kbar D.ntw (C.twI w))) (g : ℂ ≃+* ℂ),
      (∀ x, je (C.kMapE w x) = jk x) ∧
      (∀ x y, A.valuation (je x) = A.valuation (je y) → ∃ u : (C.Oe w)ˣ, x = algebraMap _ _ (u : C.Oe w) * y) ∧
      (∀ t ∈ (Formalism.L2.Host.embLL0 D).fieldRange, starRingEnd ℂ t ∈ (Formalism.L2.Host.embLL0 D).fieldRange → g t = t) ∧
      ∀ z, A.valuation (je (C.embW w z)) = A.valuation (atSide D.ntw b ι (g (D.what₂.embLL z))) := by
  have hp := (D.what₂.places.resChar_prime w).ne_zero
  rcases hw with hw | hw
  · refine ⟨true, fun ι hι jk hjk => ?_⟩
    obtain ⟨je, A, g, h1, h2, h3, h4, h5⟩ := exists_place_pz C w w hw ι hι jk hjk
    refine ⟨je, A, g, h1, h2, ?_, val_eq_of_unit A (je.comp (C.embW w)) (ι.comp (g.toRingHom.comp D.what₂.embLL)) _ hp
      (val_resChar_lt_pz w).ne h3 h5⟩
    rintro _ ⟨x, rfl⟩ -
    exact h4 x
  · refine ⟨false, fun ι hι jk hjk => ?_⟩
    obtain ⟨je, A, g, h1, h2, h3, h4, h5⟩ := exists_place_pz C w _ hw ι hι jk hjk
    let c : ℂ ≃+* ℂ := Complex.conjAe.toRingEquiv
    have hc : ∀ t, c t = starRingEnd ℂ t := fun _ => rfl
    refine ⟨je, A, (c.trans g).trans c, h1, h2, ?_, val_eq_of_unit A (je.comp (C.embW w))
      ((atSide D.ntw false ι).comp (((c.trans g).trans c).toRingHom.comp D.what₂.embLL)) _ hp
      (val_resChar_lt_pz w).ne h3 fun y hy => ?_⟩
    · rintro t - ⟨x, hx⟩
      show c (g (c t)) = t
      rw [hc t, ← hx]
      refine (congrArg c (h4 x)).trans ?_
      show starRingEnd ℂ (Formalism.L2.Host.embLL0 D x) = t
      rw [hx, Complex.conj_conj]
    · letI := D.starLL
      have h6 := h5 (star y) (by rw [← val_zero_iff_pz, D.conj_val, star_star, val_zero_iff_pz, hy])
      rw [D.starLL_cx] at h6
      show A.valuation (ι (starRingEnd ℂ (starRingEnd ℂ (g (starRingEnd ℂ (D.what₂.embLL y)))))) = 1
      rwa [Complex.conj_conj]
private theorem emb_mem_pz (σ : D.host.E →+* ℂ) (x : D.host.E) : σ x ∈ (Formalism.L2.Host.embLL0 D).fieldRange := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  let _ : Algebra D.host.E ℂ := D.host.φ₀.toAlgebra
  have : IsScalarTower ℚ D.host.E ℂ := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast D.host.φ₀ q).symm
  have e : D.host.φ₀ (σ.toRatAlgHom.restrictNormal D.host.E x) = σ x := σ.toRatAlgHom.restrictNormal_commutes D.host.E x
  rw [← e, ← D.embE_φ₀]
  exact ⟨⟨_, D.hostField_le_fixedField _⟩, rfl⟩
section Point
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF}
private theorem almostIn_pz (h : GridFit p G) (i j : Fin D.R.m) (l : ℕ) :
    GlobalTheory.GalChar.AlmostIn (Formalism.L2.Host.embLL0 D) (nuH G p.P.A3.A.μ0 i j * p.R.C.delAt l) := by
  unfold nuH
  rw [GlobalTheory.ThmAUpper.xiH_base p, mul_one, div_eq_mul_inv]
  refine ((GlobalTheory.GalChar.almostIn_of_valuesIn (h.frame.mu0 j)).mul
    (GlobalTheory.GalChar.almostIn_of_valuesIn (h.field.values _ (by omega) (by omega))).inv).mul ?_
  unfold Formalism.L2.Host.CharFrame.delAt
  split_ifs
  exacts [GlobalTheory.GalChar.almostIn_of_valuesIn h.frame.del', GlobalTheory.GalChar.almostIn_of_valuesIn h.frame.del]
private theorem isSet_pz (h : GridFit p G) {w : D.what₂.places.Pl} (hw : TwistedAt D w) :
    IsFinSetSplitPlacesCoprimeConductor (GlobalTheory.FunObj.SqNum.condF G.pl) (belowSet (ex.nch.Q w)) := by
  refine (placesBelow_splitCoprimeConductor_of_admissible (h.cond w hw) fun P hP => (h.list _ (h.setting.inW1 hw)).1 P ?_).1
  obtain ⟨v, hv, hd⟩ := (Prime.dvd_finset_prod_iff (below P).prime _).1 hP
  have e : below P = v := HeightOneSpectrum.ext
    ((v.isMaximal.eq_of_le (below P).isPrime.ne_top (Ideal.le_of_dvd ((below P).prime.dvd_of_dvd_pow hd))).symm)
  subst e
  rcases G.pl.mem_S0_of_sum_eq.1 hv with h0 | h1
  · refine Dvd.dvd.mul_left ?_ _
    have : below (G.pl.w G.pl.v0) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
    show _ ∣ (below (G.pl.w G.pl.v0)).asIdeal
    rw [this, ← h0]
  · refine Dvd.dvd.mul_right (dvd_pow (Ideal.dvd_span_singleton.2 ?_) two_ne_zero) _
    have := (GlobalTheory.ChiGrid.S1_mem_OmF D).1 h1
    simp only [Nat.cast_mul, (below P).isPrime.mul_mem_iff_mem_or_mem, or_assoc]
    exact this
end Point
theorem _root_.GlobalTheory.T.toric_ratio_field_data_cm_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    ∀ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) →
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ → T₀ ≠ 0 →
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) →
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) → ∀ z : D.what₂.LL, D.what₂.embLL z * T₀ = T ψc → (∃ ι : ℂ →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w),
        (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = GlobalTheory.ToricDenom.toBar D.ntw (ex.nch.twI w) (D.ntw.emb0 (ex.nch.twI w) x)) ∧
        ∀ b : Bool, ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (jk : FractionRing (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) (c : ℤ),
            D.ntw.sideL (ex.nch.twI w) lam = b ∧ IsCoprime c (D.ntw.l (ex.nch.twI w) : ℤ) ∧
            jk.comp (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)) = algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) ∧
            ∀ a : ℤ, jk (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) *
                GlobalTheory.ToricDenom.atSide D.ntw b ι T₀ =
              jk (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) * GlobalTheory.ToricDenom.atSide D.ntw b ι (T (ψc ^ (c * a)))) →
      ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (a : ℤ) (u : (ex.nch.Oe w)ˣ), IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) ∧
        ex.nch.embW w z * ex.nch.kMapE w (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) =
          algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)) (u : ex.nch.Oe w) *
            ex.nch.kMapE w (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w)
              (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d hp hfit hG hF w hw i j s hs1 hs2 T₀ ψc T hv h0 h0ne hψ hT' z hz hread
  obtain ⟨hcm, -, hfd, hbc, -⟩ := hF
  obtain ⟨ι, hι, hread⟩ := hread
  obtain ⟨b, hb⟩ := exists_side_pz ex.nch w (hfit.1.setting.1 w hw).2
  obtain ⟨lam, jk, c, -, hc, hjk, hid⟩ := hread b
  obtain ⟨je, A, g, h1, h2, h3, h4⟩ := hb ι hι jk hjk
  have hU : UnramFin D.host.E := hfd.2.2.1
  have hφ : IsCMType (GlobalTheory.FunObj.SqNum.cmPhi D) := hfd.2.2.2.2.2.2.1
  generalize hχ : nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) = χ at hv h0 hT'
  have hal : GlobalTheory.GalChar.AlmostIn (Formalism.L2.Host.embLL0 D) χ := hχ ▸ almostIn_pz hfit.1 i j _
  have hfin : Finite (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅)) := by
    rw [condQ, Finset.prod_empty, mul_one]; exact h0.1
  have hval : ∀ y, (finPart χ y : ℂ) ∈ (Formalism.L2.Host.embLL0 D).fieldRange :=
    GlobalTheory.ToricRational.finPart_mem hv.2.2.1 (GlobalTheory.ToricRational.condQ_ne_bot hbc.1 ∅)
      (OrderUnits.finPart_eq_one _ _ _ hφ s _ _ ∅ χ hU hbc (fun _ h => absurd h (Finset.notMem_empty _)) hv) _ emb_mem_pz
      (Filter.eventually_cofinite.1 hal).toFinset fun P hP => by simpa using hP
  have hlam : ∀ y, g (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s y) = GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s y := fun y => by
    have hm : ((modF y ^ s : ℝ) : ℂ) ∈ (Formalism.L2.Host.embLL0 D).fieldRange := by
      rw [Complex.ofReal_pow]
      exact pow_mem (GlobalTheory.ToricRational.modF_mem _ y) s
    refine h3 _ (mul_mem (hval y) hm) ?_
    rw [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF, map_mul, Complex.conj_ofReal, ← Complex.inv_eq_conj (show ‖(finPart χ y : ℂ)‖ = 1 from hv.1 _)]
    exact mul_mem (inv_mem (hval y)) hm
  haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by have := hfd.2.2.2.2.2.1; omega)
  let τ₀ : D.what₂.Tau := Classical.arbitrary _
  let δ : D.host.K := ⟨D.host.sqrtMinusD, GlobalTheory.Mem.Col2.HostK.sqrt_mem D.host⟩
  have hδ : δ ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa using Formalism.BasicNotions.Host.sqrtMinusD_sq D.host)
  obtain ⟨ζ, hζ, hg⟩ := ratio_conj CompanionTheory.FamInh.globalArtin hG D.host.E D.host.K D.host.d δ _ _ _ s _ _ _ χ hU (Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D)
    hfd.1.pos hδ hφ (fun τ => GlobalTheory.RowEx.RatioField.cmPhi_comp_eq hfd τ τ₀) hs1
    (fun τ => (GlobalTheory.FunObj.SqNum.Model.kap_add D 1 i j τ hs2).2) hbc (isSet_pz hfit.1 hw) hv h0 hT' g
    (fun τ x => h3 _ (emb_mem_pz _ x) (emb_mem_pz ((starRingEnd ℂ).comp _) x)) hlam ψc
  obtain ⟨n, hn⟩ := (p.Tp.psi_is w hw).ord
  rw [ex.nch.twI_l] at hc ⊢
  obtain ⟨a, ha, he⟩ := exists_exponent ψc (n := n) (D.what₂.places.resChar_prime w) (fun q => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← hψ]
    exact congrArg (fun ξ => finPart ξ y) hn) g hc
  have hid' := hid a
  rw [← he] at hid'
  have hz' : T ψc / T₀ = D.what₂.embLL z := by rw [← hz, mul_div_cancel_right₀ _ h0ne]
  have hT : T (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.conjChar g ψc) = ζ * g (D.what₂.embLL z) * T₀ := by
    rw [← hz', hg]
    field_simp
  have hζ1 : A.valuation (atSide D.ntw b ι ζ) = 1 := by
    obtain ⟨m, hm, hm'⟩ := isOfFinOrder_iff_pow_eq_one.1 hζ
    refine (pow_eq_one_iff_of_nonneg zero_le hm.ne').1 ?_
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hm', Units.val_one, map_one, map_one]
  obtain ⟨u, hu⟩ := h2 (ex.nch.embW w z * ex.nch.kMapE w (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)
      (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ))) (ex.nch.kMapE w (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w)
      (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a)))) (by
    have e := hid'.trans (congrArg (fun t => _ * atSide D.ntw b ι t) hT)
    rw [map_mul, ← mul_assoc] at e
    have e' := mul_right_cancel₀ ((map_ne_zero _).2 h0ne) e
    rw [map_mul, h1, h1, e', map_mul, map_mul, map_mul, map_mul, hζ1, one_mul, h4, mul_comm])
  exact ⟨lam, a, u, ha, hu⟩
end GlobalTheory.ThmAMove
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
noncomputable section
namespace GlobalTheory.ThmAUpper.Read
section Record
open GlobalTheory.ToricDenom GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}
  {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}
end Record
end GlobalTheory.ThmAUpper.Read
namespace GlobalTheory.ThmAUpper
open Read GlobalTheory.ToricDenom GlobalTheory.FunObj.SqNum in
theorem read_twisted_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    ∀ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) →
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ → T₀ ≠ 0 →
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) →
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) → (∃ ι : ℂ →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w),
        (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = GlobalTheory.ToricDenom.toBar D.ntw (ex.nch.twI w) (D.ntw.emb0 (ex.nch.twI w) x)) ∧
        ∀ b : Bool, ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (jk : FractionRing (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) (c : ℤ),
            D.ntw.sideL (ex.nch.twI w) lam = b ∧ IsCoprime c (D.ntw.l (ex.nch.twI w) : ℤ) ∧
            jk.comp (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)) = algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) ∧
            ∀ a : ℤ, jk (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) *
                GlobalTheory.ToricDenom.atSide D.ntw b ι T₀ =
              jk (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) * GlobalTheory.ToricDenom.atSide D.ntw b ι (T (ψc ^ (c * a)))) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d hp hfit _ hF w hw i j s hs1 hs2 T₀ ψc T _ h0 _ hψ hT'
  obtain ⟨_, _, -, hb, -⟩ := hF
  obtain ⟨-, ι, hι, -, hall⟩ := hfit.1.list _ (hfit.1.setting.inW1 hw)
  refine ⟨ι, hι, fun b => ?_⟩
  have hi := i.2
  let a : Fin D.R.m := ⟨D.R.m - i - 1, by omega⟩
  have ha : a.1 + 1 = D.R.m - i := by simp only [a]; omega
  have hsN : s ≤ BlochKatoReduction.Gen.NFun D.R + 1 := by
    have h3 : halfRank D i j ≤ GlobalTheory.ChiGrid.bigN D := by
      have a : GlobalTheory.ChiGrid.rankV D (i + 1) (j + 1) ≤ GlobalTheory.ChiGrid.bigN D := by
        have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
        have h2 : (i + 1) * GlobalTheory.ChiGrid.sLen D ≤ D.R.m * GlobalTheory.ChiGrid.sLen D := Nat.mul_le_mul_right _ i.2
        simp only [GlobalTheory.ChiGrid.rankV, GlobalTheory.ChiGrid.bigN, Ranks.r, mul_add] at *
        omega
      have e : GlobalTheory.ChiGrid.rankV D (i + 1) (j + 1) = GlobalTheory.ChiGrid.rankV D i j + D.R.t + GlobalTheory.ChiGrid.sLen D := by
        simp only [GlobalTheory.ChiGrid.rankV]; ring
      unfold halfRank; omega
    have h12 : BlochKatoReduction.Gen.NFun D.R = GlobalTheory.ChiGrid.bigN D := GlobalTheory.LamTie.nFun_eq_bigN D
    omega
  obtain ⟨lam, hlam, -, hth⟩ := hall j a s b hs1 hsN
  have e1 : GlobalTheory.LamTie.cond0 D.host (lamOf d.G).w0 = condF d.G.pl := cond0_eq d.G hb
  have e2 : (lamOf d.G).lam0 (D.ntw.l (ex.nch.twI w)) j a =
      nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) := by
    rw [lambdaGrid_apply, ha, ex.nch.twI_l, nuH, xiH_base p, mul_one, div_mul_eq_mul_div]
  have e3 : GlobalTheory.LamTie.phi D.host ∘ D.eTau = cmPhi D := rfl
  have e4 : (lamOf d.G).kap j a s ∘ D.eTau = kap D 1 i j s := by
    funext τ
    simp only [Function.comp, GlobalTheory.LamTie.LamDat.kap, lamOf, kap, Formalism.L2.Host.eExp, Equiv.symm_apply_apply, ha]
    have : (GlobalTheory.ChiGrid.num D 1 τ).e (j + 1) = ⌊(D.hc τ).e j⌋ := by
      show GlobalTheory.SignedHC.GridData.extend 1 (D.hc τ).e (j + 1) = _
      simp [GlobalTheory.SignedHC.GridData.extend]
    rw [this]
  rw [e1, e2] at hth
  obtain ⟨u, -, hth⟩ := hth
  obtain ⟨_, π, t, hπ, ht, hδ⟩ := hth _ (hfit.1.cond w hw)
  obtain ⟨_, π0, t0, -, ht0, hδ0⟩ := hth ∅ ⟨by simp, by simp, by simp⟩
  replace ht := fun q => isClassTerm_reindex D.eTau (ht q)
  replace ht0 := fun q => isClassTerm_reindex D.eTau (ht0 q)
  rw [e3, e4] at ht ht0
  have e5 : condQ (condF d.G.pl) (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E)))) = condF d.G.pl := by
    simp [condQ, belowSet]
  have s0 := sum_th_eq ht0 hδ0 (t := T₀) (by rw [e5]; exact h0)
  obtain ⟨J, hJ⟩ := GlobalTheory.ToricDistribution.exists_emb D.ntw (ex.nch.twI w) (ex.nch.k' w)
  obtain ⟨e, he, hchar⟩ := exists_pow_char hfit.1.psi hw (hp.ties.psiVal w hw) (atSide D.ntw b ι) J
  have hc : condQ (condF d.G.pl) (belowSet (ex.nch.Q w)) ≠ ⊥ :=
    mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have key : ∀ a : ℤ, J (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (ex.nch.psi' w ^ a)) =
      u * atSide D.ntw b ι (T (ψc ^ (e * a))) := fun a => by
    refine thEval_eq_twisted hJ (fun q => ?_) ht hδ (hT' _)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 := hchar hc π hπ y
    have h2 : ∀ (x : (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w))ˣ), J (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _ (x ^ a : _ˣ)) =
        J (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _ x) ^ a := fun x => by
      have := congrArg Units.val (map_zpow (Units.map (J.comp
        (algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) _)).toMonoidHom) x a)
      rw [Units.val_zpow_eq_zpow_val] at this
      exact this
    rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, h2, ← h1, hψ, zpow_mul, Units.val_zpow_eq_zpow_val _ a, map_zpow₀]
  refine ⟨lam, J, if b then e else -e, hlam, by cases b <;> simp [he, he.neg_left], RingHom.ext hJ, fun a => ?_⟩
  rw [hJ, s0, hlam]
  cases b
  · have : BlochKatoReduction.Gen.psiAt false (ex.nch.psi' w ^ a) = ex.nch.psi' w ^ (-a) := by simp [BlochKatoReduction.Gen.psiAt]
    rw [this, key]
    simp only [Bool.false_eq_true, if_false, mul_neg, neg_mul]
    ring
  · have : BlochKatoReduction.Gen.psiAt true (ex.nch.psi' w ^ a) = ex.nch.psi' w ^ a := rfl
    rw [this, key]
    simp only [if_true]
    ring
end GlobalTheory.ThmAUpper
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_ratio_field_data_abelian_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    ∀ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) →
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ → T₀ ≠ 0 →
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) →
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) → (∃ ι : ℂ →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w),
        (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = GlobalTheory.ToricDenom.toBar D.ntw (ex.nch.twI w) (D.ntw.emb0 (ex.nch.twI w) x)) ∧
        ∀ b : Bool, ∃ (lam : D.ntw.abelian₂ (ex.nch.twI w)) (jk : FractionRing (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) →+* GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) (c : ℤ),
            D.ntw.sideL (ex.nch.twI w) lam = b ∧ IsCoprime c (D.ntw.l (ex.nch.twI w) : ℤ) ∧
            jk.comp (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w)) = algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (GlobalTheory.ToricDenom.Kbar D.ntw (ex.nch.twI w)) ∧
            ∀ a : ℤ, jk (BlochKatoReduction.Gen.thEval D.ntw (ex.nch.twI w) (ex.nch.Q w) lam (ex.nch.k' w) (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (ex.nch.twI w) lam) (ex.nch.psi' w ^ a))) *
                GlobalTheory.ToricDenom.atSide D.ntw b ι T₀ =
              jk (BlochKatoReduction.Gen.kMap D.ntw (ex.nch.twI w) (ex.nch.k' w) (∑ δ, D.ntw.th (ex.nch.twI w) ∅ lam δ)) * GlobalTheory.ToricDenom.atSide D.ntw b ι (T (ψc ^ (c * a)))) := by
  atlas_forward_decl _root_.GlobalTheory.ThmAUpper.read_twisted_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
noncomputable section
namespace GlobalTheory.ThmAUpper
theorem val_bound_twisted_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) →
  ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ) (z : D.what₂.LL), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) * p.Tp.psi w) Λ →
    GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    D.what₂.embLL z * Λd s = Λ s →
    (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) ≤ (Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) : ℝ) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ 2 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d hp hfit hG hF hT w hw i j s Λ Λd z hs1 hs2 hΛ hΛd hz
  obtain ⟨T₀, ψc, T, hv, h0, h0ne, hd, hψ, hT', hΛs⟩ := _root_.GlobalTheory.T.toric_ratio_field_data_conjugate_alt p CF d hp hfit hG hF hT w hw i j s Λ Λd hs1 hs2 hΛ hΛd
  obtain ⟨lam, a, u, ha, he⟩ := _root_.GlobalTheory.T.toric_ratio_field_data_cm_alt p CF d hp hfit hG hF w hw i j s hs1 hs2 T₀ ψc T hv h0 h0ne hψ hT' z
    (by rw [← hd, hz, hΛs]) (_root_.GlobalTheory.T.toric_ratio_field_data_abelian_alt p CF d hp hfit hG hF w hw i j s hs1 hs2 T₀ ψc T hv h0 h0ne hψ hT')
  obtain ⟨N0, hN⟩ := hfit.1.powers
  exact GlobalTheory.T.twistedThetaValue_valuation_le_div_sq ex.nch w N0 lam a u z (hN w hw a ha) he
end GlobalTheory.ThmAUpper
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_abelian_field_data_of_toric_ratio_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.PointConditions' → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) →
  ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ) (z : D.what₂.LL), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w) * p.Tp.psi w) Λ →
    GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    D.what₂.embLL z * Λd s = Λ s →
    (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) ≤ (Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) : ℝ) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ 2 := by
  atlas_forward_decl _root_.GlobalTheory.ThmAUpper.val_bound_twisted_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
noncomputable section
namespace GlobalTheory.ThmAUpper
theorem thmA_upper_alt : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint →
    (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → FieldDat → TorEx →
    (_root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) := by
  intro hG hS hdl hF hT
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono (_root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hdl hF) (_root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hdl hT)) ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH hp hd
  refine ⟨hd, fun ⟨hf, ht⟩ w hw => ⟨_root_.GlobalTheory.T.qn_not_mem_asIdeal_of_mu_ne p CF d hp hd w hw, fun l hl hlw i j s Λ Λd z hs1 hs2 hΛ hΛd hz => ?_⟩⟩
  have hw' : D.plEq (D.plEq.symm w) = w := D.plEq.apply_symm_apply w
  have hl' : D.what₂.places.resChar (D.plEq.symm w) = l := resChar_eq _ hl (by rw [hw']; exact hlw)
  have key := _root_.GlobalTheory.T.cm_abelian_field_data_of_toric_ratio_alt p CF d hp hd hG hf ht (D.plEq.symm w) (xiH_twisted p w hw).1 i j s Λ Λd z hs1 hs2
    (by rw [← nuH_twisted p d.G w hw]; exact hΛ) (by rw [hl']; exact hΛd) hz
  rw [hw', hl'] at key
  exact key
end GlobalTheory.ThmAUpper
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_ratio_family_estimate' : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → FieldDat → TorEx → (_root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) := by
  atlas_forward_decl _root_.GlobalTheory.ThmAUpper.thmA_upper_alt
end
end
