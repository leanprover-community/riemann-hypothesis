import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSignatureOfGramEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomInfinityExponentsGapLargeGrids
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleFinitePlacesUnramOrSplitStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotDict

theorem fst_isFinF : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (hA : X.rA.IsStd) (hW : X.rW.IsStd), X.Is ψ θ α β νH S → ∀ t, IsFinF ψ θ true (GlobalTheory.BotDict.stdFr A hA.1) (GlobalTheory.BotDict.stdFr WW hW.1) (X.f t) := by
  intro D T A A' WW X ψ θ α β νH S hA hW hX t
  have hv := hX.isVac
  have hν : Formalism.L2.Theta.IsHeckeChar D (α t / β t) := by
    have h := (hX.weil t).hecT
    rw [← inv_div]
    refine ⟨?_, fun x => ?_⟩
    · exact continuous_inv.comp h.1
    · show ((β t / α t) _)⁻¹ = 1
      rw [h.2 x, inv_one]
  have hI : X.ideal S t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_
    rw [Ideal.zero_eq_bot]
    exact w.ne_bot
  obtain ⟨f₁, h1, h1t⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW (α t / β t) (X.e t) (S t) (X.ideal S t) X.vac
    hX.rigA hX.rigW hν (hX.idem t) hI hv
  have heq : X.f t = f₁ := by
    obtain ⟨⟨Tm, hT⟩, hall⟩ := hX.fst t
    rw [hall Tm hT, h1.2 Tm hT]
  have hft : IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (X.f t) := heq ▸ h1t
  refine ⟨hft, fun τ => ?_⟩
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.idem t)
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hv.1.1.1 hv.2.inf ho.infPart_eq ho.conj.infPart_eq
    (hX.fst t) hv.2.theta hft (hv.2.fock τ)
  rw [cart_frSgn_true_stdFr, cart_stdFr]
  have e1 : X.rA.s τ = 1 := (hA.2.2 τ).1
  have e2 : X.rW.s τ = 1 := (hW.2.2 τ).1
  simp only [e1, e2] at hF
  exact hF

end GlobalTheory.BotDict
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesawTriple_firstFiniteDatum_standard_isVacuumDatum : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (hA : X.rA.IsStd) (hW : X.rW.IsStd), X.Is ψ θ α β νH S → ∀ t, IsFinF ψ θ true (GlobalTheory.BotDict.stdFr A hA.1) (GlobalTheory.BotDict.stdFr WW hW.1) (X.f t) := by
  atlas_forward_decl GlobalTheory.BotDict.fst_isFinF
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotDict

theorem isFinF_snd_std : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (hA' : X.rA'.IsStd) (hW : X.rW.IsStd), X.Is ψ θ α β νH S → ∀ t, IsFinF ψ θ false (GlobalTheory.BotDict.stdFr A' hA'.1) (GlobalTheory.BotDict.stdFr WW hW.1) (X.f' t) := by
  intro D T A A' WW X ψ θ α β νH S hA' hW hI t
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hth : IsThetaFunO ψ A' WW (X.f' t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hI.isVac'.1 hI.isVac'.2.inf (hI.snd t) hI.isVac'.2.theta
  refine ⟨hth, fun τ => ?_⟩
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hI.isVac'.1.1.1 hI.isVac'.2.inf ho.conj.infPart_eq
    ho.conj.conj.infPart_eq (hI.snd t) hI.isVac'.2.theta hth (hI.isVac'.2.fock τ)
  rw [(hA'.2.2 τ).1, (hW.2.2 τ).1] at hF
  rw [cart_frSgn_false_stdFr, cart_stdFr]
  exact hF

end GlobalTheory.BotDict

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesawTriple_secondFiniteDatum_standard_isVacuumDatum : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (hA' : X.rA'.IsStd) (hW : X.rW.IsStd), X.Is ψ θ α β νH S → ∀ t, IsFinF ψ θ false (GlobalTheory.BotDict.stdFr A' hA'.1) (GlobalTheory.BotDict.stdFr WW hW.1) (X.f' t) := by
  atlas_forward_decl GlobalTheory.BotDict.isFinF_snd_std
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotRankSize

theorem bot_arith (D : D7) (i j : ℕ) :
    Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧
      1 < SqNum.botSmall D i j := by
  have hk := D.R.k_even
  have hm := D.R.m_even
  have ht := D.R.t_odd
  have h3 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  rw [Nat.even_iff] at hk hm
  rw [Nat.odd_iff] at ht
  simp only [SqNum.botBig, SqNum.botSmall, rankV, sLen, Formalism.BasicNotions.Ranks.r]
  have e1 : (j + 1) * D.R.t = j * D.R.t + D.R.t := by ring
  have e2 : (i + 1) * (D.R.k + D.R.m - 1 + 6) = i * (D.R.k + D.R.m - 1 + 6) + (D.R.k + D.R.m - 1 + 6) := by ring
  rw [e1, e2]
  generalize j * D.R.t = A
  generalize i * (D.R.k + D.R.m - 1 + 6) = B
  rw [Nat.even_iff]
  omega

theorem bottom_ranks : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ i j : Fin D.R.m, Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧ 1 < SqNum.botSmall D i j := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro i j
  exact bot_arith D i j

end GlobalTheory.BotRankSize

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomRanks_arithmetic_largeGrids : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ i j : Fin D.R.m, Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧ 1 < SqNum.botSmall D i j := by
  atlas_forward_decl GlobalTheory.BotRankSize.bottom_ranks
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotDict

open GlobalTheory.ChainFr

theorem gBig_three {P Q R S : GP} (hP : GBig P) (hQ : GBig Q) (hR : GBig R)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → Q G μ₀ C x b → R G μ₀ C x b → S G μ₀ C x b) : GBig S := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  obtain ⟨CF3, h3⟩ := hR
  refine ⟨max CF1 (max CF2 CF3), fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, g1⟩ := h1 ε CF ((le_max_left _ _).trans hCF)
  obtain ⟨C2, x2, g2⟩ := h2 ε CF (((le_max_left _ _).trans (le_max_right _ _)).trans hCF)
  obtain ⟨C3, x3, g3⟩ := h3 ε CF (((le_max_right _ _).trans (le_max_right _ _)).trans hCF)
  refine ⟨max C1 (max C2 C3), max x1 (max x2 x3), fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ ?_ ?_ ?_⟩
  · exact g1 C ((le_max_left _ _).trans hC) D large₂ he ((le_max_left _ _).trans hx) hr T Lc μ₀ hμ G
  · exact g2 C (((le_max_left _ _).trans (le_max_right _ _)).trans hC) D large₂ he
      (((le_max_left _ _).trans (le_max_right _ _)).trans hx) hr T Lc μ₀ hμ G
  · exact g3 C (((le_max_right _ _).trans (le_max_right _ _)).trans hC) D large₂ he
      (((le_max_right _ _).trans (le_max_right _ _)).trans hx) hr T Lc μ₀ hμ G

theorem bottom_dictionary : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ), (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) ∧ (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) ∧ ∀ t : T, IsTriple A A' WW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) ∧ (∀ τ, HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ)) ∧ IsFinF W.ψ W.θ true FA FW (X.f t) ∧ IsFinF W.ψ W.θ false FA' FW (X.f' t) ∧ (∀ P g h, thetaKO (X.ω t) g h (fockF W.ψ W.θ true FA FW (X.f t) P) = X.ker W.ψ W.θ t P h g) ∧ ∀ P g h, thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.ker' W.ψ W.θ t P h g := by
  refine gBig_three GlobalTheory.T.bottomRanks_arithmetic_largeGrids GlobalTheory.T.exists_bottomInfinityExponents_gap_largeGrids GlobalTheory.T.definiteBottomTriple_finitePlaces_unram_or_split ?_
  intro D T Lc sc G μ₀ C x b _ hsz hinf hram W i j A A' WW X hX
  obtain ⟨a, b, hab⟩ := hinf W i j
  have hs := hX.std
  have hs' := hX.std'
  have hw := hX.stdW
  have hr : WW.rank = SqNum.botBig D i j + SqNum.botSmall D i j := by rw [← hX.is.rank, hX.rank, hX.rank']
  refine ⟨stdFr A hs.1, stdFr A' hs'.1, stdFr WW hw.1, a, b, hasSignature_of_gram_eq_one hs.1,
    hasSignature_of_gram_eq_one hs'.1, hasSignature_of_gram_eq_one hw.1, fun t => ⟨?_, fun τ => ⟨(hab t τ).1, (hab t τ).2.1⟩,
    GlobalTheory.T.seesawTriple_firstFiniteDatum_standard_isVacuumDatum X _ _ _ _ _ _ hs hw hX.is t, GlobalTheory.T.seesawTriple_secondFiniteDatum_standard_isVacuumDatum X _ _ _ _ _ _ hs' hw hX.is t, ?_, ?_⟩⟩
  · refine
      { hecA := (hX.is.weil' t).hecS
        hecB := (hX.is.weil t).hecS
        resA := (hX.is.weil' t).resS
        resB := (hX.is.weil t).resS
        rank := hX.is.rank.symm
        even := by rw [hr]; exact (hsz i j).1
        sig := ⟨0, 0, fun τ => ⟨by simpa using hasSignature_of_gram_eq_one hs.1 τ, by simpa using hasSignature_of_gram_eq_one hs'.1 τ,
          by simpa using hasSignature_of_gram_eq_one hw.1 τ⟩, by rw [hX.rank, hX.rank']; have := (hsz i j).2; omega,
          by rw [hX.rank']; have := (hsz i j).2.2; omega⟩
        gap := fun τ => ⟨a τ, b τ, (hab t τ).1, (hab t τ).2.1, by rw [hr]; exact (hab t τ).2.2⟩
        ram := hram W i j A A' WW X hX t }
  · intro P g h
    have e1 : (GlobalTheory.SquareComm.frSgn true (stdFr A hs.1)).cart = fun τ => -X.rA.s τ :=
      funext fun τ => by rw [cart_frSgn_true_stdFr, (hs.2.2 τ).1]
    have e2 : (stdFr WW hw.1).cart = X.rW.s := funext fun τ => by rw [cart_stdFr, (hw.2.2 τ).1]
    have e3 : (stdFr A hs.1).onb = X.rA.B := funext fun τ => by rw [onb_stdFr, (hs.2.2 τ).2]
    have e4 : (stdFr WW hw.1).onb = X.rW.B := funext fun τ => by rw [onb_stdFr, (hw.2.2 τ).2]
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker
    rw [e1, e2, e3, e4]
  · intro P g h
    have e1 : (GlobalTheory.SquareComm.frSgn false (stdFr A' hs'.1)).cart = X.rA'.s :=
      funext fun τ => by rw [cart_frSgn_false_stdFr, (hs'.2.2 τ).1]
    have e2 : (stdFr WW hw.1).cart = X.rW.s := funext fun τ => by rw [cart_stdFr, (hw.2.2 τ).1]
    have e3 : (stdFr A' hs'.1).onb = X.rA'.B := funext fun τ => by rw [onb_stdFr, (hs'.2.2 τ).2]
    have e4 : (stdFr WW hw.1).onb = X.rW.B := funext fun τ => by rw [onb_stdFr, (hw.2.2 τ).2]
    unfold GlobalTheory.SquareComm.fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker'
    rw [e1, e2, e3, e4]
    rfl

end GlobalTheory.BotDict

end
end
