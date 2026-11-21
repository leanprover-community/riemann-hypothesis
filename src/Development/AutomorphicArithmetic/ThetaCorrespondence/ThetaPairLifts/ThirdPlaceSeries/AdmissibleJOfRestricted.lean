import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleJOfRestricted
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.ConstituentConditionAtDistinguishedPrime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CompatR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfHyp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionaryOfParamsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionaryOfParams
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicCharacterOfAdmStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicCharacterOfAdm
import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.NonCriticalLocalParamOfFullDim
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bridge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenPeriodOfLocalGlobal

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal
noncomputable section
namespace UpperTheory.GalS
theorem de_rham_points_weight_jumps_alt (D : D7) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h2' : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : SumRepresentations.adm5 D)
    (hC : UpperTheory.GalC.CutRec D) : (∀ i r, GoodR D.nd i r → G2a D.nd D.naut i r) ∧ DeRhamJumpsDistinctCondition D := by
  have h2 := _root_.UpperTheory.GalS.weak' h2'
  have all : ∀ i r, GoodR D.nd i r → ∀ x, ∀ w ∈ placesOver D.host.E (D.nd.l i),
      D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
      ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ := by
    intro i r hr x w hw
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hB⟩ := h1 i P
    have hn : Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) := by
      have hg : ∀ k, D.nd.l i = D.host.g k → Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) := fun k hk => by
        have hw' : w ∈ placesOver D.host.E (D.host.g k) := hk ▸ hw
        rw [hB.2.2.2.1 w (GlobalTheory.DepthZeroType.isSplitPl_of_over D k w hw')]
        exact hC i P (by rw [hP]; simp) k w hw'
      by_cases a : D.nd.l i = D.host.g 0
      · exact hg 0 a
      by_cases b : D.nd.l i = D.host.g 1
      · exact hg 1 b
      exact .of_unr (Parts.iso_unr_l D i P Pa w hB hw a b)
    have h := compatR D h0 h2 h5 i r hr x P Pa hP hB w hw hn
    exact ⟨h.1, h.2.2⟩
  exact ⟨fun i r hr => (Parts.crys_unram_of_lgc D h0 h1 (Parts.lgc D h0 h2 h5) i r fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hr x)).1,
    fun i r hr _ w hw x => all i r hr x w hw, fun i r hr => Parts.constituentCondition_of_hodgeJumps D h0 i r hr (all i r hr)⟩
end UpperTheory.GalS
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
namespace GlobalTheory.AlgCharFromGal
theorem main_alt_alt_alt : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D := by
  intro D hA i π s z hz
  obtain ⟨ρ, hc, h1, h2⟩ := (_root_.UpperTheory.GalS.weak' hA i).2.2 π s (fun τ x hx => ⟨z τ, by
      have := Multiset.mem_map_of_mem (fun y => y + (s : ℂ)) hx
      rwa [hz τ, Multiset.mem_singleton] at this⟩)
  refine ⟨ρ, hc, fun w hw hu B σ hB hσ => ?_, fun w hw => (h2 w hw).1, fun τ => ?_⟩
  · have hu' : D.naut.unr (D.naut.wdOf i ρ w) := by
      rw [h1 w hw]; exact (D.naut.unr_tw _ _).2 hu
    have e := D.naut.wdOf_frob i ρ w hw hc hu' B σ hB hσ
    have hcard : Multiset.card (D.naut.frobEig (D.naut.wdOf i ρ w)) = 1 := by
      rw [D.naut.frobEig_card _ hu', D.naut.wdOf_dim]
    obtain ⟨α, hα⟩ := Multiset.card_eq_one.1 hcard
    rw [hα, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C] at e
    rw [← h1 w hw, hα]
    congr 1
    have e0 := congrArg (fun p => p.coeff 0) e
    simpa using e0.symm
  · obtain ⟨w, hw, hτ⟩ := GlobalTheory.GaloisInputCompare.exists_inducesW D.nd i τ
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [(h2 w hw).2.2 τ hτ]
    have e := hz ((D.naut.iotaQC i).toRingHom.comp τ)
    rw [show (fun y : ℂ => -(y + (s : ℂ))) = (fun y => -y) ∘ (fun y => y + (s : ℂ)) from rfl,
      ← Multiset.map_map, e]
    simp
end GlobalTheory.AlgCharFromGal
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicCharacter_of_adm2 : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D := by
  atlas_forward_decl _root_.GlobalTheory.AlgCharFromGal.main_alt_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
namespace GlobalTheory.BridgeAdmDict
theorem main_alt_alt : GlobalTheory.TwSys.Cheb → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  intro hC D hA hW hB
  have hAC := _root_.GlobalTheory.T.algebraicCharacter_of_adm2 D hA
  refine ⟨false, ?_⟩
  rintro i τ₀ g ρ ⟨hτ, hP⟩
  obtain ⟨b, hb, hU⟩ : ∃ b : Bool, (D.naut.iotaQC i).toRingHom.comp τ₀ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ b ∧
      (AdmissibleParameterJ.TypeU D false g ↔ b = true) := by
    rcases hP with h | h
    · refine ⟨false, ?_, ?_⟩
      · rw [hτ, ← h]; rfl
      · subst h
        simp [AdmissibleParameterJ.TypeU, (D.eTau ρ).2]
    · refine ⟨true, ?_, ?_⟩
      · rw [hτ, ← h, Formalism.L2.Geo.emb_mul_cc_comp]; rfl
      · subst h
        have := (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau ρ).2
        simp [AdmissibleParameterJ.TypeU, this]
  obtain ⟨cτ, h1, h2⟩ := GlobalTheory.T.jumps_dictionary_at_embedding_over_realPlace D hW hB hAC hC i τ₀ ρ b hb
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.sgnOf true b, cτ, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [hU.1 h]; rfl
  · intro h
    cases b
    · rfl
    · exact absurd (hU.2 rfl) h
  · rw [PPm_eq]; exact h1
  · intro w hw
    obtain ⟨h3, h4⟩ := h2 w (mem_placesOver D i τ₀ w hw)
    refine ⟨h3, ?_⟩
    rw [show AdmissibleParameterJ.rankOneCharacterQbar D i = mapRep (iotaOQ D.nd D.naut i) (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.chiGL D i 1) from rfl, h4, sz_eq]
    rfl
end GlobalTheory.BridgeAdmDict
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admDict_of_weight_blockChar : GlobalTheory.TwSys.Cheb → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  atlas_forward_decl _root_.GlobalTheory.BridgeAdmDict.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace UpperTheory.GalS
theorem lgc_of_cut'_alt (D : D7) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D) (hC : UpperTheory.GalC.CutRec D) : LGCN D := by
  intro i r hr w hw x
  have ht := hA.1
  have h1 := hA.2.2.1
  have h2 := _root_.UpperTheory.GalS.weak' hA.2.2.2.1
  have h5 := hA.2.2.2.2.2.2
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hPa⟩ := h1 i P
  obtain ⟨ρ, hc, hss, hwd, -⟩ := isoRep D ht h2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := rep_conj D h5 i r hr x P Pa hP hPa ρ hc hss hwd
  have hsp := D.nd.SQ_split i w hw
  have hwl := D.nd.SQ_l i w hw
  have rel : RelW D.nd D.naut (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)
      (D.naut.lpTw (D.naut.locV i P w) ((1 - (D.R.nV : ℝ)) / 2)) := by
    rw [← hPa.2.2.2.1 w hsp, ((ht.2.2.2.2.2 i).2.1 _ ρ _ hc Pm hPm).2.1 w (Or.inl hwl)]
    exact hwd w hwl
  refine ⟨P, hP, rel, (nc_tw _ _).2 ?_⟩
  have hd : D.naut.lpDim (D.naut.locV i P w) = D.R.nV := by
    rw [← D.naut.lpDim_tw _ ((1 - (D.R.nV : ℝ)) / 2), ← rel.dim, D.naut.wdOf_dim]
  have hne : D.naut.ptV i P ≠ none := by rw [hP]; simp
  rcases hw with hS | hQ
  · rcases ((D.nd.S_def i w).1 hS).1 with h | h | h
    · exact hC i P hne 0 w h
    · exact hC i P hne 1 w h
    · refine nonCritical_localParam_of_full_dim D hA.2.2.2.2.2.1 i P w (Or.inl hS) (Or.inr ⟨hS, ?_⟩) hd
      split_ifs at h with he
      · exact Or.inr ⟨he, h⟩
      · exact Or.inl h
  · exact nonCritical_localParam_of_full_dim D hA.2.2.2.2.2.1 i P w (Or.inr hQ) (Or.inl hQ) hd
end UpperTheory.GalS
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace Formalism.MainNotions.SumRepresentations
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal Topology
section BN
variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}
end BN
section G1
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
end G1
section SS
variable {Γ : Type} [Group Γ] {a : ℕ}
variable {K L : Type} [Field K] [Field L] [Algebra K L]
end SS
section Cont
end Cont
section Main
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
end Main
section C42
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace At
end At
namespace At
end At
end C42
section Del
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
end Del
section G5c
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))}
  {π : N.X i} {S : IdempotentChoiceData N i}
end G5c
section Quad
end Quad
section G5c
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))}
  {π : N.X i} {S : IdempotentChoiceData N i}
end G5c
section G5c
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))}
  {π : N.X i} {S : IdempotentChoiceData N i}
end G5c
section Cont
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
end Cont
section G5b
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin R.nV) (N.O i)))
end G5b
section Maschke
variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}
end Maschke
section G5a
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (Formalism.ConjugateSelfDual.G H.E N.Om →* GL (Fin R.nV) (N.O i)))
theorem splitI_of_monodromyInertiaType_of_lgCatN (A : NAut N) (hr : GoodR N i r) (hTY : At.MonodromyInertiaType N A) (w : PlE H)
    (hSQ : w ∈ N.S i ∨ w ∈ N.Q i)
    (hcond : w ∈ N.Q i ∨ (At.Del N i ∧
      (w ∈ placesOver H.E H.pde ∨ (N.l i = H.pde ∧ w ∈ placesOver H.E H.pde'))))
    (hL : _root_.UpperTheory.GalS.LGCatN N r A w) (x : N.X i) : SplitI N r w x :=
  _root_.UpperTheory.GalS.SplitI_of_TY N r A hr w (N.SQ_l i w hSQ) hL (fun P => hTY.1 i P w hSQ hcond) x
end G5a
section H0
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
end H0
section Lin
end Lin
section Z
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace At
end At
end Z
namespace At
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
def SufficientGaloisClauseAlt (i : N.Loc) : Prop :=
  HG N A i → ∀ r, GoodR N i r → ∀ w : PlE H, (w ∈ N.S i ∨ w ∈ N.Q i) →
    _root_.UpperTheory.GalS.LGCatN N r A w ∧
    (w ∈ N.S i → (∃ rb, IsRhoBar N i rb) ∧ ∀ rb, IsRhoBar N i rb →
      ¬ (((rb (N.gam0 i w) : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
        (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w))) ∧
      ∀ e : ℤ, HOneTwoZero N i w (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (chiEpsBar N i e)))
theorem galois_clause_of_sufficient_alt (hC : Cheb N) (hT : TieGal N A) (hTY : MonodromyInertiaType N A) (i : N.Loc) (hDel : Del N i)
    (h : _root_.Formalism.MainNotions.SumRepresentations.At.SufficientGaloisClauseAlt N A i) : ConclusionG5 N A i := by
  rw [galois_clause_iff_reduced N A i hDel]
  intro hg r hr w hw hl
  obtain ⟨hL, hS⟩ := h hg r hr w hw
  refine ⟨fun hq x => _root_.Formalism.MainNotions.SumRepresentations.splitI_of_monodromyInertiaType_of_lgCatN N r A hr hTY w hw ?_ hL x, fun hgk hS' => ?_,
    fun hS' rb hrb e => ?_⟩
  · rcases hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr ⟨hDel, hq⟩
  · obtain ⟨⟨rb, hrb⟩, hall⟩ := hS hS'
    exact _root_.UpperTheory.GalS.exists_inertia_charpoly_factor_of_tame_type N r A hC hr hT hTY w hS' hgk hL rb hrb (hall rb hrb).1
  · exact (HStarZero_iff N rb w hl ((hS hS').2 rb hrb).1 e).2 (((hS hS').2 rb hrb).2 e)
end At
def SufficientGaloisClauseAlt (D : D7) : Prop := ∀ i, _root_.Formalism.MainNotions.SumRepresentations.At.SufficientGaloisClauseAlt D.nd D.naut i
theorem galois_clause_of_sufficient_alt (D : D7) (h : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D) (ho : _root_.Formalism.MainNotions.SumRepresentations.SufficientGaloisClauseAlt D) : ConclusionG5 D := fun i =>
  _root_.Formalism.MainNotions.SumRepresentations.At.galois_clause_of_sufficient_alt D.nd D.naut h.2.2.2.2.2.2.2.2.1 h.1.2.2 h.2.2.2.2.2.1 i (Del_holds D i) (ho i)
end Formalism.MainNotions.SumRepresentations
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TameEig
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
abbrev _root_.GlobalTheory.TameEig.eigPd_holds_tyz : Prop :=  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D → _root_.GlobalTheory.StringRepresentationDecomposition.LocalGlobalCompatible D → RbEx D → EigPd D
end GlobalTheory.TameEig
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition Topology
open GlobalTheory.TameEig
noncomputable section
namespace UpperTheory.GalS
theorem eigPd_holds_alt : _root_.GlobalTheory.TameEig.eigPd_holds_tyz := by
  intro D hA hLGC _ i _ w hS hw rb hrb hroot
  have hC : Formalism.MainNotions.SumRepresentations.Cheb D.nd := hA.2.2.2.2.2.2.2.2.1
  have hDel := Formalism.MainNotions.SumRepresentations.Del_holds D i
  have hq : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    · exact D.host.pde'_prime
    · exact D.host.pde_prime
  have hq15 : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) % 15 = 1 := by
    split_ifs
    · exact D.host.pde_mod.2
    · exact D.host.pde_mod.1
  have hne := residue_ne_one D.nd i w hS _ hq hq15 hw (hDel w hS hw)
  have hcond : w ∈ D.nd.Q i ∨ (Formalism.MainNotions.SumRepresentations.At.Del D.nd i ∧ (w ∈ placesOver D.host.E D.host.pde ∨
      (D.nd.l i = D.host.pde ∧ w ∈ placesOver D.host.E D.host.pde'))) := by
    refine Or.inr ⟨hDel, ?_⟩
    by_cases hlp : D.nd.l i = D.host.pde
    · rw [if_pos hlp] at hw
      exact Or.inr ⟨hlp, hw⟩
    · rw [if_neg hlp] at hw
      exact Or.inl hw
  have x : D.nd.X i := Classical.choice (D.nd.neX i)
  have hQ : ∀ x, ∃ ρ, Formalism.MainNotions.SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hA.2.2.1 i P
    obtain ⟨ρ, h1, h2, h3, -⟩ := isoRep D hA.1 (_root_.UpperTheory.GalS.weak' hA.2.2.2.1) i P Pa hPa
    exact ⟨ρ, heckeQ D i x P Pa hP hPa ρ h1 h2 h3⟩
  choose rq hrq using hQ
  obtain ⟨r, hr⟩ := Formalism.MainNotions.SumRepresentations.exists_GoodR D.nd D.naut hA.2.1 i ⟨rq, hrq⟩
  have hL := hLGC i r hr w (Or.inl hS)
  have hs := _root_.Formalism.MainNotions.SumRepresentations.splitI_of_monodromyInertiaType_of_lgCatN D.nd r D.naut hr hA.2.2.2.2.2.1 w (Or.inl hS) hcond hL x
  have hg := D.nd.locNd_chebotarevPlace_mem i w
  have hwl := D.nd.SQ_l i w (Or.inl hS)
  have fac := Formalism.MainNotions.SumRepresentations.rhobar_fac D.nd r hC hr rb hrb x (D.nd.gam0 i w)
  rw [charpoly_red D.nd r hs _ hg] at fac
  have hprod : ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i)
      ((D.nd.chi i c (D.nd.gam0 i w) : (D.nd.O i)ˣ) : D.nd.O i))) =
      ∏ _c ∈ Finset.Icc 1 D.R.t, (X - C (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w)))) :=
    Finset.prod_congr rfl fun c hc => by
      rw [Formalism.MainNotions.SumRepresentations.character_eq_first_off_l D.nd w hwl c (Finset.mem_Icc.1 hc).1 (Finset.mem_Icc.1 hc).2 _ hg]
      rfl
  rw [hprod, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel] at fac
  have hcp := mul_right_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero _)) fac
  have h0 : ((X - 1 : Polynomial (IsLocalRing.ResidueField (D.nd.O i))) ^ D.R.r).eval
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) = 0 := by
    rw [← hcp]
    exact hroot
  rw [eval_pow, eval_sub, eval_X, eval_one] at h0
  exact pow_ne_zero _ (sub_ne_zero.2 hne) h0
end UpperTheory.GalS
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory GlobalTheory.StringRepresentationDecomposition UpperTheory.GalC
theorem g3a_of_restricted_general_alt {D : D7} (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (h : DeRhamJumpsDistinctCondition D) : ∀ i r, GoodR D.nd i r → DistinctAbsIrredConstituents D.nd i r := h.2
theorem admJ_of_admPar (D : D7) (L : SizeData₂ D) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : SumRepresentations.adm5 D)
    (hC : CutRec D) (hW : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D) (hB : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D) (hP : AdmissibleParameterJ.AdmPar L) :
    _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L :=
  have hG := _root_.UpperTheory.GalS.de_rham_points_weight_jumps_alt D h0 h1 h2 h5 hC
  ⟨hG.1, GlobalTheory.CrysWD.crysIffWD D, hG.2, _root_.GlobalTheory.T.admDict_of_weight_blockChar GlobalTheory.Published.cheb_holds D h2 hW hB, GlobalTheory.T.hodgeTateJumpsReading_rowAdm D, hP⟩
theorem duties_of_large_aux41 (hC : GlobalTheory.TwSys.Cheb) (D : D7) (hL : GlobalTheory.CoefDuty.Large D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (hg : _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D)
    (hRho : AutomorphicSideWildInertia.ResidualIrreducibleGood D) : GlobalTheory.CoefDuty.Duties D :=
  ⟨hL.1, fun i r hr => jc_of_u hr hL.2.1 (_root_.UpperTheory.GalS.g3a_of_restricted_general_alt h41 hg i r hr), GlobalTheory.T.designConditionAll_of_cheb_of_takenAll hC D hL.2.2, GlobalTheory.T.rowFiveOneTypePrime_of_coefRingTakenAtLive hC D hRho hL.2.2⟩
theorem prvG5_of_admissible_cutRec : LocalFiniteness → LocalTateDuality → LocalEulerChar →
    ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → CutRec D → SumRepresentations.ConclusionG5 D := by
  intro h1 h2 h3 D hA hRb hC
  have hLGC : _root_.GlobalTheory.StringRepresentationDecomposition.LocalGlobalCompatible D := _root_.UpperTheory.GalS.lgc_of_cut'_alt D hA.1.1 hC
  have hEig : EigPd D := _root_.UpperTheory.GalS.eigPd_holds_alt D hA.1.1 hLGC hRb
  have hH : HOneTwo D := GlobalTheory.T.hOneTwo_of_localFiniteness_tateDuality_eulerChar h1 h2 h3 D
  refine _root_.Formalism.MainNotions.SumRepresentations.galois_clause_of_sufficient_alt D hA.1.1 fun i hg r hr w hw => ⟨hLGC i r hr w hw, fun hS => ⟨hRb i hg, fun rb hrb => ?_⟩⟩
  have hS' := (D.nd.S_def i w).1 hS
  have hnr : ¬ (((rb (D.nd.gam0 i w) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) := by
    have hk : ∀ k, w ∈ placesOver D.host.E (D.host.g k) → D.nd.l i ≠ D.host.g k :=
      fun k hk h => hS'.2 (h ▸ hk)
    rcases hS'.1 with h0 | h0 | h0
    · exact (hA.2.1 i hg rb hrb).2 0 (hk 0 h0) w h0
    · exact (hA.2.1 i hg rb hrb).2 1 (hk 1 h0) w h0
    · exact hEig i hg w hS h0 rb hrb
  exact ⟨hnr, hH i rb w hS hrb hnr⟩
end UpperTheory.GalS
end
end
end
