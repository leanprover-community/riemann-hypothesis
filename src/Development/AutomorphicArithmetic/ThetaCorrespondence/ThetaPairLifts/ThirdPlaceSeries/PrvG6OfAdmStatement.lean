import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrvG6OfAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG6OfAdmissible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrvG6OfAllPartsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG6OfAllParts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeCharEqOfLAdicRealisation
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TwListSs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.HeckeCharacterEqualityOfRealisation
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecompositionStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.EtaPiece
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartFrobEigNormO
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthCharacterEqualityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthCharacterEquality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacter
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCountOfSsRankStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCountOfSsRank

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeckeCharacterEquality
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
def _root_.UpperTheory.GalS.HeckeCharacterEqualityOfRealisationAlt : Prop :=
  ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc) (χ χ' : D.naut.CG 1) (s : ℝ)
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))),
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      UpperTheory.GalS.RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (D.naut.locG χ w) s)) →
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ' w) s) →
    χ = χ'
theorem hecke_character_equality_of_realisation : _root_.UpperTheory.GalS.HeckeCharacterEqualityOfRealisationAlt := by
  intro D hA i χ χ' s ρ h h'
  have hAN := hA.1.1.2.2.2.2.2.2.1
  have hloc : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.locG χ w) → D.naut.locG χ w = D.naut.locG χ' w := by
    intro w hw hu
    have e := congrArg (fun a => D.naut.lpTw a (-s)) (((h w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)).symm.trans (h' w hw))
    simpa [D.naut.lpTw_add, D.naut.lpTw_zero] using e
  have hp := hAN [⟨1, χ, 1⟩] [⟨1, χ', 1⟩] (by simp) (by simp) (by
    have hfin := placesOver_finite_joint_conditions_zpowers D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
    filter_upwards [hfin.compl_mem_cofinite, D.naut.locG_unr_ae χ] with w hw hu
    simp only [isoLoc, spehLoc, List.foldr]
    rw [hloc w hw hu])
  have := List.perm_singleton.1 hp
  simpa using this
end GlobalTheory.HeckeCharacterEquality
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.EigenPoint
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
section Alg
variable {Γ : Type} [Group Γ] {K : Type} [Field K]
end Alg
variable (D : D7) (i : D.nd.Loc)
theorem eq_one_twist_t_of_mulVec_eigen (_h3 : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation') (h4 : _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (hg : HG D.nd D.naut i)
    (p : Part D.naut.CG) (Rk : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)))
    (hR : UpperTheory.GalS.IsStringRepN D i p Rk) (ha : p.a = 1) (hd : p.d = D.R.t) (u : Fin p.a → Qbar (D.nd.l i)) (hu0 : u ≠ 0)
    (hu : ∀ g, ((Rk g : GL _ _) : Matrix (Fin p.a) (Fin p.a) (Qbar (D.nd.l i))).mulVec u =
      iotaOQ D.nd D.naut i (chi1 D.nd i g) • u) :
    p = ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ := by
  have h3 := _root_.GlobalTheory.HeckeCharacterEquality.hecke_character_equality_of_realisation
  rcases p with ⟨a, π, d⟩
  dsimp only at ha hd
  subst ha hd
  have hu00 : u 0 ≠ 0 := fun h => hu0 (funext fun j => by rw [Fin.fin_one_eq_zero j]; exact h)
  have h00 : ∀ g, ((Rk g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
      iotaOQ D.nd D.naut i (chi1 D.nd i g) := fun g => by
    have := congrFun (hu g) 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hu00 this
  have hπ := h3 D hA i π (D.naut.tw (D.naut.muC i) D.naut.etaTinv) _ Rk hR.2.2 (h4 D hA i hg Rk h00)
  subst hπ
  rfl
end GlobalTheory.EigenPoint
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.EigenPoint
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
section Alg
variable {Γ : Type} [Group Γ] {K : Type} [Field K]
end Alg
variable (D : D7) (i : D.nd.Loc)
theorem mem_ZN_alt (h1 : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt) (h2 : _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight') (h3 : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation') (h4 : _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition) (h8 : EigenCharTwist)
    (hrc : _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount) (h11 : Numerics) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (hRb : RbEx D) (hg : HG D.nd D.naut i) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (x : D.nd.X i) (v : Fin D.R.nV → Kf D.nd i) (hv0 : v ≠ 0)
    (hv : ∀ g, ((mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x) g : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)).mulVec v =
          algebraMap (D.nd.O i) (Kf D.nd i) (chi1 D.nd i g) • v) :
    x ∈ ZN D.nd D.naut i := by
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hBC⟩ := hA.1.1.2.2.1 i P
  obtain ⟨R, hR, hcp⟩ := h1 D hA i x P Pa hP hBC r hr
  obtain ⟨Ak, hAk, hsum⟩ := hrc D hA hRb i hg r hr x Pa R hR hcp
  have hss : IsSSRep (mapRep (iotaOQ D.nd D.naut i) (r x)) :=
    (GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois D i x (r x) (hr x)).2.1
  obtain ⟨p, hpL, u, hu0, hu⟩ := h8 (Qbar (D.nd.l i)) (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) D.R.nV
    (mapRep (iotaOQ D.nd D.naut i) (r x)) (twList D i Pa R) (cU D i) hss (_root_.GlobalTheory.EigenPoint.isSSRep_of_mem_twList D i Pa R hR)
    (fun g => (hcp g).trans (twList_cp D i Pa R g).symm) (eig_map D i (r x) v hv0 hv)
  obtain ⟨k, a, ha, rfl⟩ := mem_twList D i hpL
  have hW : ∀ g, ((epsQ D i g)⁻¹ ^ a) • ((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a)
      (Qbar (D.nd.l i))).mulVec u = iotaOQ D.nd D.naut i (chi1 D.nd i g) • u := fun g => by
    have e := hu g
    rw [twGL_val, Matrix.smul_mulVec, eU_pow] at e
    exact e
  have hwt := h2 D hA i x P Pa hP hBC k (R k) (hR k) a ha ⟨u, hu0, hW⟩
  have hmem : Pa.get k ∈ Pa := List.get_mem Pa k
  have ha1 : 1 ≤ (Pa.get k).a := (hBC.1 _ hmem).1
  have hr1 : 1 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k
    show 1 < D.R.k + D.R.m - 1
    omega
  have ht2 : 2 ≤ D.R.t := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; have := D.R.rank_add_five_le
    omega
  have hle : (Pa.get k).d • Ak k ≤ D.R.r ::ₘ Multiset.replicate D.R.t 1 := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    exact Multiset.le_add_right _ _
  have hnum := h11 D.R.r D.R.t (Pa.get k).d (Pa.get k).a a (Ak k) hr1 ht2 ha hwt (hAk k).1 (hAk k).2 ha1 hle
  have ha0 : a = 0 := by rw [hnum.2] at hwt; omega
  subst ha0
  have hpart := _root_.GlobalTheory.EigenPoint.eq_one_twist_t_of_mulVec_eigen D i h3 h4 hA hg (Pa.get k) (R k) (hR k) hnum.1 hnum.2 u hu0
    (fun g => by simpa using hW g)
  exact ⟨P, hP, Pa, hBC, hpart ▸ hmem⟩
theorem isCuspIso_of_hasParamX (h1 : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt) (hrc : _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount)
    (h12 : Rest) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (hRb : RbEx D) (hg : HG D.nd D.naut i)
    (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) (x : D.nd.X i)
    (Sig : List (Part D.naut.CG)) (hSig : HasParamX D.nd D.naut i x Sig) : IsCuspIso D.nd D.naut Sig := by
  obtain ⟨P, hP, hBC⟩ := hSig
  have hlen : (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv).length = Sig.length + 1 := by
    simp [twistIso]
  have hlast : (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv).get
      (Fin.cast hlen.symm (Fin.last _)) = ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ := by
    simp only [List.get_eq_getElem, Fin.val_cast, Fin.val_last]
    simp [twistIso, muPart, List.getElem_append_right]
  generalize hPa : twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv = Pa at hBC hlen hlast
  obtain ⟨R, hR, hcp⟩ := h1 D hA i x P Pa hP hBC r hr
  obtain ⟨Ak, hAk, hsum⟩ := hrc D hA hRb i hg r hr x Pa R hR hcp
  rw [sum_split hlen] at hsum
  have hAl : Ak (Fin.cast hlen.symm (Fin.last _)) = {1} :=
    ms_one ((hAk _).1.trans (by rw [hlast])) (hAk _).2
  have hlt : (Pa.get (Fin.cast hlen.symm (Fin.last _))).d • Ak (Fin.cast hlen.symm (Fin.last _)) =
      Multiset.replicate D.R.t 1 := by
    rw [hAl, hlast]
    exact Multiset.nsmul_singleton _ _
  rw [hlt, ← Multiset.singleton_add] at hsum
  have hS := add_right_cancel hsum
  have hmem : ∀ k : Fin Sig.length, Pa.get (Fin.cast hlen.symm k.castSucc) ∈ Pa := fun k => List.get_mem _ _
  have hG := h12 (Fin Sig.length) (fun k => (Pa.get (Fin.cast hlen.symm k.castSucc)).d)
    (fun k => Ak (Fin.cast hlen.symm k.castSucc)) D.R.r (fun k => (hBC.1 _ (hmem k)).2.1)
    (fun k h => by
      have e := (hAk (Fin.cast hlen.symm k.castSucc)).1
      rw [h, Multiset.sum_zero] at e
      have := (hBC.1 _ (hmem k)).1
      omega) hS
  have hl1 : Sig.length = 1 := by simpa using hG.1
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl1
  have h0 := hG.2 ⟨0, by simp⟩
  have hget : Pa.get (Fin.cast hlen.symm (Fin.castSucc (⟨0, by simp⟩ : Fin [p].length))) =
      ⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ := by
    subst hPa
    simp [twistIso]
  have hd : p.d = 1 := by have := h0.1; rw [hget] at this; exact this
  have ha : p.a = D.R.r := by
    have e := (hAk (Fin.cast hlen.symm (Fin.castSucc (⟨0, by simp⟩ : Fin [p].length)))).1
    rw [h0.2, hget, Multiset.sum_singleton] at e
    exact e.symm
  rcases p with ⟨a, π, d⟩
  dsimp only at hd ha
  subst hd ha
  exact ⟨π, rfl⟩
theorem prvG6_of_realisation_mu_res_count_numerics : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt → _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' → _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' → _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition → EigenCharTwist → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount → Numerics → Rest →
    ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → SumRepresentations.ConclusionG6 D :=
  fun h1 h2 h3 h4 h8 hrc h11 h12 D hA hRb i hg r hr x hx =>
    ⟨hx.elim fun v hv => _root_.GlobalTheory.EigenPoint.mem_ZN_alt D i h1 h2 h3 h4 h8 hrc h11 hA hRb hg r hr x v hv.1 hv.2,
      fun Sig hSig => _root_.GlobalTheory.EigenPoint.isCuspIso_of_hasParamX D i h1 hrc h12 hA hRb hg r hr x Sig hSig⟩
end GlobalTheory.EigenPoint
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prvG6_of_admissible_of_g6_decomposition : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt → _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' → _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' → _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition → EigenCharTwist → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount → Numerics → Rest → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → SumRepresentations.ConclusionG6 D := by
  atlas_forward_decl _root_.GlobalTheory.EigenPoint.prvG6_of_realisation_mu_res_count_numerics
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
section Alg
variable {Γ : Type} [Group Γ] {K : Type} [Field K]
end Alg
end GlobalTheory.StringDecomp
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
section Frob
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
end Frob
end GlobalTheory.StringDecomp
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
section Eps
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)
end Eps
end GlobalTheory.StringDecomp
namespace GlobalTheory.StringDecomp
open Formalism.MainNotions.SumRepresentations.At Topology
theorem exists_stringRep_alt_alt (D : D7) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (i : D.nd.Loc) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)) (hBC : IsBCV D.nd D.naut i P Pa) (p : Part D.naut.CG) (hp : p ∈ Pa) :
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)), UpperTheory.GalS.IsStringRepN D i p ρ := by
  obtain ⟨⟨⟨hLP, hAut, hGal⟩, -, -, hG, -, -, -⟩, -⟩ := hA.1
  obtain ⟨ha, hd, hc⟩ := hBC.1 p hp
  have hw := GlobalTheory.BCGal.galois_relation_away_from_l D.nd D.naut i hLP hAut hGal (_root_.UpperTheory.GalS.weak' hG) ha p.π hc
    ((p.d : ℤ) - 1 + p.a - D.R.nV) fun τ => by
    have hW : (D.naut.infWt i τ).Nodup ∧
        ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
      rw [D.nbc.embAV_inf i P]
      exact D.nbc.infW_alg _ _ τ
    have hle : (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ D.naut.infWt i τ := by
      rw [← hBC.2.2.2.2.2 τ]
      refine le_trans (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ ?_)
        (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
      exact List.mem_map.2 ⟨0, by simp; exact ⟨0, by omega, by simp⟩, by simp⟩
    refine ⟨(Multiset.nodup_of_le hle hW.1).of_map _, fun z hz => ?_⟩
    obtain ⟨n, hn⟩ := hW.2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz))
    exact ⟨n, by push_cast at hn ⊢; linear_combination hn⟩
  obtain ⟨ρ, hcont, hss, hwd⟩ := hw
  refine ⟨ρ, hcont, hss, fun w hwl => ?_⟩
  convert hwd w hwl using 2
  push_cast
  ring_nf
theorem stringDecomp_holds_alt_alt :
    ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ r, GoodR D.nd i r →
    ∃ R : ∀ k : Fin Pa.length, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)),
      (∀ k, UpperTheory.GalS.IsStringRepN D i (Pa.get k) (R k)) ∧
      ∀ g, ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
        ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
          (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
            ((epsQ D i g)⁻¹ ^ a) := by
  intro D hA i x P Pa hx hBC r hr
  have hC := hA.1.1.2.2.2.2.2.2.2.2.1
  have hex : ∀ p : Part D.naut.CG, ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)),
      p ∈ Pa → UpperTheory.GalS.IsStringRepN D i p ρ := by
    intro p
    by_cases hp : p ∈ Pa
    · obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.StringDecomp.exists_stringRep_alt_alt D hA i P Pa hBC p hp
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose Rp hRp using hex
  refine ⟨fun k => Rp (Pa.get k), fun k => hRp _ (List.get_mem Pa k), ?_⟩
  have hrk : rkL Pa = D.R.nV := (rkL_eq Pa).trans hBC.2.2.1
  have hcL := cont_listRep Rp _ (cont_epsQU_inv D.nd D.naut i) Pa (fun p hp => (hRp p hp).1)
  obtain ⟨ρ', hρ'⟩ := exists_cast hrk (listRep Rp (epsQU D.nd D.naut i)⁻¹ Pa)
  have hQ := GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois D i x (r x) (hr x)
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) : Set (PlE D.host)).Finite :=
    ((placesOver_finite' D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).union (D.nd.S i).finite_toSet).union
      (D.nd.Q i).finite_toSet
  have key := GlobalTheory.charpoly_eq_of_eqOn_dense
    (fun g => ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))))
    (fun g => ((ρ' g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))))
    hQ.1 (hρ'.1 hcL) _ (dense_iff_closure_eq.2 (hC _ hfin)) (by
      rintro σ ⟨w, hw, hsp, B, hB, hσ⟩
      simp only [Set.mem_union, not_or, Finset.mem_coe] at hw
      have hso : SplitOut D.nd i w := ⟨hsp, hw.1.1, hw.1.2, hw.2⟩
      show _ = _
      rw [hQ.2.2 w hso B σ hB hσ, hρ'.2 σ, charpoly_listRep]
      apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
      rw [Polynomial.map_map, show (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) =
        ((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).comp (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
        from rfl, D.naut.pt_loc i P x hx w hso, ← hBC.2.2.2.1 w hsp]
      exact (iso_poly i w hso.2.1 B σ hB hσ Rp _ _ (epsQU_frob D.nd D.naut i hso.2.1 hB hσ) Pa
        (fun p hp => (hRp p hp).1) (fun p hp => ((hRp p hp).2.2 w hso.2.1).eq_of_unr ((D.naut.unr_tw _ _).2
          (UpperTheory.GalN.unr_part Pa (iso_unr i hBC w hso) p hp (hBC.1 p hp).2.1))) (iso_unr i hBC w hso)).symm)
  intro g
  rw [key g, hρ'.2 g, charpoly_listRep, epsQU_inv_val, ← prod_get]
  rfl
end GlobalTheory.StringDecomp
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centred_string_decomposition : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt := by
  atlas_forward_decl _root_.GlobalTheory.StringDecomp.stringDecomp_holds_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.FrobeniusCharacterNorms
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
end GlobalTheory.FrobeniusCharacterNorms
namespace GlobalTheory.FrobeniusCharacterNorms
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
theorem sixth_weight_purity_alt_alt : _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' := by
  intro D hA i x P Pa hxP hBC k R hR j hj hv
  have hAut : At.TieAut D.nd D.naut := hA.1.1.1.2.1
  have hC := hA.1.1.2.2.2.2.2.2.2.2.1
  have hp : Pa.get k ∈ Pa := List.get_mem Pa k
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) ∪
      {w | ¬ D.naut.unr (D.naut.locG (Pa.get k).π w)} ∪
      {w | ¬ D.naut.unr (D.naut.locG (D.naut.muC i) w)} : Set (PlE D.host)).Finite := by
    have h1 : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) : Set (PlE D.host)).Finite :=
      ((placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).union
        (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet
    exact (h1.union (Filter.eventually_cofinite.1 (D.naut.locG_unr_ae (Pa.get k).π))).union
      (Filter.eventually_cofinite.1 (D.naut.locG_unr_ae (D.naut.muC i)))
  have hne := (hC _ hfin).symm ▸ Set.mem_univ (1 : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)
  obtain ⟨σ, ⟨w, hw, hsp, B, hB, hσ⟩⟩ : Set.Nonempty {σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ (placesOver D.host.E (D.nd.l i) ∪
      ↑(D.nd.S i) ∪ ↑(D.nd.Q i) ∪ {w | ¬ D.naut.unr (D.naut.locG (Pa.get k).π w)} ∪
      {w | ¬ D.naut.unr (D.naut.locG (D.naut.muC i) w)} : Set (PlE D.host)), IsSplitPl D.host w ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hne
    exact hne
  simp only [Set.mem_union, not_or, Finset.mem_coe, Set.mem_setOf_eq, not_not] at hw
  have hl := hw.1.1.1.1
  have hwo : SplitOut D.nd i w := ⟨hsp, hl, hw.1.1.1.2, hw.1.1.2⟩
  have huπ := hw.1.2
  have huμ := hw.2
  have hR := _root_.UpperTheory.GalS.strN' hR
  have hwd := (hR.2.2 w hl).eq_of_unr ((D.naut.unr_tw _ _).2 huπ)
  have hU : D.naut.unr (D.naut.wdOf i R w) := by rw [hwd]; exact (D.naut.unr_tw _ _).2 huπ
  have hF := D.naut.wdOf_frob i R w hl hR.1 hU B σ hB hσ
  rw [hwd, D.naut.frobEig_tw _ _ huπ] at hF
  obtain ⟨v, hv0, hvg⟩ := hv
  have h1 := hvg σ
  set M : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i)) :=
    ((R σ : GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))) with hM
  set c : Qbar (D.nd.l i) := iotaOQ D.nd D.naut i (chi1 D.nd i σ) with hc
  have he0 : epsQ D i σ ≠ 0 :=
    ((Units.isUnit (Formalism.MainNotions.N.Glob.epsO D.nd i σ)).map (iotaOQ D.nd D.naut i)).ne_zero
  have hMv : M.mulVec v = (epsQ D i σ ^ j * c) • v := by
    have h2 := congrArg (fun u => (epsQ D i σ ^ j) • u) h1
    simp only [smul_smul, inv_pow] at h2
    rw [mul_inv_cancel₀ (pow_ne_zero _ he0), one_smul] at h2
    exact h2
  have hdet : (Matrix.scalar (Fin (Pa.get k).a) (epsQ D i σ ^ j * c) - M).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, hMv]
    ext t
    simp [Matrix.scalar_apply]
  have hroot : (M.charpoly.map (D.naut.iotaQC i).toRingHom).IsRoot
      ((D.naut.iotaQC i).toRingHom (epsQ D i σ ^ j * c)) :=
    Polynomial.IsRoot.map (by rw [Polynomial.IsRoot.def, Matrix.eval_charpoly]; exact hdet)
  rw [hF] at hroot
  have hmem := (Polynomial.mem_roots (Polynomial.monic_multiset_prod_of_monic _ _
    (fun a _ => Polynomial.monic_X_sub_C a)).ne_zero).2 hroot
  rw [Polynomial.roots_multiset_prod_X_sub_C] at hmem
  obtain ⟨α, hα, hαe⟩ := Multiset.mem_map.1 hmem
  have hα1 := (_root_.GlobalTheory.PartUnitary.frobEig_openB_and_norm_one_of_isBCV D hA.1.1.1 hA.1.2 i P Pa hBC (Pa.get k) hp w huπ α hα).1
  have hq0 : 0 < normV w := normV_pos w
  have hq1 : (1 : ℝ) < normV w := GlobalTheory.LocalInv.one_lt_normV w
  have hε : D.naut.iotaQC i (epsQ D i σ) = (normV w : ℂ) := eps_frob i hl hB hσ
  have hχ := norm_first_character_frobenius hAut i hwo huμ hB hσ
  have hn := congrArg norm hαe
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow, hε, norm_mul, norm_pow,
    Complex.norm_natCast_cpow_of_pos hq0, Complex.ofReal_re, Complex.norm_natCast] at hn
  rw [hc, hχ, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)] at hn
  have hx := hα1.exp_eq (UpperTheory.GalN.one_lt_q w) hn (2 * (j : ℤ) + D.R.t - (Pa.get k).d) (by push_cast; ring)
  have hz : (((Pa.get k).d : ℤ) - 1 - 2 * j : ℝ) = ((D.R.t : ℤ) - 1 : ℝ) := by push_cast; linarith
  exact_mod_cast hz
end GlobalTheory.FrobeniusCharacterNorms
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.purity_string_weight : _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' := by
  atlas_forward_decl _root_.GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeckeCharacterEquality
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
theorem sixth_character_equality_holds_alt_alt : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' := by
  intro D hA i χ χ' s ρ h h'
  have hAN := hA.1.1.2.2.2.2.2.2.1
  have hloc : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.locG χ w = D.naut.locG χ' w := by
    intro w hw
    have e := congrArg (fun a => D.naut.lpTw a (-s)) ((h w hw).symm.trans (h' w hw))
    simpa [D.naut.lpTw_add, D.naut.lpTw_zero] using e
  have hp := hAN [⟨1, χ, 1⟩] [⟨1, χ', 1⟩] (by simp) (by simp) (by
    have hfin := placesOver_finite_joint_conditions_zpowers D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
    filter_upwards [hfin.compl_mem_cofinite] with w hw
    simp only [isoLoc, spehLoc, List.foldr]
    rw [hloc w hw])
  have := List.perm_singleton.1 hp
  simpa using this
end GlobalTheory.HeckeCharacterEquality
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_char_eq_of_l_adic_realisation : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' := by
  atlas_forward_decl _root_.GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace GlobalTheory.MuCharProof
abbrev _root_.GlobalTheory.MuCharProof.muChar_holds_tyz : Prop :=  _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition
end GlobalTheory.MuCharProof
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
open GlobalTheory.MuCharProof
noncomputable section
namespace UpperTheory.GalS
open UpperTheory.Lit.Car
theorem muChar_holds_alt : _root_.GlobalTheory.MuCharProof.muChar_holds_tyz := by
  intro D hA i hg ρ hρ w hw
  obtain ⟨x, ⟨P, -, Pa, hBC, hmem⟩, -⟩ := hg
  have h2 := _root_.UpperTheory.GalS.weak' hA.1.1.2.2.2.1
  have h5 : Formalism.MainNotions.SumRepresentations.adm5 D := hA.1.1.2.2.2.2.2.2
  set χ := D.naut.tw (D.naut.muC i) D.naut.etaTinv with hχ
  set s : ℝ := ((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2 with hs
  have halg : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ) := by
    intro τ z hz
    have ht : 0 ∈ List.range D.R.t := List.mem_range.2 D.R.t_odd.pos
    have h1 : z + (((D.R.t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) ∈ isoInf D.nd D.naut Pa τ := by
      refine mem_list_sum Pa _ hmem ?_
      refine mem_list_sum _ _ (a := ((0 : ℕ) : ℂ)) ?_ ?_
      · simp only [List.mem_range]
        simp
        exact ⟨0, D.R.t_odd.pos, by simp⟩
      · exact Multiset.mem_map_of_mem _ hz
    rw [hBC.2.2.2.2.2 τ] at h1
    let τ' : D.host.E →+* Qbar (D.nd.l i) := (D.naut.iotaQC i).symm.toRingHom.comp τ
    have hτ : (D.naut.iotaQC i).toRingHom.comp τ' = τ := by
      ext e
      simp [τ']
    have hj := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ'
    rw [hτ] at hj
    have h3 : -(z + (((D.R.t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) + ((D.R.nV : ℂ) - 1) / 2 ∈
        (D.naut.locAutHodgeTateWeightsLevelZero i τ').map (fun n : ℤ => (n : ℂ)) := by
      rw [hj]
      exact Multiset.mem_map_of_mem _ h1
    obtain ⟨n, -, hn⟩ := Multiset.mem_map.1 h3
    refine ⟨-n, ?_⟩
    rw [hs]
    push_cast at hn ⊢
    linear_combination hn
  obtain ⟨ρ', hc', hw', -⟩ := (h2 i).2.2 χ s halg
  have hc0 : Continuous fun g => ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 := by
    have : (fun g => ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0) =
        fun g => iotaOQ D.nd D.naut i (chi1 D.nd i g) := funext hρ
    rw [this]
    exact (Formalism.MainNotions.SumRepresentations.continuous_iotaOQ D.nd D.naut i).comp (D.nd.chi_cont i 1)
  have hc0' : Continuous fun g => ((ρ' g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 :=
    hc'.matrix_elem 0 0
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) : Set (PlE D.host)).Finite :=
    ((Formalism.MainNotions.SumRepresentations.placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).union
      (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet
  have hdense := h5.2.2.1 _ hfin
  have hsub : {σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) :
      Set (PlE D.host)), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} ⊆
      {g | ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
        ((ρ' g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0} := by
    rintro σ ⟨v, hv, hsp, B, hB, hσ⟩
    simp only [Set.mem_union, not_or, Finset.mem_coe] at hv
    have hso : SplitOut D.nd i v := ⟨hsp, hv.1.1, hv.1.2, hv.2⟩
    obtain ⟨hu, hf⟩ := D.naut.chi_mu i v hso
    have hunr : D.naut.unr (D.naut.wdOf i ρ' v) := by
      rw [hw' v hv.1.1]
      exact (D.naut.unr_tw _ _).2 hu
    have e := D.naut.wdOf_frob i ρ' v hv.1.1 hc' hunr B σ hB hσ
    rw [hw' v hv.1.1, hf B σ hB hσ, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
    have e2 := (D.naut.iotaQC i).injective (C_injective (sub_right_injective e))
    show _ = _
    rw [hρ σ]
    exact e2.symm
  have hall : ∀ g, ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
      ((ρ' g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 := by
    intro g
    have hcl : IsClosed {g | ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
        ((ρ' g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0} := isClosed_eq hc0 hc0'
    have := closure_minimal hsub hcl
    rw [hdense] at this
    exact this (Set.mem_univ g)
  have heq : ρ = ρ' := by
    refine MonoidHom.ext fun g => Units.ext (Matrix.ext fun a b => ?_)
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    exact hall g
  rw [heq]
  exact hw' w hw
end UpperTheory.GalS
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
noncomputable section
namespace GlobalTheory.ResidualRankCount
section Alg
variable {Γ : Type} [Group Γ]
end Alg
section Lists
end Lists
section Psi
end Psi
theorem residual_count_alt_alt : ValRingModel → SSList → SSRankUnique → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount := by
  intro hV hS hU D hA hRb i hg r hr x Pa R hR hcp
  classical
  obtain ⟨B, _, _, _, j, hj, hran, hmax, hmod⟩ := hV (D.nd.l i)
  obtain ⟨ψ, hψ, φ, hφ⟩ := exists_psi D.nd D.naut i j hj hran hmax
  choose ρ0 P hP using fun k : Fin Pa.length => hmod (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (Pa.get k).a (R k) (_root_.UpperTheory.GalS.strN' (hR k)).1
  choose L hL1 hL2 using fun k : Fin Pa.length =>
    hS (IsLocalRing.ResidueField B) (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (Pa.get k).a (mapRep (IsLocalRing.residue B) (ρ0 k))
  obtain ⟨rb, hrb⟩ := hRb i hg
  have hC : Formalism.MainNotions.SumRepresentations.Cheb D.nd := hA.1.1.2.2.2.2.2.2.2.2.1
  have hirr := (hA.2.1 i hg rb hrb).1
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    show 1 ≤ D.R.k + D.R.m - 1
    omega
  let cR : ℕ → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (IsLocalRing.ResidueField B)) := fun c =>
    (Units.map (algebraMap (IsLocalRing.ResidueField B)
      (Matrix (Fin 1) (Fin 1) (IsLocalRing.ResidueField B))).toMonoidHom).comp
      ((Units.map (φ.comp (IsLocalRing.residue (D.nd.O i))).toMonoidHom).comp (D.nd.chi i c))
  let τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (IsLocalRing.ResidueField B)ˣ :=
    (Units.map ((IsLocalRing.residue B).comp ψ).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO D.nd i)⁻¹
  let L1 : List (Σ m : ℕ, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin m) (IsLocalRing.ResidueField B)) :=
    ⟨D.R.r, mapRep φ rb⟩ :: (Finset.Icc 1 D.R.t).toList.map fun c => ⟨1, cR c⟩
  let L2 : List (Σ m : ℕ, Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin m) (IsLocalRing.ResidueField B)) :=
    (List.finRange Pa.length).flatMap fun k => (List.range (Pa.get k).d).flatMap fun a =>
      (L k).map fun p => ⟨p.1, Formalism.MainNotions.SumRepresentations.At.twGL p.2 (τ ^ a)⟩
  have h1 : ∀ p ∈ L1, 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤ := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨hr1, GlobalTheory.T.absIrrSub_map_of_irredOn_map_Fbar hr1 rb (D.naut.kFbar i) hirr φ⟩
    · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hp
      exact ⟨le_rfl, absIrr_id le_rfl _ fun W _ => sub_fin_one W⟩
  have h2 : ∀ p ∈ L2, 1 ≤ p.1 ∧ AbsIrrSub p.2 ⊤ := by
    intro p hp
    obtain ⟨k, -, hp⟩ := List.mem_flatMap.1 hp
    obtain ⟨a, -, hp⟩ := List.mem_flatMap.1 hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨hq1, hq2⟩ := hL1 k q hq
    exact ⟨hq1, absIrr_id hq1 _ fun W hW => hq2.2.2 W le_top (isInv_of_twGL _ _ W hW)⟩
  have hjψ : j.comp ψ = iotaOQ D.nd D.naut i := RingHom.ext hψ
  have hs : ∀ g, j (ψ (((Formalism.MainNotions.N.Glob.epsO D.nd i g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) = (epsQ D i g)⁻¹ := by
    intro g
    rw [hψ, map_units_inv]
    rfl
  have hBid : ∀ g, (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map ψ =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((ρ0 k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) B).charpoly).scaleRoots
          (ψ (((Formalism.MainNotions.N.Glob.epsO D.nd i g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) ^ a) := by
    intro g
    apply Polynomial.map_injective j hj
    rw [Polynomial.map_map, hjψ, ← Matrix.charpoly_map]
    show ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly = _
    rw [hcp g, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_scaleRoots _ _ _ (by rw [(Matrix.charpoly_monic _).leadingCoeff, map_one]; exact one_ne_zero),
      ← Matrix.charpoly_map, map_pow, hs, hP k g, Matrix.charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
  have hkA : ∀ g, (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map
        ((IsLocalRing.residue B).comp ψ) =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((mapRep (IsLocalRing.residue B) (ρ0 k) g : GL _ _) :
          Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (IsLocalRing.ResidueField B)).charpoly).scaleRoots
          ((τ g : IsLocalRing.ResidueField B) ^ a) := by
    intro g
    rw [← Polynomial.map_map, hBid g, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_scaleRoots _ _ _ (by rw [(Matrix.charpoly_monic _).leadingCoeff, map_one]; exact one_ne_zero),
      ← Matrix.charpoly_map, map_pow]
    all_goals rfl
  have hcpL1 : ∀ g, (L1.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod =
      (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly).map
        ((IsLocalRing.residue B).comp ψ) := by
    intro g
    have hφ' : φ.comp (IsLocalRing.residue (D.nd.O i)) = (IsLocalRing.residue B).comp ψ := RingHom.ext hφ
    have hf : (((r x g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map
        (IsLocalRing.residue (D.nd.O i))).charpoly = _ :=
      (Formalism.MainNotions.SumRepresentations.rhobar_fac D.nd r hC hr rb hrb x g).symm
    rw [← hφ', ← Polynomial.map_map, ← Matrix.charpoly_map, hf, Polynomial.map_mul, Polynomial.map_prod]
    simp only [L1, List.map_cons, List.prod_cons, List.map_map]
    congr 1
    · exact Matrix.charpoly_map _ φ
    · rw [Finset.prod_map_toList]
      refine Finset.prod_congr rfl fun c _ => ?_
      show (algebraMap (IsLocalRing.ResidueField B) (Matrix (Fin 1) (Fin 1) (IsLocalRing.ResidueField B))
        (φ (IsLocalRing.residue (D.nd.O i) ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i)))).charpoly = _
      rw [charpoly_scal, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hcpL2 : ∀ g, (L2.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((mapRep (IsLocalRing.residue B) (ρ0 k) g : GL _ _) :
          Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (IsLocalRing.ResidueField B)).charpoly).scaleRoots
          ((τ g : IsLocalRing.ResidueField B) ^ a) := by
    intro g
    simp only [L2]
    rw [prod_map_flatMap, Fin.prod_univ_def]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    rw [prod_map_flatMap, prod_range_list]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    rw [hL2 k g, scaleRoots_list_prod]
    simp only [List.map_map]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    show ((Formalism.MainNotions.SumRepresentations.At.twGL q.2 (τ ^ a) g : GL _ _) :
      Matrix (Fin q.1) (Fin q.1) (IsLocalRing.ResidueField B)).charpoly = _
    rw [charpoly_twGL, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rfl
  have h3 : ∀ g, (L1.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod =
      (L2.map fun p => ((p.2 g : GL _ _) :
        Matrix (Fin p.1) (Fin p.1) (IsLocalRing.ResidueField B)).charpoly).prod := fun g => by
    rw [hcpL1 g, hcpL2 g, hkA g]
  have hrk := hU (IsLocalRing.ResidueField B) (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) L1 L2 h1 h2 h3
  refine ⟨fun k => (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ), fun k => ⟨?_, ?_⟩, ?_⟩
  · show (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ).sum = _
    rw [Multiset.sum_coe, ← (charpoly_list_monic (L k) 1).2, ← hL2 k 1, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  · intro a ha
    rw [Multiset.mem_coe, List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact (hL1 k p hp).1
  · have e1 : ((L1.map fun p => p.1 : List ℕ) : Multiset ℕ) = D.R.r ::ₘ Multiset.replicate D.R.t 1 := by
      have : (L1.map fun p => p.1) = D.R.r :: List.replicate D.R.t 1 := by
        simp only [L1, List.map_cons, List.map_map, List.cons.injEq, true_and]
        refine List.eq_replicate_iff.2 ⟨by simp, fun b hb => ?_⟩
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hb
        rfl
      rw [this, ← Multiset.cons_coe, Multiset.coe_replicate]
    have e2 : ((L2.map fun p => p.1 : List ℕ) : Multiset ℕ) =
        ∑ k, (Pa.get k).d • (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ) := by
      simp only [L2, List.map_flatMap, List.map_map, Function.comp_def, coe_flatMap, sum_range_const]
      rw [Fin.sum_univ_def]
    show ∑ k, (Pa.get k).d • (((L k).map fun p => p.1 : List ℕ) : Multiset ℕ) = _
    rw [← e2, ← hrk, e1]
end GlobalTheory.ResidualRankCount
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.resCount_of_valRing_ssList_ssRank : ValRingModel → SSList → SSRankUnique → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount := by
  atlas_forward_decl _root_.GlobalTheory.ResidualRankCount.residual_count_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
namespace GlobalTheory.ClosingSixth
theorem conclusionG6_of_adm_alt : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → SumRepresentations.ConclusionG6 D :=
  _root_.GlobalTheory.T.prvG6_of_admissible_of_g6_decomposition _root_.GlobalTheory.T.centred_string_decomposition _root_.GlobalTheory.T.purity_string_weight _root_.GlobalTheory.T.hecke_char_eq_of_l_adic_realisation _root_.UpperTheory.GalS.muChar_holds_alt GlobalTheory.T.eigencharacter_of_summand_charZero
    (_root_.GlobalTheory.T.resCount_of_valRing_ssList_ssRank GlobalTheory.T.valuation_ring_model GlobalTheory.T.exists_irreducible_constituents_charpoly_product GlobalTheory.T.absIrreducible_constituent_ranks_unique_of_charpoly)
    GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton.1 GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton.2
end GlobalTheory.ClosingSixth
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prvG6_of_admissible' : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → SumRepresentations.ConclusionG6 D := by
  atlas_forward_decl _root_.GlobalTheory.ClosingSixth.conclusionG6_of_adm_alt
end
end
