import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecOfF
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNormHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLatCoord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFacEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAtApart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MatEqOfComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongGrpEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCuspTh
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TyFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
import GroundTheory.AutomorphicForms.AffineBruhat
import Development.AutomorphicArithmetic.IwahoriCommensurability.IsCommensuratedIwahoriGl
import Development.AutomorphicArithmetic.IwahoriCommensurability.AffineWeylSimpleReflectionCoset
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SeenShapeHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.IwInvT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PConvSupp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeedOrbKVanish
import Development.AutomorphicArithmetic.IwahoriCommensurability.IwahoriDoubleCosetTorusMulOfStrictAnti
import Development.AutomorphicArithmetic.IwahoriCommensurability.IsCommensuratedIwahoriSubgroupGlFin
import Development.AutomorphicArithmetic.IwahoriCommensurability.CharpolySmulSeparable
import Development.AutomorphicArithmetic.IwahoriCommensurability.ExistsLevelSubgroupCentralScalarOfPos
import Development.AutomorphicArithmetic.IwahoriCommensurability.ExistsPrimePowScalarIntegralOfGoodPrime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.MemFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CLocEqOneOfNotOverPair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.T2SpaceAfP
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AdmCusp

section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw invT_val invT_invT')
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc

private theorem continuous_invT' {n : ℕ} {R : Type} [CommRing R] [TopologicalSpace R] :
    Continuous (invT n R : GL (Fin n) R → GL (Fin n) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_coe_inv.matrix_transpose
  · have e : (fun g : GL (Fin n) R => ((invT n R g)⁻¹ : GL (Fin n) R).val) = fun g => g.valᵀ := by
      funext g
      rw [← map_inv, invT_val, inv_inv]
    rw [e]
    exact Units.continuous_val.matrix_transpose

private theorem tyTop_of (hF : KNFact) (hG : CongGrpEx) (hC : CuspTh) : TyTop := by
  intro E _ _ _ A n p _ S F x U w₀ Up V _ _ _ _ hq r W _ N _ _ L hw Ty hT
  obtain ⟨q, hq, hgood, hqw⟩ := hq
  have hN : 0 < N.1 := lt_of_lt_of_le (by norm_num) N.2.1
  have hJ : ∀ y : GLw n w₀, y ∈ Ty.J ↔ invT n _ y ∈ V.J := fun y => hT.J_iff y _ (invT_val y)
  have hJo : IsOpen (V.J : Set (GLw n w₀)) := V.Kw0 ▸ V.shape.opn w₀ V.shape.mem
  have hJc : IsCompact (V.J : Set (GLw n w₀)) := V.Kw0 ▸ V.shape.cpt w₀ V.shape.mem
  refine ⟨GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p _ _ S.L N.1 hN, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨K, hK, ho, hc, -⟩ := hG E n N.1 hN w₀
    refine ⟨K, ho, hc, ?_⟩
    rw [hT.L_eq, hT.K₀_eq]
    exact hF E A n p S F ⟨w₀, hw⟩ _ (hT.fac _) q hq hgood hqw N.1 hN K hK
  · have e : (Ty.J : Set (GLw n w₀)) = invT n _ ⁻¹' (V.J : Set (GLw n w₀)) := Set.ext hJ
    rw [e]
    exact hJo.preimage continuous_invT'
  · have e : (Ty.J : Set (GLw n w₀)) = invT n _ '' (V.J : Set (GLw n w₀)) := by
      ext y
      constructor
      · intro hy
        exact ⟨_, (hJ y).1 hy, invT_invT' y⟩
      · rintro ⟨y', hy', rfl⟩
        exact (hJ _).2 (by rwa [invT_invT'])
    rw [e]
    exact hJc.image continuous_invT'
  · have hc : Continuous (fun y : Ty.J => (⟨invT n _ y.1, (hJ y.1).1 y.2⟩ : V.J)) :=
      (continuous_invT'.comp continuous_subtype_val).subtype_mk _
    have e : (Ty.ψ.ker : Set Ty.J) =
        (fun y : Ty.J => (⟨invT n _ y.1, (hJ y.1).1 y.2⟩ : V.J)) ⁻¹' {k : V.J | V.χ k = 1} := by
      ext y
      have h := hT.ψ_eq y ⟨invT n _ y.1, (hJ y.1).1 y.2⟩ (invT_val y.1)
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq, h]
    rw [e]
    exact V.ker_open.preimage hc
  · intro σ v hv hσ
    obtain ⟨σ', e, he, hcusp⟩ := hC E n w₀ σ
    refine hcusp (V.cusp σ' (e v) (fun h => hv (e.map_eq_zero_iff.1 h)) fun g => ?_)
    have hg : invT n _ g.1 ∈ Ty.J := (hJ _).2 (by rw [invT_invT']; exact g.2)
    have hval : (g : GLw n w₀).val = ((invT n _ g.1)⁻¹).valᵀ := by
      rw [← invT_val, invT_invT']
    rw [he _ _ v hval, hσ ⟨_, hg⟩, map_smul, hT.ψ_eq ⟨_, hg⟩ g hval]

theorem UpperTheory.Gal.Spc.tyTop :
    UpperTheory.Gal.Spc.TyTop :=
  tyTop_of (pKNFact (pKNIff (pLatCoord pRepLaws)) pFacEq (pAtApart pJEq) pCongGrpEx (pCongConj UpperTheory.Gal.CertificateRingHomMap.pLocComm_of) pLocComm
    UpperTheory.Gal.CertificateRingHomMap.pLocComm_of) pCongGrpEx pCuspTh
end

section
set_option autoImplicit false

noncomputable section

open Formalism.UG GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal Matrix

namespace UpperTheory.Gal.Spc.Iw

private def LI {G : Type} [Group G] (K : Subgroup G) (g : G) : Prop :=
  ∃ φ ∈ Hecke ℂ K, conv K φ (dosetInd ℂ K g) = dosetInd ℂ K 1


private theorem LI.one {G : Type} [Group G] (K : Subgroup G) : LI K (1 : G) :=
  ⟨_, Final.DosetIndMem G K ℂ 1, (Final.HeckeUnit G K ℂ _ (Final.DosetIndMem G K ℂ 1)).1⟩

private def Qr {G : Type} [Group G] (K : Subgroup G) (g : G) : Prop := ∀ h, LI K h → LI K (h * g)

private theorem Qr.one {G : Type} [Group G] (K : Subgroup G) : Qr K (1 : G) := fun h hh => by simpa using hh

private theorem Qr.mul {G : Type} [Group G] {K : Subgroup G} {g g' : G} (a : Qr K g) (b : Qr K g') : Qr K (g * g') :=
  fun h hh => by simpa [mul_assoc] using b _ (a h hh)

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ)

private abbrev tau : GL (Fin (m + 1)) k :=
  diagPow k (m + 1) (Pi.mulSingle (Fin.last m) (Multiplicative.ofAdd 1)) * permGL k (finRotate (m + 1))⁻¹

private def goodDiag : Subgroup (Fin (m + 1) → Multiplicative ℤ) where
  carrier := {a | Qr (iwahori k (m + 1)) (diagPow k (m + 1) a) ∧ Qr (iwahori k (m + 1)) (diagPow k (m + 1) a⁻¹)}
  one_mem' := by simpa using Qr.one _
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by simpa using ha.mul hb, ?_⟩
    rw [_root_.mul_inv_rev, map_mul]
    exact hb'.mul ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by simpa using ha⟩

end Local

end UpperTheory.Gal.Spc.Iw
end
end

section
noncomputable section

open Formalism.UG (Hecke conv dosetInd IsCommensurated)
open UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.Spc

variable {X M M' : Type} [Group X] [Group M] [Group M']

private theorem fin_out {K : Subgroup X} (hK : IsCommensurated K) {f : X → ℂ} (hf : f ∈ Hecke ℂ K) (c : X ⧸ K → ℂ) :
    (Function.support fun q : X ⧸ K => f q.out * c q).Finite := by
  refine (GlobalTheory.LFun.finite_heckeVec hK hf (1 : Representation ℂ X ℂ) 1).subset fun q hq => ?_
  simpa using left_ne_zero_of_mul hq

private theorem conv_add {K : Subgroup X} (hK : IsCommensurated K) {f f' : X → ℂ} (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K)
    (y : X → ℂ) (g : X) : conv K (f + f') y g = conv K f y g + conv K f' y g := by
  simp only [conv, Pi.add_apply, add_mul]
  exact finsum_add_distrib (fin_out hK hf _) (fin_out hK hf' _)

private theorem conv_smul (K : Subgroup X) (r : ℂ) (f y : X → ℂ) (g : X) : conv K (r • f) y g = r * conv K f y g := by
  simp only [conv, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_finsum]

private theorem ind_one (K : Subgroup X) (g : X) : conv K (dosetInd ℂ K 1) (dosetInd ℂ K 1) g = dosetInd ℂ K 1 g := by
  have h1 : ∀ x, x ∈ DoubleCoset.doubleCoset (1 : X) (K : Set X) K ↔ x ∈ K := fun x => by
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨by rintro ⟨a, ha, b, hb, rfl⟩; exact mul_mem (mul_mem ha (one_mem K)) hb, fun h => ⟨x, h, 1, one_mem K, by simp⟩⟩
  have h0 : ((1 : X) : X ⧸ K).out ∈ K := by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (1 : X)
    rw [hk, one_mul]
    exact k.2
  rw [conv, finsum_eq_single _ ((1 : X) : X ⧸ K) fun q hq => ?_]
  · rw [dosetInd, Set.indicator_of_mem ((h1 _).2 h0), Pi.one_apply, one_mul]
    by_cases hg : g ∈ K
    · rw [Set.indicator_of_mem ((h1 _).2 hg), Set.indicator_of_mem ((h1 _).2 (mul_mem (inv_mem h0) hg))]
      rfl
    · rw [Set.indicator_of_notMem (mt (h1 _).1 hg), Set.indicator_of_notMem fun h => hg ?_]
      simpa using mul_mem h0 ((h1 _).1 h)
  · rw [dosetInd, Set.indicator_of_notMem fun h => hq ?_, zero_mul]
    rw [← q.out_eq', QuotientGroup.eq]
    simpa using (h1 _).1 h

private theorem lift_ex (T : TyLev X M) (L : Loc X M') (I : Subgroup M') (h1 : L.Fact T.K I) (h2 : T.L.Apart L) (hI : IsCommensurated I)
    (t : M') {φ : M' → ℂ} (hφ : φ ∈ Hecke ℂ I) : ∃ v ∈ Hecke ℂ T.K₀, ∀ g, conv T.K₀ v (T.tf (L.loc t)) g =
      T.tf 1 (g * (L.loc (L.pr g))⁻¹) * conv I φ (dosetInd ℂ I t) (L.pr g) := by
  refine GlobalTheory.LFun.hecke_induction (p := fun φ => ∃ v ∈ Hecke ℂ T.K₀, ∀ g, conv T.K₀ v (T.tf (L.loc t)) g =
      T.tf 1 (g * (L.loc (L.pr g))⁻¹) * conv I φ (dosetInd ℂ I t) (L.pr g)) ⟨0, zero_mem _, fun g => by simp [conv]⟩ ?_ ?_ hφ
  · rintro f hf f' hf' ⟨v, hv, e⟩ ⟨v', hv', e'⟩
    exact ⟨v + v', add_mem hv hv', fun g => by rw [conv_add T.cms hv hv', conv_add hI hf hf', e, e', mul_add]⟩
  · intro r s
    refine ⟨r • T.tf (L.loc s), Submodule.smul_mem _ _ (pTfAdm X M T _ (h2.1 s)).1.1, fun g => ?_⟩
    rw [conv_smul, conv_smul, tfLoc_holds X M M' T L I h1 h2, mul_left_comm]

private theorem inv_ex (T : TyLev X M) (L : Loc X M') (I : Subgroup M') (h1 : L.Fact T.K I) (h2 : T.L.Apart L) (hI : IsCommensurated I)
    (t : M') {φ : M' → ℂ} (hφ : φ ∈ Hecke ℂ I) (e : conv I φ (dosetInd ℂ I t) = dosetInd ℂ I 1) :
    ∃ v ∈ Hecke ℂ T.K₀, conv T.K₀ v (T.tf (L.loc t)) = T.tf 1 := by
  obtain ⟨v, hv, h⟩ := lift_ex T L I h1 h2 hI t hφ
  refine ⟨v, hv, funext fun g => ?_⟩
  have h3 := tfLoc_holds X M M' T L I h1 h2 1 1 g
  rw [map_one, (tfIdem_holds X M T 1 (map_one _)).2.1, ind_one] at h3
  rw [h, e, ← h3]

theorem exists_invertible_hecke_function_at_finite_places : ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (ι : Type) (M' : ι → Type) [∀ w, Group (M' w)] (L : ∀ w, Loc X (M' w))
    (I : ∀ w, Subgroup (M' w)) (t : ∀ w, M' w) (W : Finset ι),
    (∀ w ∈ W, (L w).Fact T.K (I w) ∧ T.L.Apart (L w) ∧ ∀ w' ∈ W, w ≠ w' → (L w).Apart (L w')) →
    (∀ w ∈ W, IsCommensurated (I w) ∧ ∃ φ ∈ Hecke ℂ (I w), conv (I w) φ (dosetInd ℂ (I w) (t w)) = dosetInd ℂ (I w) 1) →
    ∃ τ ∈ Subgroup.closure {y | ∃ w ∈ W, y = (L w).loc (t w)}, T.L.pr τ = 1 ∧ (∀ w ∈ W, (L w).pr τ = t w) ∧
      (∀ h, T.L.pr h = 1 → (∀ w ∈ W, (L w).pr h = 1) → conv T.K₀ (T.tf τ) (T.tf h) = conv T.K₀ (T.tf h) (T.tf τ)) ∧
      ∃ u' ∈ Hecke ℂ T.K₀, conv T.K₀ u' (T.tf τ) = T.tf 1 := by
  intro X M _ _ T ι M' _ L I t W
  classical
  induction W using Finset.induction_on with
  | empty =>
    refine fun _ _ => ⟨1, one_mem _, map_one _, by simp, fun h hh _ => ?_, T.tf 1, (pTfAdm X M T 1 (map_one _)).1.1,
      (tfIdem_holds X M T 1 (map_one _)).2.1⟩
    rw [(tfIdem_holds X M T h hh).2.1, (tfIdem_holds X M T h hh).2.2]
  | insert w W hw ih =>
    intro h1 h2
    obtain ⟨τ, m, p0, p1, c, u, hu, e⟩ := ih
      (fun x hx => ⟨(h1 x (Finset.mem_insert_of_mem hx)).1, (h1 x (Finset.mem_insert_of_mem hx)).2.1,
        fun y hy => (h1 x (Finset.mem_insert_of_mem hx)).2.2 y (Finset.mem_insert_of_mem hy)⟩)
      fun x hx => h2 x (Finset.mem_insert_of_mem hx)
    obtain ⟨f1, f2, f3⟩ := h1 w (Finset.mem_insert_self w W)
    obtain ⟨g1, φ, g2, g3⟩ := h2 w (Finset.mem_insert_self w W)
    have ap : ∀ x ∈ W, (L w).Apart (L x) := fun x hx => f3 x (Finset.mem_insert_of_mem hx) fun h => hw (h ▸ hx)
    have q : (L w).pr τ = 1 := (Subgroup.closure_le (L w).pr.ker).2 (by rintro _ ⟨x, hx, rfl⟩; exact (ap x hx).1 _) m
    obtain ⟨v, hv, ev⟩ := inv_ex T (L w) (I w) f1 f2 g1 (t w) g2 g3
    have a1 := (pTfAdm X M T _ (f2.1 (t w))).1.1
    have a2 := (pTfAdm X M T τ p0).1.1
    have R := pConvRing X T.K₀ T.cms
    have e1 := tfMulL_holds X M _ T (L w) (I w) f1 f2 (t w) τ p0 q
    refine ⟨(L w).loc (t w) * τ, mul_mem (Subgroup.subset_closure ⟨w, Finset.mem_insert_self w W, rfl⟩)
      (Subgroup.closure_mono (by rintro _ ⟨x, hx, rfl⟩; exact ⟨x, Finset.mem_insert_of_mem hx, rfl⟩) m),
      by rw [map_mul, f2.1, p0, one_mul], fun x hx => ?_, fun h hh hW => ?_, conv T.K₀ u v, (R u hu v hv).1, ?_⟩
    · rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [map_mul, (L x).pr_loc, q, mul_one]
      · rw [map_mul, (ap x hx).2, p1 x hx, one_mul]
    · have a3 := (pTfAdm X M T h hh).1.1
      have hw1 := hW w (Finset.mem_insert_self w W)
      rw [← e1, (R _ a1 _ a2).2 _ a3, c h hh fun x hx => hW x (Finset.mem_insert_of_mem hx), ← (R _ a1 _ a3).2 _ a2,
        tfMulL_holds X M _ T (L w) (I w) f1 f2 (t w) h hh hw1, ← tfMulR_holds X M _ T (L w) (I w) f1 f2 (t w) h hh hw1,
        (R _ a3 _ a1).2 _ a2]
    · rw [← e1, (R u hu v hv).2 _ (R _ a1 _ a2).1, ← (R v hv _ a1).2 _ a2, ev, (tfIdem_holds X M T τ p0).2.2, e]

end UpperTheory.Gal.Spc
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj GLw)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open Formalism.UG (Hecke conv dosetInd IsCommensurated)
open scoped Classical

namespace UpperTheory.Gal.Spc

section Abstract

variable {X : Type} [Group X]

private def trl (z : X) (f : X → ℂ) : X → ℂ := fun g => f (z * g)

private theorem trl_mem {K : Subgroup X} {z : X} (hz : ∀ g, z * g = g * z) {f : X → ℂ} (hf : f ∈ Hecke ℂ K) :
    trl z f ∈ Hecke ℂ K := by
  obtain ⟨hb, S, hS⟩ := hf
  refine ⟨fun a b g => ?_, S.image (z⁻¹ * ·), fun g hg => ?_⟩
  · show f (z * (a * g * b)) = f (z * g)
    rw [← hb a b (z * g), ← mul_assoc, ← mul_assoc, hz a, mul_assoc (a : X) z g]
  · obtain ⟨s, hs, a, b, e⟩ := hS _ hg
    refine ⟨z⁻¹ * s, Finset.mem_image_of_mem _ hs, a, b, ?_⟩
    have h1 : (a : X) * z⁻¹ = z⁻¹ * a := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hz a, inv_mul_cancel_left]
    rw [← mul_assoc, h1, mul_assoc z⁻¹, mul_assoc z⁻¹, ← e, inv_mul_cancel_left]

private theorem conv_trl_right (K : Subgroup X) {z : X} (hz : ∀ g, z * g = g * z) (f f' : X → ℂ) :
    conv K f (trl z f') = trl z (conv K f f') := by
  funext g
  unfold conv trl
  refine finsum_congr fun x => ?_
  rw [← mul_assoc, hz, mul_assoc]

private theorem conv_trl_left {K : Subgroup X} (z : X) {f f' : X → ℂ} (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) :
    conv K (trl z f) f' = trl z (conv K f f') := by
  funext g
  unfold conv trl
  beta_reduce
  rw [← finsum_comp_equiv (MulAction.toPerm z : X ⧸ K ≃ X ⧸ K) (f := fun x : X ⧸ K => f x.out * f' (x.out⁻¹ * (z * g)))]
  refine finsum_congr fun y => ?_
  have hy : (MulAction.toPerm z : X ⧸ K ≃ X ⧸ K) y = (QuotientGroup.mk (z * y.out) : X ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' y]
    rfl
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (z * y.out)
  simp only [hy, hh]
  congr 1
  · simpa using (hf.1 1 h (z * y.out)).symm
  · rw [← hf'.1 h⁻¹ 1 (y.out⁻¹ * g)]
    congr 1
    simp only [Subgroup.coe_inv, OneMemClass.coe_one]
    group

private theorem comm_span {K : Subgroup X} (hK : IsCommensurated K) {u : X → ℂ} (hu : u ∈ Hecke ℂ K) {s : Set (X → ℂ)}
    (hs : ∀ f ∈ s, f ∈ Hecke ℂ K ∧ conv K u f = conv K f u) :
    ∀ f ∈ Submodule.span ℂ s, f ∈ Hecke ℂ K ∧ conv K u f = conv K f u := by
  have fin : ∀ a ∈ Hecke ℂ K, ∀ b : X ⧸ K → ℂ, (Function.support fun x : X ⧸ K => a x.out * b x).Finite := fun a ha b =>
    (Formalism.UG.P.finite_support_cosets hK ha.2).subset fun x hx => left_ne_zero_of_mul hx
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f h => exact hs f h
  | zero => exact ⟨zero_mem _, by funext g; simp [conv]⟩
  | add f f' _ _ h h' =>
    refine ⟨add_mem h.1 h'.1, funext fun g => ?_⟩
    have e := congrFun h.2 g
    have e' := congrFun h'.2 g
    unfold conv at e e' ⊢
    simp only [Pi.add_apply, mul_add, add_mul]
    rw [finsum_add_distrib (fin u hu _) (fin u hu _), finsum_add_distrib (fin f h.1 _) (fin f' h'.1 _), e, e']
  | smul c f _ h =>
    refine ⟨Submodule.smul_mem _ c h.1, funext fun g => ?_⟩
    have e := congrFun h.2 g
    unfold conv at e ⊢
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm _ c]
    rw [← mul_finsum, ← mul_finsum, e]

private theorem tf_supp {M : Type} [Group M] (T : TyLev X M) {h g : X} (e : T.tf h g ≠ 0) :
    ∃ a ∈ T.K, ∃ b ∈ T.K, g = a * h * b := by
  refine DoubleCoset.mem_doubleCoset.1 ?_
  by_contra hn
  apply e
  simp [TyLev.tf, dosetInd, Set.indicator_of_notMem hn]

end Abstract

private theorem locT (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∃ t : GL (Fin n) k,
      (∃ φ ∈ Hecke ℂ (GlobalTheory.SmGL.iwahori k (Fin n)), conv (GlobalTheory.SmGL.iwahori k (Fin n)) φ (dosetInd ℂ (GlobalTheory.SmGL.iwahori k (Fin n)) t) =
        dosetInd ℂ (GlobalTheory.SmGL.iwahori k (Fin n)) 1) ∧
      (∀ m : ℕ, ∀ a ∈ DoubleCoset.doubleCoset t (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)),
        ∀ b ∈ DoubleCoset.doubleCoset (t ^ m) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)),
        a * b ∈ DoubleCoset.doubleCoset (t ^ (m + 1)) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n))) ∧
      ∀ m : ℕ, 1 ≤ m →
        ∀ y ∈ DoubleCoset.doubleCoset (t ^ m) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)),
          y.val.charpoly.Separable := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer k)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact ValuativeRel.uniformizer_ne_zero hx.symm
  have hν : StrictAnti fun i : Fin n => -(i : ℤ) := fun i j hij => by
    have : (i : ℕ) < j := hij
    show -((j : ℕ) : ℤ) < -((i : ℕ) : ℤ)
    omega
  refine ⟨_, CertificateRingHomMap.iwInvT k n (Units.mk0 x hx0) hx _ hν.antitone, UpperTheory.iwahori_doubleCoset_torus_mul_of_strictAnti k n (Units.mk0 x hx0) hx _ hν, fun m hm y hy => ?_⟩
  rw [GlobalTheory.TorusElementPower.torusElt_pow_eq] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  exact (GlobalTheory.IwahoriRegular.regular_split k n (Units.mk0 x hx0) hx _
    (fun i j hij => mul_lt_mul_of_pos_left (hν hij) hm') a ha b hb).1

private theorem integ_mul {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {a b : G.GAf}
    (ha : Integ L a) (hb : Integ L b) : Integ L (a * b) := fun v hv => by
  rw [map_mul, Module.End.mul_apply]
  exact ha _ (hb v hv)

private theorem scal_comm {k : Type} [Field k] {n : ℕ} {s : GL (Fin n) k} {a : k} (hs : s.val = a • (1 : Matrix (Fin n) (Fin n) k))
    (y : GL (Fin n) k) : Commute s y :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, hs, smul_mul_assoc, mul_smul_comm, one_mul, mul_one])

private theorem scal_sep {k : Type} [Field k] {n : ℕ} {s : GL (Fin n) k} {a : k} (ha : a ≠ 0)
    (hs : s.val = a • (1 : Matrix (Fin n) (Fin n) k)) (m : ℕ) (y : GL (Fin n) k) (h : (s ^ m * y).val.charpoly.Separable) :
    y.val.charpoly.Separable := by
  have := UpperTheory.charpoly_smul_separable k n (a ^ m)⁻¹ (inv_ne_zero (pow_ne_zero m ha)) _ h
  rwa [Units.val_mul, Units.val_pow_eq_pow_val, hs, _root_.smul_pow, one_pow, smul_mul_assoc, one_mul, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero m ha), one_smul] at this

private theorem cen_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    (F : Frame S) (c : ℕ) (hc : 0 < c) : ∃ d : GUf E n, (∀ g, F.j d * g = g * F.j d) ∧
      (∀ w : Plc E, (comp w d).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ∧
      ∀ v, S.L.actG (F.j d) v = c • v := by
  first
    | exact UpperTheory.exists_levelSubgroup_central_scalar_of_pos E A n p S F c hc
    | (obtain ⟨y, -, -, h1, -, h2, h3⟩ := UpperTheory.exists_levelSubgroup_central_scalar_of_pos E A n p S F c hc; exact ⟨_, h2, h1, h3⟩)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem auxFn : ExistsIdempotentHeckeOperatorWithRegularSupport := by
  intro E _ _ _ A n p _ S F x U w₀ Up V hn hsc hgen hoff hq r W hA N hrN hst L hw Ty hTy
  obtain ⟨hF, -, c, hc, -, hcK⟩ := tyFact E A n p S F x U w₀ Up V hn hsc hgen hoff hq r W hA N hrN hst L hw Ty hTy
  choose t hti htm hts using fun w : Spl E p => locT (w.1.adicCompletion E) n
  obtain ⟨τ, hτ, hτ0, hτw, hcm, u', hu', hu'τ⟩ := exists_invertible_hecke_function_at_finite_places _ _ Ty (Spl E p) (fun w => GLw n w.1) L (fun w => Iw n w.1) t W hF
    fun w _ => ⟨UpperTheory.isCommensurated_iwahoriSubgroup_gl_fin _ n, hti w⟩
  obtain ⟨g₀, hg₀, hg₀u⟩ : ∃ g₀ : GUf E n, F.j g₀ = τ⁻¹ ∧ ∀ u : Plc E, (r : 𝓞 E) ∉ u.asIdeal → comp u g₀ = 1 := by
    have hτ' := inv_mem hτ
    generalize τ⁻¹ = σ at hτ'
    haveI : Fact r.Prime := ⟨hA.prime⟩
    induction hτ' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨w, hwW, rfl⟩ := hy
      exact ⟨CertificateRingHomMap.loc w.2.1 (t w), ((hTy.fac w).2 _).symm, fun u hu =>
        CertificateRingHomMap.comp_loc_of_apart w.2.1 (Ne.symm (apart_of_not_mem hu (hA.half.above w hwW))) _⟩
    | one => exact ⟨1, map_one _, fun _ _ => map_one _⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a', rfl, ha⟩ := ha
      obtain ⟨b', rfl, hb⟩ := hb
      exact ⟨a' * b', map_mul _ _ _, fun u hu => by rw [map_mul, ha u hu, hb u hu, one_mul]⟩
    | inv a _ ha =>
      obtain ⟨a', rfl, ha⟩ := ha
      exact ⟨a'⁻¹, map_inv _ _, fun u hu => by rw [map_inv, ha u hu, inv_one]⟩
  obtain ⟨M, hM⟩ := UpperTheory.exists_primePow_scalar_integral_of_good_prime E A n p S F r hA.prime hA.good g₀ hg₀u
  obtain ⟨dc, hdc, hdcw, hdcv⟩ := cen_ex F c hc
  obtain ⟨dr, hdr, hdrw, -⟩ := cen_ex F (r ^ M) (pow_pos hA.prime.pos M)
  have hI := hM dr hdrw
  rw [map_mul, hg₀] at hI
  have hK : ∀ k ∈ Ty.K, Integ S.L (k * F.j dc) := fun k hk v hv => by
    rw [map_mul, Module.End.mul_apply, hdcv, map_nsmul]
    exact hcK k hk v hv
  obtain ⟨D, hD⟩ : ∃ D, D = F.j dc * F.j dr * F.j dc := ⟨_, rfl⟩
  have hDc : ∀ g, D * g = g * D := fun g => by
    rw [hD, mul_assoc, hdc g, ← mul_assoc, mul_assoc _ _ g, hdr g, ← mul_assoc, hdc g]
    simp only [mul_assoc]
  have hDc' : ∀ g, D⁻¹ * g = g * D⁻¹ := fun g => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hDc g, mul_inv_cancel_right]
  have hs : ∀ w : Spl E p, ((L w).pr D).val =
      ((c * r ^ M * c : ℕ) : w.1.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) := fun w => by
    rw [hD, ← map_mul, ← map_mul, (hTy.fac w).1, map_mul, map_mul, Units.val_mul, Units.val_mul, hdcw, hdrw]
    simp only [smul_mul_assoc, one_mul, smul_smul, Nat.cast_mul]
  have hs0 : ∀ w : Spl E p, ((c * r ^ M * c : ℕ) : w.1.adicCompletion E) ≠ 0 := fun w => by
    haveI : CharZero (w.1.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
    exact Nat.cast_ne_zero.2 (Nat.mul_pos (Nat.mul_pos hc (pow_pos hA.prime.pos M)) hc).ne'
  have hτH : Ty.tf τ ∈ Hecke ℂ Ty.K₀ := (pTfAdm _ _ Ty τ hτ0).1.1
  have h1H : Ty.tf 1 ∈ Hecke ℂ Ty.K₀ := (pTfAdm _ _ Ty 1 (map_one _)).1.1
  have hid := (tfIdem_holds _ _ Ty τ hτ0).2
  have hue : conv Ty.K₀ (trl D (Ty.tf τ)) (Ty.tf 1) = trl D (Ty.tf τ) := by rw [conv_trl_left D hτH h1H, hid.1]
  have hsupp : ∀ g, trl D (Ty.tf τ) g ≠ 0 → Integ S.L g⁻¹ ∧
      ∀ w ∈ W, (L w).pr D * (L w).pr g ∈ DoubleCoset.doubleCoset (t w) (Iw n w.1 : Set (GLw n w.1)) (Iw n w.1) := by
    intro g hg
    obtain ⟨a, ha, b, hb, e⟩ := tf_supp Ty hg
    refine ⟨?_, fun w hwW => ?_⟩
    · have e' : g⁻¹ = b⁻¹ * F.j dc * (τ⁻¹ * F.j dr * (a⁻¹ * F.j dc)) := by
        have e1 : g⁻¹ = b⁻¹ * τ⁻¹ * a⁻¹ * D := by
          rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, ← mul_assoc, ← e, _root_.mul_inv_rev, inv_mul_cancel_right]
        rw [e1, mul_assoc b⁻¹ (F.j dc), hdc, mul_assoc τ⁻¹, hdr, hD]
        simp only [mul_assoc]
      rw [e']
      exact integ_mul (hK _ (inv_mem hb)) (integ_mul hI (hK _ (inv_mem ha)))
    · rw [← map_mul, e, map_mul, map_mul, hτw w hwW]
      exact DoubleCoset.mem_doubleCoset.2 ⟨_, (hF w hwW).1.2 a ha, _, (hF w hwW).1.2 b hb, rfl⟩
  have hpow : ∀ m : ℕ, ∀ g, powFn Ty.K₀ (trl D (Ty.tf τ)) (Ty.tf 1) (m + 1) g ≠ 0 → Integ S.L g⁻¹ ∧
      ∀ w ∈ W, (L w).pr D ^ (m + 1) * (L w).pr g ∈
        DoubleCoset.doubleCoset (t w ^ (m + 1)) (Iw n w.1 : Set (GLw n w.1)) (Iw n w.1) := by
    intro m
    induction m with
    | zero =>
      intro g hg
      simp only [zero_add, pow_one]
      refine hsupp g ?_
      rw [← hue]
      exact hg
    | succ m ih =>
      intro g hg
      unfold powFn at hg
      rw [Function.iterate_succ_apply'] at hg
      obtain ⟨a, b, ha, hb, rfl⟩ := pConvSupp _ _ _ _ _ hg
      obtain ⟨a1, a2⟩ := hsupp a ha
      obtain ⟨b1, b2⟩ := ih b hb
      refine ⟨by rw [_root_.mul_inv_rev]; exact integ_mul b1 a1, fun w hwW => ?_⟩
      have := htm w (m + 1) _ (a2 w hwW) _ (b2 w hwW)
      rwa [mul_assoc, ← mul_assoc ((L w).pr a), ← ((scal_comm (hs w) ((L w).pr a)).pow_left (m + 1)).eq, mul_assoc,
        ← mul_assoc, ← pow_succ', ← map_mul] at this
  refine ⟨trl D (Ty.tf τ), trl_mem hDc hτH, trl D⁻¹ u', trl_mem hDc' hu', ?_, hue, ?_, fun f hf => ?_, fun m hm => ?_⟩
  · rw [conv_trl_right _ hDc, hid.2]
  · rw [conv_trl_left _ hu' (trl_mem hDc hτH), conv_trl_right _ hDc, hu'τ]
    funext g
    simp [trl]
  · obtain ⟨hfH, hfc⟩ := comm_span Ty.cms hτH (by
      rintro f ⟨h, h0, h1, rfl⟩
      exact ⟨(pTfAdm _ _ Ty h h0).1.1, hcm h h0 h1⟩) f hf
    rw [conv_trl_left D hτH hfH, conv_trl_right _ hDc, hfc]
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    refine ⟨fun w => {y | (L w).pr D ^ (m + 1) * y ∈
      DoubleCoset.doubleCoset (t w ^ (m + 1)) (Iw n w.1 : Set (GLw n w.1)) (Iw n w.1)}, fun w _ y hy => ⟨?_, fun a ha => ?_⟩, hpow m⟩
    · exact scal_sep (hs0 w) (hs w) _ y (hts w _ hm _ hy)
    · obtain ⟨a₁, h₁, a₂, h₂, e⟩ := DoubleCoset.mem_doubleCoset.1 hy
      refine DoubleCoset.mem_doubleCoset.2 ⟨a * a₁, mul_mem ha h₁, a₂, h₂, ?_⟩
      rw [← mul_assoc, ((scal_comm (hs w) a).pow_left (m + 1)).eq, mul_assoc, e]
      simp only [mul_assoc]

end UpperTheory.Gal.Spc
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw IsCen SameK)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open Formalism.UG (Hecke conv dosetInd IsCommensurated)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private theorem conv_smul_right {X : Type} [Group X] (K : Subgroup X) (f y : X → ℂ) (b : ℂ) :
    conv K f (b • y) = b • conv K f y := by
  funext g
  simp only [conv, Pi.smul_apply, smul_eq_mul]
  rw [← smul_eq_mul, smul_finsum]
  exact finsum_congr fun x => by simp only [smul_eq_mul]; ring

private theorem conv_smul_left {X : Type} [Group X] (K : Subgroup X) (x y : X → ℂ) (a : ℂ) :
    conv K (a • x) y = a • conv K x y := by
  funext g
  simp only [conv, Pi.smul_apply, smul_eq_mul]
  rw [← smul_eq_mul, smul_finsum]
  exact finsum_congr fun x => by simp only [smul_eq_mul]; ring

private theorem comm_of_scaled {X : Type} [Group X] (K : Subgroup X) (hK : IsCommensurated K) (hR : ConvRing)
    {e f f' x y : X → ℂ} {a b : ℂ} (he : e ∈ Hecke ℂ K) (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K)
    (hx : x ∈ Hecke ℂ K) (hy : y ∈ Hecke ℂ K) (hex : conv K e x = x) (hey : conv K e y = y)
    (h1 : conv K f e = a • x) (h2 : conv K f' e = b • y) (hxy : conv K x y = conv K y x) :
    conv K f (conv K f' e) = conv K f' (conv K f e) := by
  have e1 : conv K f y = a • conv K x y := by
    rw [← hey, ← (hR X K hK f hf e he).2 y hy, h1, conv_smul_left, hey]
  have e2 : conv K f' x = b • conv K y x := by
    rw [← hex, ← (hR X K hK f' hf' e he).2 x hx, h2, conv_smul_left, hex]
  rw [h2, h1, conv_smul_right, conv_smul_right, e1, e2, hxy, smul_comm]

private theorem tf_of_mem {X M : Type} [Group X] [Group M] (T : TyLev X M) {h : X} (hh : h ∈ T.K) : T.tf h = T.tf 1 := by
  have e : DoubleCoset.doubleCoset h (T.K : Set X) T.K = DoubleCoset.doubleCoset 1 (T.K : Set X) T.K :=
    DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨h, hh, 1, T.K.one_mem, by simp⟩)
  funext g
  simp only [TyLev.tf, dosetInd, e]

private theorem nat_not_mem {R : Type} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) {a b : ℕ} (hab : a.Coprime b)
    (ha : (a : R) ∈ I) : (b : R) ∉ I := by
  intro hb
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  have h : (u : R) * a + v * b = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → R) huv
  exact hI ((Ideal.eq_top_iff_one I).2 (h ▸ I.add_mem (I.mul_mem_left _ ha) (I.mul_mem_left _ hb)))

private theorem gl_comm_of_scalar {k : Type} [Field k] {n : ℕ} (A B : GL (Fin n) k) (c : k)
    (h : A.val = c • (1 : Matrix (Fin n) (Fin n) k)) : A * B = B * A := by
  apply Units.ext
  simp [Units.val_mul, h]

private theorem tf_facts : TfAdm ∧ TfIdem ∧ TfComm := by
  have hCen : TfCen := pTfCen pAvgK pTfAdm
  have hIdem : TfIdem := pTfIdem pTfAdm hCen
  have hAct : TfAct := pTfAct pAvgK pDosetCosets pTfAdm
  have hMulCen : TfMulCen := pTfMulCen pTfAdm hCen hIdem
  have hMulL : TfMulL := pTfMulL pTfAdm hAct pDosetIff
  have hMulR : TfMulR := pTfMulR pAvgK pTfAdm pDosetIff
  have hLoc : TfLoc := pTfLoc pTfAdm hAct pDosetIff
  exact ⟨pTfAdm, hIdem, pTfComm pTfAdm pConvRing hMulCen hMulL hMulR hLoc⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

private theorem cen_comm (F : Frame S) {x : E} {w : Plc E} {z : GUf E n} (hz : IsCen x w z) (g : S.G.GAf) :
    Commute (F.j z) g := by
  obtain ⟨g', rfl⟩ := F.surj g
  show F.j z * F.j g' = F.j g' * F.j z
  rw [← map_mul, ← map_mul, F.j_tr]
  refine (F.tr.j_eq _ _).2 fun u _ => ?_
  rw [map_mul, map_mul]
  by_cases h : SameK x (cj u) w
  · exact gl_comm_of_scalar _ _ _ ((hz u).1 h)
  · rw [(hz u).2 h]; simp

private theorem place_cases {w u : Plc E} (hne : cj w ≠ w) (h : ¬ GlobalTheory.Cong.Apart u w) : u = w ∨ u = cj w := by
  have h' : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := not_not.1 h
  exact GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq E w (cj w) u hne (GlobalTheory.DefU.LocRet.under_conjSrc w) h'

private theorem not_sameK_ne {x : E} {w : Plc E} (h : ¬ SameK x (cj w) w) : cj w ≠ w := by
  intro e
  apply h
  rw [e]
  exact fun _ _ => Iff.rfl

private theorem apart_of_primes {w u : Plc E} {a b : ℕ} (hab : a.Coprime b) (ha : (a : 𝓞 E) ∈ w.asIdeal)
    (hb : (b : 𝓞 E) ∈ u.asIdeal) : GlobalTheory.Cong.Apart w u := by
  intro h
  have h1 : (b : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap _ (𝓞 E) (b : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
    simpa using hb
  rw [← h] at h1
  have h2 : algebraMap _ (𝓞 E) (b : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal := h1
  exact nat_not_mem w.isPrime.ne_top hab ha (by simpa using h2)

private theorem comp_cj_ofU (w : Plc E) (a b : finU E n)
    (h : comp w (CertificateRingHomMap.ofU a) = comp w (CertificateRingHomMap.ofU b)) : comp (cj w) (CertificateRingHomMap.ofU a) = comp (cj w) (CertificateRingHomMap.ofU b) := by
  have ha := GlobalTheory.LadicPair.cT_cLoc_conjSrc_mul a.1 w
  have hb := GlobalTheory.LadicPair.cT_cLoc_conjSrc_mul b.1 w
  have h' : cLoc w a.1 = cLoc w b.1 := h
  rw [h'] at ha
  have e := (Units.mul_left_inj (cLoc w b.1)).1 (ha.trans hb.symm)
  have e2 := Matrix.map_injective (RingHom.injective _) (Matrix.transpose_injective e)
  exact Units.ext e2

private def Sh {w₀ : Plc E} (L : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1)) (Ty : TyLev S.G.GAf (GLw n w₀)) (x : E)
    (h : S.G.GAf) : Prop :=
  ∃ (w : Spl E p) (t : GLw n w.1) (Z : S.G.GAf), h = (L w).loc t * Z ∧ Ty.Cen Z ∧
    (L w).Fact Ty.K (GlobalTheory.LFun.KGL w.1 n) ∧ Ty.L.Apart (L w) ∧ ¬ SameK x (cj w.1) w.1

private theorem sh_comm (F : Frame S) {w₀ : Plc E} {x : E} {L : ∀ w : Spl E p, Loc S.G.GAf (GLw n w.1)}
    {Ty : TyLev S.G.GAf (GLw n w₀)} (hfac : ∀ w, IsFac F w (L w)) {h h' : S.G.GAf} (hh : Sh L Ty x h) (hh' : Sh L Ty x h') :
    conv Ty.K₀ (Ty.tf h) (Ty.tf h') = conv Ty.K₀ (Ty.tf h') (Ty.tf h) := by
  obtain ⟨w, t, Z, rfl, hZ, hf, ha, hs⟩ := hh
  obtain ⟨w', t', Z', rfl, hZ', hf', ha', hs'⟩ := hh'
  have hC := tf_facts.2.2
  by_cases hap : GlobalTheory.Cong.Apart w'.1 w.1
  · have hLL : (L w).Apart (L w') := by
      constructor
      · intro y
        rw [(hfac w').2, (hfac w).1]
        exact CertificateRingHomMap.comp_loc_of_apart w'.2.1 (Ne.symm hap) y
      · intro y
        rw [(hfac w).2, (hfac w').1]
        exact CertificateRingHomMap.comp_loc_of_apart w.2.1 hap y
    exact (hC _ _ _ _ Ty (L w) _ hf ha Z Z' hZ hZ' t).1 (L w') t' ha' hLL
  · rcases place_cases (not_sameK_ne hs) hap with e | e
    · have e' : w' = w := Subtype.ext e
      subst e'
      exact (hC _ _ _ (GLw n w'.1) Ty (L w') _ hf ha Z Z' hZ hZ' t).2 t' (pSphComm E n w'.1 t t')
    · have hloc : (L w').loc t' = (L w).loc (comp w.1 (CertificateRingHomMap.loc w'.2.1 t')) := by
        rw [(hfac w').2, (hfac w).2, F.j_tr]
        refine (F.tr.j_eq _ _).2 fun u _ => ?_
        by_cases hu : GlobalTheory.Cong.Apart u w.1
        · have hu' : GlobalTheory.Cong.Apart u w'.1 := fun e2 => hu (e2.trans (not_not.1 hap))
          rw [CertificateRingHomMap.comp_loc_of_apart w.2.1 hu, CertificateRingHomMap.comp_loc_of_apart w'.2.1 hu']
        · rcases place_cases (not_sameK_ne hs) hu with rfl | rfl
          · rw [CertificateRingHomMap.comp_loc]
          · exact comp_cj_ofU w.1 (CertificateRingHomMap.locF w'.2.1 t') (CertificateRingHomMap.locF w.2.1 _) (CertificateRingHomMap.comp_loc w.2.1 _).symm
      rw [hloc]
      exact (hC _ _ _ (GLw n w.1) Ty (L w) _ hf ha Z Z' hZ hZ' t).2 _ (pSphComm E n w.1 _ _)

theorem memComm : UpperTheory.Gal.Spc.MemComm := by
  intro E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq r W hAux N hN hStab L hw Ty hTy g g' θ θ' hs hs'
  obtain ⟨hAdm, hIdem, -⟩ := tf_facts
  have hMF := UpperTheory.Gal.Spc.memFn E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W hAux N hN hStab L hw Ty hTy
  have hTF := UpperTheory.Gal.Spc.tyFact E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W hAux N hN hStab L hw Ty hTy
  have hOff : ∀ (g : Mem S.L N) (θ : ℂ), Seen F V r g θ → conv Ty.K₀ g.fn (Ty.tf 1) ∈ Off2 W L Ty := by
    intro g θ hs
    obtain ⟨-, -, hb⟩ := hMF g θ hs
    rcases hb with ⟨-, -, he⟩ | ⟨hpr, hW, he⟩
    · rw [he]
      exact Submodule.subset_span ⟨1, map_one _, fun w _ => map_one _, rfl⟩
    · rw [he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨g.h⁻¹, by simp [hpr], fun w hw => by simp [hW w hw], rfl⟩)
  have key : ∀ (g : Mem S.L N) (θ : ℂ), Seen F V r g θ → ∃ (a : ℂ) (h : S.G.GAf),
      conv Ty.K₀ g.fn (Ty.tf 1) = a • Ty.tf h ∧ Ty.L.pr h = 1 ∧ (h = 1 ∨ Sh L Ty x h) := by
    intro g θ hs
    obtain ⟨-, -, hb⟩ := hMF g θ hs
    rcases hb with ⟨-, -, he⟩ | ⟨hpr, hW, he⟩
    · exact ⟨1, 1, by rw [he, one_smul], map_one _, Or.inl rfl⟩
    · rcases hs with ⟨-, ⟨k', hk', hlev, -⟩, -, -⟩ | ⟨w, σ, i, B, hfree, hqr, -, htm, -, -⟩
      · have hK : g.h ∈ Ty.K := (hTy.K_iff _).2
          ⟨⟨k', hk', hlev⟩, fun w hw => by rw [hW w hw]; exact one_mem _⟩
        exact ⟨idx g, 1, by rw [he, tf_of_mem Ty (Ty.K.inv_mem hK)], map_one _, Or.inl rfl⟩
      · obtain ⟨-, -, hIsH, -⟩ := htm
        obtain ⟨hw', t, z, -, hcen, hh⟩ := hIsH
        have hqw : (σ.q : 𝓞 E) ∈ w.asIdeal := σ.atp.le (Ideal.subset_span (Or.inl rfl))
        have hp : (p : 𝓞 E) ∉ w.asIdeal :=
          nat_not_mem w.isPrime.ne_top ((Nat.coprime_primes σ.atp.prime Fact.out).2 σ.atp.ne) hqw
        obtain ⟨wS, hwS⟩ : ∃ wS : Spl E p, wS = ⟨w, hw', hp⟩ := ⟨_, rfl⟩
        have hap : ∀ u ∈ W, GlobalTheory.Cong.Apart wS.1 u.1 := fun u hu => by
          rw [hwS]
          exact apart_of_primes ((Nat.coprime_primes σ.atp.prime hAux.prime).2 hqr) hqw (hAux.half.above u hu)
        have hfr : wS.1 ∉ V.S ∧ cj wS.1 ∉ V.S ∧ ¬ SameK x (cj wS.1) wS.1 := by
          rw [hwS]
          exact ⟨hfree.2.1, hfree.2.2.1, hfree.2.2.2.2⟩
        obtain ⟨hfact, hTap⟩ := hTF.2.1 wS hfr.1 hfr.2.1 hap
        obtain ⟨t₁, ht₁⟩ : ∃ t₁ : GLw n wS.1, (L wS).loc t₁ = F.j (CertificateRingHomMap.loc hw' t) := by
          subst hwS
          exact ⟨t, (hTy.fac ⟨w, hw', hp⟩).2 t⟩
        obtain ⟨C, hCdef⟩ : ∃ C, C = F.j z ^ i := ⟨_, rfl⟩
        have hC : ∀ y, Commute C y := fun y => hCdef ▸ (cen_comm F hcen y).pow_left i
        have hgh : g.h = (L wS).loc t₁ * C := by rw [hh, map_mul, map_pow, ht₁, hCdef]
        have hprC : Ty.L.pr C = 1 := by
          have h1 := hpr
          rw [hgh, map_mul, hTap.1 t₁, one_mul] at h1
          exact h1
        have hinv : g.h⁻¹ = (L wS).loc t₁⁻¹ * C⁻¹ := by
          rw [hgh, map_inv, _root_.mul_inv_rev]
          exact ((hC _).inv_left.inv_right).eq
        exact ⟨idx g, g.h⁻¹, he, by simp [hpr], Or.inr ⟨wS, t₁⁻¹, C⁻¹, hinv,
          ⟨fun y => (hC y).inv_left.eq, by simp [hprC]⟩, hfact, hTap, hfr.2.2⟩⟩
  obtain ⟨a, h, e1, hp, hs1⟩ := key g θ hs
  obtain ⟨b, h', e2, hp', hs2⟩ := key g' θ' hs'
  refine ⟨hOff g θ hs, ?_⟩
  have he : Ty.tf 1 ∈ Hecke ℂ Ty.K₀ := (hAdm _ _ Ty 1 (map_one _)).1.1
  refine comm_of_scaled Ty.K₀ Ty.cms pConvRing he (hMF g θ hs).1 (hMF g' θ' hs').1 (hAdm _ _ Ty h hp).1.1
    (hAdm _ _ Ty h' hp').1.1 (hIdem _ _ Ty h hp).2.2 (hIdem _ _ Ty h' hp').2.2 e1 e2 ?_
  rcases hs1 with rfl | hs1
  · rw [(hIdem _ _ Ty h' hp').2.1, (hIdem _ _ Ty h' hp').2.2]
  · rcases hs2 with rfl | hs2
    · rw [(hIdem _ _ Ty h hp).2.1, (hIdem _ _ Ty h hp).2.2]
    · exact sh_comm F hTy.fac hs1 hs2

end UpperTheory.Gal.Spc
end
end

section
theorem UpperTheory.Gal.Spc.phiEx :
    UpperTheory.Gal.Spc.PhiEx :=
  UpperTheory.Gal.W2.Seed.phiEx_holds
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw Gam0 rat sim mat th th0 invT_val mem_lev comp_th sim_th th_rat)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open GlobalTheory.LFun (KGL)
open Formalism.UG (Hecke conv hAct)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private theorem frame_th {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]
    {S : Setup A n p} (F : Frame S) (g : GUf E n) : F.th g = th g :=
  Subtype.ext (Prod.ext (Units.ext (F.th_mat g)) (F.th_sim g))

private theorem th_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {n p : ℕ} (hn : 0 < n) (w₀ : Plc E) (S₀ : Finset (Plc E))
    (Kw : ∀ w : Plc E, Subgroup (GLw n w)) (hS : ∀ u ∈ S₀, (p : 𝓞 E) ∉ u.asIdeal) (k : GUf E n)
    (h1 : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) (h2 : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ KGL w n) :
    th k ∈ lev S₀ Kw := by
  have hall : ∀ w : Plc E, comp w k ∈ KGL w n := fun w => by
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · exact h2 w hw
    · rw [h1 w hw]; exact one_mem _
  have hsim : sim k ∈ CertificateRingHomMap.ZU := ((pIntConj E n k w₀ hn).2.1 hall)
  refine mem_lev.2 ⟨by rw [sim_th]; exact inv_mem hsim, fun w hw => ?_, fun w _ _ => ?_⟩
  · rw [comp_th, h1 w (hS w hw)]
    have : GlobalTheory.CuspRep.invT n _ (1 : GLw n w) = 1 := map_one _
    rw [this]; exact one_mem _
  · rw [comp_th]; exact CertificateRingHomMap.invT_mem_KGL (hall w)

theorem eigEx : EigEx := by
  intro E _ _ _ A n p _ S F x U w₀ Up V hn hSc hGen hOff hq r W hAux N hr hStab L hw Ty hTy
  refine ⟨(GlobalTheory.CuspRep.invT n E).prodMap invMonoidHom, fun y => ⟨rfl, rfl⟩, fun J g θ hg => ?_⟩
  obtain ⟨φ, hφ0, hφT, hφj, hφe⟩ := phiEx E A n p S F x U w₀ Up V hn hSc hGen hOff hq r W hAux N hr hStab L hw Ty hTy
  have hkey : ∀ h, V.Φ (th (F.tr.sec h)) = φ h := fun h => by
    have := hφj (F.tr.sec h) fun w hw => by rw [F.tr.sec_p h w hw]; exact one_mem _
    rw [frame_th, F.j_tr, F.tr.j_sec] at this
    exact this.symm
  have hfun : (fun h => V.Φ (th (F.tr.sec h))) = φ := funext hkey
  have hCen : Ty.Cen 1 := ⟨fun g => by simp, map_one _⟩
  refine pHasEigOf (pStdForm pMuStar) pPInt (pPPart pJEq) pExtP E A n p S F.tr _ ((CertificateRingHomMap.xi V.W V.jz).comp _) (fun g => V.Φ (th g))
    (fun γ g => ?_) (fun k h1 h2 g => ?_) ?_ Ty.K₀ Ty.cms (fun k hk h => ?_) J (fun j => (g j).fn) θ (Ty.tf 1)
    (fun j => (memFn E A n p S F x U w₀ Up V hn hSc hGen hOff hq r W hAux N hr hStab L hw Ty hTy (g j) (θ j) (hg j)).1)
    (pTfAdm _ _ Ty 1 (map_one _)).1.1 ?_ (fun j => ?_)
  · show V.Φ (th (rat γ * g)) = _
    rw [map_mul, th_rat, V.form.left]
    rfl
  · have hpos : Odd n → 0 < n := Odd.pos
    have hk := th_mem (hpos hn) w₀ V.S V.Kw hOff.1 k h1 h2
    have hw₀ : (p : 𝓞 E) ∉ w₀.asIdeal := hOff.1 _ V.shape.mem
    have hc : comp w₀ (th k) = 1 := by
      rw [comp_th, h1 w₀ hw₀]; exact map_one _
    have hJ : comp w₀ (th k) ∈ V.J := by rw [hc]; exact one_mem _
    show V.Φ (th (g * k)) = V.Φ (th g)
    have hr' := V.form.right (th k) hk hJ (th g)
    have hone : V.χ ⟨comp w₀ (th k), hJ⟩ = 1 := by
      have : (⟨comp w₀ (th k), hJ⟩ : V.J) = 1 := Subtype.ext hc
      rw [this, map_one]
    rw [map_mul, hr', hone]
    simp
  · obtain ⟨h, hh⟩ := Function.ne_iff.1 hφ0
    exact ⟨F.tr.sec h, by rw [hkey]; exact hh, fun w hw => by rw [F.tr.sec_p h w hw]; exact one_mem _⟩
  · rw [hkey, hkey, hφT k (Ty.le hk) h, Ty.ker k hk]
    simp
  · rw [hfun]
    funext a
    have := pTfCen pAvgK pTfAdm _ _ Ty 1 hCen _ φ hφT a
    simpa using this
  · rw [hfun]
    exact hφe (g j) (θ j) (hg j)

end UpperTheory.Gal.Spc
end
end

section
set_option autoImplicit false

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef
open GlobalTheory.CuspRep (pLoc)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw mat)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo.Pl
open scoped TensorProduct Classical Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private theorem small_of_nhds {E : Type} [Field E] [NumberField E] (w : Plc E) {U : Set (w.adicCompletion E)}
    (hU : U ∈ 𝓝 (0 : w.adicCompletion E)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : w.adicCompletion E, Valued.v x ≤ Valued.v (M : w.adicCompletion E) → x ∈ U := by
  obtain ⟨γ, -, hγ⟩ := (Valued.hasBasis_nhds_zero (w.adicCompletion E) _).mem_iff.1 hU
  have hball := (Valued.hasBasis_nhds_zero (w.adicCompletion E) _).mem_of_mem (i := γ) trivial
  have hN0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hlt : Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) < 1 := by
    have hm : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
    have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w _).2 hm
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) : E)) =
        w.valuation E (((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have h3 : algebraMap E (w.adicCompletion E) (((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) : E) =
        ((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) := by simp
    rw [h3] at h2
    rw [h2]
    exact h1
  obtain ⟨m, hm⟩ := ((Valued.tendsto_zero_pow_of_v_lt_one hlt).eventually hball).exists
  refine ⟨Ideal.absNorm w.asIdeal ^ m, Nat.pos_of_ne_zero (pow_ne_zero _ hN0), fun x hx => hγ ?_⟩
  have hx' : Valued.v x ≤ Valued.v (((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) ^ m) := by
    simpa using hx
  exact lt_of_le_of_lt ((Valuation.restrict_le_iff _).2 hx') hm

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.facCont :
    UpperTheory.Gal.Spc.FacCont := by
  intro E _ _ _ A n p _ S F w L hL
  have hI := pKNIff (pLatCoord pRepLaws)
  have key : ∀ M : ℕ, 0 < M → ∀ k ∈ S.L.KN M, Cong1 M w.1 (F.a w.1 * L.pr k * (F.a w.1)⁻¹) := by
    intro M hM k hk
    obtain ⟨g, rfl⟩ := F.surj k
    have h1 : S.L.CongOne M (F.tr.j g) := by rw [← F.j_tr]; exact hk.1
    have h2 := ((hI E A n p S F.tr g).2 M hM).1 h1 w.1 w.2.2
    have h3 : UpperTheory.Gal.CertificateRingHomMap.comp w.1 g = GeneralLinearGroup.map (pLoc E w.1) (mat g) := rfl
    rw [hL.1 g, F.a_tr, h3]
    simpa [map_mul, map_inv] using h2
  have hopen : ∀ M : ℕ, 0 < M → (S.L.KN M : Set S.G.GAf) ∈ 𝓝 (1 : S.G.GAf) := by
    intro M hM
    obtain ⟨K, hK⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p S.D S.G S.L M hM
    have ho : IsOpen (S.L.KN M : Set S.G.GAf) := hK ▸ K.K.isOpen
    exact ho.mem_nhds (one_mem _)

  have hent : ∀ i j, Filter.Tendsto (fun k => ((F.a w.1 * L.pr k * (F.a w.1)⁻¹).val - 1) i j) (𝓝 (1 : S.G.GAf)) (𝓝 0) := by
    intro i j U hU
    obtain ⟨M, hM, hsm⟩ := small_of_nhds w.1 hU
    exact Filter.mem_map.2 (Filter.mem_of_superset (hopen M hM) fun k hk => hsm _ (key M hM k hk i j))
  have hmat : Filter.Tendsto (fun k => (F.a w.1 * L.pr k * (F.a w.1)⁻¹).val) (𝓝 (1 : S.G.GAf))
      (𝓝 (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E))) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have := (hent i j).add_const ((1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j)
    simpa [Matrix.sub_apply] using this
  have hval : ContinuousAt (fun k => (L.pr k).val) (1 : S.G.GAf) := by
    have h := ((tendsto_const_nhds (x := ((F.a w.1)⁻¹).val)).mul hmat).mul (tendsto_const_nhds (x := (F.a w.1).val))
    have h1 : ((F.a w.1)⁻¹).val * 1 * (F.a w.1).val = (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) := by
      rw [mul_one]; exact (F.a w.1).inv_mul
    rw [h1] at h
    have h2 : ∀ k, ((F.a w.1)⁻¹).val * (F.a w.1 * L.pr k * (F.a w.1)⁻¹).val * (F.a w.1).val = (L.pr k).val := by
      intro k
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    simp only [h2] at h
    simpa [ContinuousAt] using h
  have hinv : ContinuousAt (fun k => (((L.pr k)⁻¹ : GL (Fin n) (w.1.adicCompletion E))).val) (1 : S.G.GAf) := by
    have h : ContinuousAt (fun k : S.G.GAf => k⁻¹) 1 := continuous_inv.continuousAt
    have h' : ContinuousAt (fun k => (L.pr k).val) ((1 : S.G.GAf)⁻¹) := by simpa using hval
    have h2 : (fun k => (((L.pr k)⁻¹ : GL (Fin n) (w.1.adicCompletion E))).val) =
        (fun k => (L.pr k).val) ∘ (fun k : S.G.GAf => k⁻¹) := by
      funext k
      simp only [Function.comp, map_inv]
    rw [h2]
    exact ContinuousAt.comp h' h
  refine continuous_of_continuousAt_one L.pr ?_
  rw [Units.isEmbedding_embedProduct.isInducing.continuousAt_iff]
  exact hval.prodMk (MulOpposite.continuous_op.continuousAt.comp hinv)
end

section
set_option autoImplicit false

namespace UpperTheory.Gal.Spc

open UpperTheory.Gal.W2.Seed GlobalTheory.LKTrip GlobalTheory.UPel.HT

private def splitEquiv {X M : Type} [Group X] [Group M] (L : Loc X M) : X ≃* M × L.pr.ker where
  toFun g := (L.pr g, ⟨(L.loc (L.pr g))⁻¹ * g, by simp [MonoidHom.mem_ker, L.pr_loc]⟩)
  invFun x := L.loc x.1 * (x.2 : X)
  left_inv g := by simp
  right_inv x := by
    obtain ⟨m, h, hh⟩ := x
    have hh' : L.pr h = 1 := hh
    ext <;> simp [L.pr_loc, hh']
  map_mul' g h := by
    have hc : L.pr ((L.loc (L.pr g))⁻¹ * g) = 1 := by simp [L.pr_loc]
    have key := L.comm (L.pr h)⁻¹ _ hc
    rw [map_inv] at key
    refine Prod.ext (map_mul _ _ _) (Subtype.ext ?_)
    show (L.loc (L.pr (g * h)))⁻¹ * (g * h) = (L.loc (L.pr g))⁻¹ * g * ((L.loc (L.pr h))⁻¹ * h)
    rw [← mul_assoc ((L.loc (L.pr g))⁻¹ * g), ← key]
    simp [mul_assoc]

private theorem t2Space_hTGroup_gAf {p : ℕ} [Fact p.Prime] (G : HTGroup p) : T2Space G.GAf := by
  haveI := GlobalTheory.GfTop.t2Space_afP p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_locallyCompactSpace p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_totallyDisconnectedSpace p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_secondCountableTopology p
  exact (GlobalTheory.GfTop.upts_props G.star (AfP p)).2.1

theorem splitC : SplitC := by
  intro p _ G Lv k _ _ _ _ P L hcont hat Kw hKo hKc hF
  haveI := t2Space_hTGroup_gAf G
  have hker : IsClosed (L.pr.ker : Set G.GAf) := isClosed_singleton.preimage hcont
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨splitEquiv L, fun g => (hat g).symm, Kw, (Lv.K : Subgroup G.GAf).subgroupOf L.pr.ker,
      hKo, hKc, ?_, ?_, ?_⟩, fun g h => rfl⟩
  · exact Lv.K.isOpen.preimage continuous_subtype_val
  · exact hker.isClosedEmbedding_subtypeVal.isCompact_preimage Lv.compact
  · ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨hF.2 g hg, ?_⟩
      show (L.loc (L.pr g))⁻¹ * g ∈ (Lv.K : Subgroup G.GAf)
      exact mul_mem (inv_mem (hF.1 _ (hF.2 g hg))) hg
    · rintro ⟨hm, hh⟩
      exact ⟨L.loc x.1 * (x.2 : G.GAf), mul_mem (hF.1 _ hm) hh,
        (splitEquiv L).apply_symm_apply x⟩

end UpperTheory.Gal.Spc
end

section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep
open GlobalTheory.SplitPts (conjE)

namespace UpperTheory.Gal.Spc

section LinAlg

variable {K : Type*} [Field K] {m : ℕ}

private theorem sep_of_mul_closed [IsAlgClosed K] {M N : Matrix (Fin m) (Fin m) K} {a : K} (ha : a ≠ 0)
    (h : N * M = a • (1 : Matrix (Fin m) (Fin m) K)) (hM : M.charpoly.Separable) : N.charpoly.Separable := by
  classical
  have hdet : M.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    by_cases hm : m = 0
    · subst hm
      simp [Matrix.det_isEmpty] at h0
    · exact pow_ne_zero _ ha this.symm
  have hroot : ∀ x ∈ M.charpoly.roots, x ≠ 0 ∧ a / x ∈ N.charpoly.roots := by
    intro x hx
    have hx0 : M.charpoly.eval x = 0 := (Polynomial.mem_roots'.1 hx).2
    rw [Matrix.eval_charpoly] at hx0
    have hne : x ≠ 0 := by
      rintro rfl
      apply hdet
      simpa [Matrix.det_neg] using hx0
    refine ⟨hne, Polynomial.mem_roots'.2 ⟨(Matrix.charpoly_monic N).ne_zero, ?_⟩⟩
    show N.charpoly.eval (a / x) = 0
    rw [Matrix.eval_charpoly]
    have e : Matrix.scalar (Fin m) (a / x) - N = (-x⁻¹) • (N * (Matrix.scalar (Fin m) x - M)) := by
      rw [Matrix.mul_sub, h, Matrix.scalar_apply, Matrix.scalar_apply]
      ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply] <;> field_simp <;> ring
    rw [e, Matrix.det_smul, Matrix.det_mul, hx0, mul_zero, mul_zero]
  have hnd : M.charpoly.roots.Nodup := Polynomial.nodup_roots hM
  have hcM : M.charpoly.roots.card = m := by
    have := Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits M.charpoly)
    rw [this, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcN : N.charpoly.roots.card = m := by
    have := Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits N.charpoly)
    rw [this, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hinj : Set.InjOn (fun x : K => a / x) (M.charpoly.roots.toFinset : Set K) := by
    intro x hx y hy hxy
    have hx0 := (hroot x (by simpa using hx)).1
    have hy0 := (hroot y (by simpa using hy)).1
    have hxy' : a * x⁻¹ = a * y⁻¹ := by simpa only [div_eq_mul_inv] using hxy
    exact inv_injective (mul_left_cancel₀ ha hxy')
  have hsub : M.charpoly.roots.toFinset.image (fun x : K => a / x) ⊆ N.charpoly.roots.toFinset := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact Multiset.mem_toFinset.2 (hroot x (Multiset.mem_toFinset.1 hx)).2
  have hle : m ≤ N.charpoly.roots.toFinset.card := by
    have h1 := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injOn hinj, Multiset.toFinset_card_of_nodup hnd, hcM] at h1
  have hndN : N.charpoly.roots.Nodup := by
    rw [← Multiset.dedup_card_eq_card_iff_nodup]
    refine le_antisymm (Multiset.card_le_card (Multiset.dedup_le _)) ?_
    rw [hcN]
    exact hle
  exact (Polynomial.nodup_roots_iff_of_splits (Matrix.charpoly_monic N).ne_zero (IsAlgClosed.splits _)).1 hndN

private theorem sep_of_mul {M N : Matrix (Fin m) (Fin m) K} {a : K} (ha : a ≠ 0)
    (h : N * M = a • (1 : Matrix (Fin m) (Fin m) K)) (hM : M.charpoly.Separable) : N.charpoly.Separable := by
  have h' : N.map (algebraMap K (AlgebraicClosure K)) * M.map (algebraMap K (AlgebraicClosure K)) =
      algebraMap K (AlgebraicClosure K) a • (1 : Matrix (Fin m) (Fin m) (AlgebraicClosure K)) := by
    rw [← Matrix.map_mul, h]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have h2 := sep_of_mul_closed (K := AlgebraicClosure K) (a := algebraMap K (AlgebraicClosure K) a)
    (by simpa using ha) h' (by rw [Matrix.charpoly_map]; exact hM.map)
  rw [Matrix.charpoly_map] at h2
  exact (Polynomial.separable_map _).1 h2

end LinAlg

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.sepConj :
    UpperTheory.Gal.Spc.SepConj := by
  intro E _ _ _ n g w hw
  have h0 : (g.1.1.val.map (conjFin (conjE E)))ᵀ * g.1.1.val =
      GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (g.1.2 : UpperTheory.Gal.CertificateRingHomMap.AfQ) • (1 : Matrix (Fin n) (Fin n) _) := g.2
  have h1 := congrArg (RingHom.mapMatrix (pLoc E w)) h0
  rw [map_mul] at h1
  have ha : pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (g.1.2 : UpperTheory.Gal.CertificateRingHomMap.AfQ)) ≠ 0 :=
    ((g.1.2.isUnit.map (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E)).map (pLoc E w)).ne_zero
  have h2 : (((UpperTheory.Gal.CertificateRingHomMap.comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (conjE E) w))ᵀ) * (UpperTheory.Gal.CertificateRingHomMap.comp w g).val =
      pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (g.1.2 : UpperTheory.Gal.CertificateRingHomMap.AfQ)) • (1 : Matrix (Fin n) (Fin n) _) := by
    refine Eq.trans ?_ (h1.trans ?_)
    · congr 1
    · ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have h3 := UpperTheory.Gal.Spc.sep_of_mul ha h2 hw
  rw [Matrix.charpoly_transpose, Matrix.charpoly_map] at h3
  exact (Polynomial.separable_map _).1 h3
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open Formalism.UG (Hecke conv)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private theorem conv_add_r {X : Type} [Group X] {K : Subgroup X} (hK : Formalism.UG.IsCommensurated K) {e : X → ℂ}
    (he : e ∈ Hecke ℂ K) (f f' : X → ℂ) : conv K e (f + f') = conv K e f + conv K e f' := by
  have hs := Formalism.UG.P.finite_support_cosets hK ((Formalism.UG.P.mem_hecke_iff ℂ K e).1 he).2
  funext x
  have hsub : ∀ (φ : X → ℂ), (Function.support fun q : X ⧸ K => e q.out * φ (q.out⁻¹ * x)).Finite := fun φ =>
    hs.subset fun q hq => left_ne_zero_of_mul hq
  simp only [conv, Pi.add_apply, mul_add]
  exact finsum_add_distrib (hsub f) (hsub f')

private theorem conv_smul_r {X : Type} [Group X] (K : Subgroup X) (e : X → ℂ) (c : ℂ) (f : X → ℂ) :
    conv K e (c • f) = c • conv K e f := by
  funext x
  simp only [conv, Pi.smul_apply, smul_eq_mul]
  refine (finsum_congr fun q => mul_left_comm _ _ _).trans ?_
  simpa only [smul_eq_mul] using (smul_finsum c fun q : X ⧸ K => e q.out * f (q.out⁻¹ * x)).symm

private theorem span_fix {X : Type} [Group X] {K : Subgroup X} (hK : Formalism.UG.IsCommensurated K) {e : X → ℂ}
    (he : e ∈ Hecke ℂ K) (s : Set (X → ℂ)) (hs : ∀ f ∈ s, conv K e f = f) :
    ∀ f ∈ Submodule.span ℂ s, conv K e f = f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact hs f hf
  | zero => funext x; simp [conv]
  | add f f' _ _ h h' => rw [conv_add_r hK he, h, h']
  | smul c f _ h => rw [conv_smul_r, h]

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.specData :
    UpperTheory.Gal.Int.Geo.Pl.WtOf → UpperTheory.Gal.Spc.SpecData := by
  intro hWt E _ _ _ A n p _ S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy hEx J g θ hseen
  obtain ⟨⟨Lv, hLv⟩, ⟨Kw, hKwo, hKwc, hKwF⟩, hJo, hJc, hker, hcusp⟩ :=
    UpperTheory.Gal.Spc.tyTop E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  obtain ⟨u, hu, u', hu', heu, hue, hinv, hcomm, hX⟩ :=
    UpperTheory.Gal.Spc.auxFn E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  have hmem := UpperTheory.Gal.Spc.memFn E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  have hmc := UpperTheory.Gal.Spc.memComm E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  obtain ⟨thQ, hthQ, hEig⟩ :=
    UpperTheory.Gal.Spc.eigEx E A n p S F x U w₀ Up V hodd hSc hGen hOff hq r W hAux N hrN hStab L hw Ty hTy
  have hLK : Lv.K.toSubgroup = Ty.K₀ := hLv.trans hTy.K₀_eq.symm
  have hid : TfIdem := pTfIdem pTfAdm (pTfCen pAvgK pTfAdm)
  have hAdm1 : Ty.admitted (Ty.tf 1) := (pTfAdm _ _ Ty 1 (map_one _)).1
  have he : Ty.tf 1 ∈ Hecke ℂ Ty.K₀ := hAdm1.1
  have hψ : ∀ j, (g j).fn ∈ Hecke ℂ Ty.K₀ := fun j => (hmem (g j) (θ j) (hseen j)).1
  have hring := pConvRing _ Ty.K₀ Ty.cms
  have hoff : ∀ f ∈ Off2 W L Ty, conv Ty.K₀ (Ty.tf 1) f = f := by
    refine UpperTheory.Gal.Spc.span_fix Ty.cms he _ ?_
    rintro f ⟨h, hh, -, rfl⟩
    exact (hid _ _ Ty h hh).2.2
  have hrel : Rel (conv Ty.K₀) (fun j => (g j).fn) (Ty.tf 1) u u' :=
    { idem := (hid _ _ Ty 1 (map_one _)).2.1
      eT := fun j => hoff _ (hmc (g j) (g j) (θ j) (θ j) (hseen j) (hseen j)).1
      eu := by rw [hue, heu]
      TT := fun j j' => (hmc (g j) (g j') (θ j) (θ j') (hseen j) (hseen j')).2
      uT := fun j => by
        show conv Ty.K₀ u (conv Ty.K₀ (g j).fn (Ty.tf 1)) = conv Ty.K₀ (g j).fn (conv Ty.K₀ u (Ty.tf 1))
        rw [hcomm _ (hmc (g j) (g j) (θ j) (θ j) (hseen j) (hseen j)).1, hue,
          (hring _ (hψ j) _ he).2 u hu, heu]
      inv := by rw [hue]; exact hinv }
  obtain ⟨w₁, hw₁⟩ := hAux.nonempty
  obtain ⟨P₁, hP₁⟩ := hEx.1 w₁.1 w₁.2.2
  obtain ⟨P, hP⟩ := hEx.1 w₀ hw.2
  have hfac₀ : ∀ y, Ty.L.pr (F.j y) = comp w₀ y := by
    intro y
    rw [hTy.L_eq]
    exact (hTy.fac ⟨w₀, hw⟩).1 y
  have hcont : Continuous Ty.L.pr := by
    rw [hTy.L_eq]
    exact UpperTheory.Gal.Spc.facCont E A n p S F ⟨w₀, hw⟩ _ (hTy.fac ⟨w₀, hw⟩)
  have hat : ∀ y, P.at y = (Ty.L.pr y : Matrix (Fin n) (Fin n) (w₀.adicCompletion E)) := by
    intro y
    obtain ⟨y', rfl⟩ := F.surj y
    rw [hP, hfac₀]
  letI : MeasurableSpace (w₀.adicCompletion E) := borel _
  haveI : BorelSpace (w₀.adicCompletion E) := ⟨rfl⟩
  obtain ⟨τ, hτ, hτ2, Sp, hSp⟩ := UpperTheory.Gal.Spc.splitC p S.G Lv (w₀.adicCompletion E) P Ty.L hcont hat Kw hKwo hKwc
    (by rw [hLK]; exact hKwF)
  have hCe : Sp.Cusp (Ty.tf 1) := by
    intro h
    have h0 := UpperTheory.Gal.Spc.cuspIrr_kFinite_rep_eq_centralCuspForm S.G.GAf (w₀.adicCompletion E) n Ty hJo hJc hker hcusp (Ty.tf 1) hAdm1 h.1 h.2
    have h1 : (fun y => Ty.tf 1 (Sp.e.symm (y, h))) = fun y => Ty.tf 1 (Ty.L.loc y * h.1) :=
      funext fun y => by rw [hSp]; rfl
    rw [h1]
    exact h0
  have hA : ∀ m : ℕ, 1 ≤ m → ∃ A' : Set S.G.GAf,
      (∀ y ∈ A', (P₁.at y).charpoly.Separable ∧ GlobalTheory.LKCx.RegAf S.G y) ∧
      (∀ j a, (g j).fn a ≠ 0 → ∀ y ∈ A', a * y ∈ A') ∧
      ∀ y, powFn Lv.K.toSubgroup u (Ty.tf 1) m y ≠ 0 → y ∈ A' := by
    intro m hm
    obtain ⟨X, hX1, hX2⟩ := hX m hm
    refine ⟨{y | ∀ w ∈ W, (L w).pr y ∈ X w}, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨y', rfl⟩ := F.surj y
      have hsep : ∀ w ∈ W, (comp w.1 y').val.charpoly.Separable := fun w hw' => by
        have h := (hX1 w hw' _ (hy w hw')).1
        rwa [(hTy.fac w).1] at h
      refine ⟨?_, hEx.2 r hAux.prime hAux.ne y' ?_⟩
      · rw [hP₁]
        exact hsep w₁ hw₁
      · intro v hv
        obtain ⟨w, hwW, rfl | rfl⟩ := hAux.half.all v hv
        · exact hsep w hwW
        · exact UpperTheory.Gal.Spc.sepConj E n y' w.1 (hsep w hwW)
    · intro j a ha y hy w hw'
      rw [map_mul]
      exact (hX1 w hw' _ (hy w hw')).2 _ ((hmem (g j) (θ j) (hseen j)).2.1 a ha w hw')
    · intro y hy
      rw [hLK] at hy
      exact (hX2 y hy).2
  have hso : UpperTheory.Gal.Spc.SpecOfF := UpperTheory.Gal.Spc.specOfF
  unfold UpperTheory.Gal.Spc.SpecOfF UpperTheory.Gal.Spc.ForPlaces at hso
  have hso' := @hso p _ S.G (pSetupBasic E A n p S).1 Lv (w₀.adicCompletion E) _ _ _ _ _ _ _ P Ty.L.pr.ker _ τ hτ hτ2 Sp
    (w₁.1.adicCompletion E) _ _ P₁ (UpperTheory.Gal.G1.FinCls_holds E A n p S)
  have key := hso'
    S.D S.L V.lam (Module.Dual ℂ V.W.Sp) ((UpperTheory.Gal.CertificateRingHomMap.xi V.W V.jz).comp thQ) (hWt E A n p S x U w₀ Up V thQ hthQ)
    J (fun j => (g j).fn) θ (Ty.tf 1) u u' (by rw [hLK]; exact hψ) (by rw [hLK]; exact he) (by rw [hLK]; exact hu)
    (by rw [hLK]; exact hu') (by rw [hLK]; exact hrel) hCe hA
    (by rw [hLK]; exact hEig J g θ hseen)
  obtain ⟨m, hm, hspec⟩ := key
  have hW := (UpperTheory.Gal.Spc.words p S.G Lv J (fun j => (g j).fn) (Ty.tf 1) u u' (by rw [hLK]; exact hψ)
    (by rw [hLK]; exact he) (by rw [hLK]; exact hu) (by rw [hLK]; exact hrel) m).1
  obtain ⟨X, -, hX2⟩ := hX m hm
  rw [hLv] at hspec hW
  refine ⟨_, ⟨hW, fun y hy => ?_⟩, hspec⟩
  rw [← hTy.K₀_eq] at hy
  exact (hX2 y hy).1
end
end
