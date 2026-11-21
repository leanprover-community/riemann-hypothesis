import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PFrameEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PDatEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.NsmulIntegIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PLevBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PThLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.POfUBij
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFacEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLevSec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongGrpEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSiteFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCuspTh
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDenom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSeenShape
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.FinsumInvT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPhiTy
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTyFact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAtApart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSumDoset
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemAct
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAct
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAdm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfIdem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDosetCosets
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDosetIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulCen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulR
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIdx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspaces
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PHasEigOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PStdForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PExtP

section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pCenFacts :
    Sides → CenFacts := by
  intro hS E _ _ _ A n _ x hx q hq hsp w hw z hz
  obtain ⟨-, -, -, h4, -⟩ := hS E A x hx q hq hsp w hw
  have hscal : ∀ (u : Plc E) (a : GL (Fin n) (u.adicCompletion E)), comp u z * a = a * comp u z := by
    intro u a
    by_cases h : UpperTheory.Gal.CertificateRingHomMap.SameK x (UpperTheory.Gal.CertificateRingHomMap.cj u) w
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, (hz u).1 h, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    · rw [(hz u).2 h, one_mul, mul_one]
  refine ⟨fun g => UpperTheory.Gal.CertificateRingHomMap.guf_ext ?_ fun u => ?_, fun u hu => ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_mul, map_mul, hscal]
  · refine (hz u).2 fun h => hu ?_
    have h' := h4 _ h
    have e : (UpperTheory.Gal.CertificateRingHomMap.cj u).asIdeal = _ :=
      (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)
    rw [e, Ideal.mem_comap, map_natCast] at h'
    exact h'
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pStabKer :
    FacEq → KNFact → CongGrpEx → StabKer := by
  intro _ hKN hCG E _ _ _ A n p _ S F x U w₀ Up V _ _ _ _ _ r W haux N _ _ L hw Ty hTy k hk hkr
  obtain ⟨k', hk', hlev, hJ, hχ⟩ := hk
  have hK : k ∈ Ty.K := by
    refine (hTy.K_iff k).2 ⟨⟨k', hk', hlev⟩, fun w hwW => ?_⟩
    have hr : (r : 𝓞 E) ∈ w.1.asIdeal := haux.half.above w hwW
    obtain ⟨K, hK, -, -, -, -, hIw, -⟩ := hCG E n r haux.prime.pos w.1
    have hf := hKN E A n p S F w (L w) (hTy.fac w) r haux.prime haux.good hr r haux.prime.pos K hK
    exact hIw hr (hf.2 k hkr)
  refine (Ty.mem_kerK k).2 ⟨hK, ?_⟩
  have hpr : Ty.L.pr k = comp w₀ k' := by
    rw [hTy.L_eq, ← hk']
    exact (hTy.fac ⟨w₀, hw⟩).1 k'
  refine (hTy.ψ_eq _ ⟨comp w₀ (F.th k'), hJ⟩ ?_).trans hχ
  simp only [hpr, th_eq F, CertificateRingHomMap.comp_th, CertificateRingHomMap.invT_val]
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pSeenActs :
    MemSum → MemAct → MemDeck → SeenShape → LevBasic → KNIdx → SeenActs := by
  intro hS hA hD hSh hLB _ E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hTy g θ hseen
  have hK : g.K ≤ Ty.kerK := (hSh E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hTy g θ hseen).1
  have hK₀ : Ty.K₀ = S.L.KN N.1 := hTy.K₀_eq
  have hker : Ty.kerK ≤ Ty.K := fun k hk => ((Ty.mem_kerK k).1 hk).1
  have hnorm : ∀ M : ℕ, ∀ k ∈ S.L.KN 1, ∀ u ∈ S.L.KN M, k * u * k⁻¹ ∈ S.L.KN M := fun M k hk u hu =>
    (hLB p S.D S.G S.L).2.2.2.2.1 _ _ ((hLB p S.D S.G S.L).2.2.1 M) k hk u hu
  have hnormK : ∀ k ∈ g.K, ∀ u ∈ S.L.KN g.M.1, k * u * k⁻¹ ∈ S.L.KN g.M.1 := fun k hk =>
    hnorm _ k (g.le_one hk)
  have hidx : (S.L.KN g.M.1).relIndex g.K ≠ 0 := fun h0 =>
    GlobalTheory.W2.relIndex_KN_ne_zero S.L one_pos (by have := g.M.2.1; omega) (Subgroup.relIndex_eq_zero_of_le_right g.le_one h0)
  refine ⟨fun a ha => ?_, fun hd hh => ?_, fun M' _ L' Kw t z hf hf' hap hz he => ?_⟩
  · obtain ⟨k, hk, hka⟩ := (hS _ g.K (S.L.KN g.M.1) (S.L.KN N.1) g.h g.le hidx hnormK g.adm).2.1 a ha
    exact ⟨k, hker (hK hk), Ty.le (hK₀ ▸ hka)⟩
  · obtain ⟨h1, h2, h3⟩ := hd
    have := hD _ _ Ty Ty.kerK (Ty.triv_of_le le_rfl) g.h hh (fun u hu => by
      rw [hK₀] at hu ⊢; exact hnorm _ _ h3 u hu)
    rw [hK₀] at this
    have e : g.fn = memFn (S.L.KN N.1) (S.L.KN N.1) (S.L.KN N.1) g.h := by
      have : g.fn = memFn g.K (S.L.KN g.M.1) (S.L.KN N.1) g.h := rfl
      rw [this, h1, h2]
    rw [e]; exact this
  · have := hA _ _ _ Ty L' Kw hf hap g.K (S.L.KN g.M.1) (Ty.triv_of_le hK) hf' (hK₀ ▸ g.le)
      (hK₀ ▸ KN_anti g.dvd) hidx hnormK t z g.h hz he (hK₀ ▸ g.adm)
    rw [hK₀, ← he] at this
    exact this
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem conv_eq_hAct {X : Type} [Group X] (K : Subgroup X) (f f' : X → ℂ) (g : X) :
    conv K f f' g = hAct K f (fun x => f' (x⁻¹ * g)) 1 := by
  simp only [conv, hAct, one_mul, smul_eq_mul]

private theorem conv_tf {X M : Type} [Group X] [Group M] (hA : TfAdm) (T : TyLev X M) (ψ : X → ℂ) (c : ℂ) (h h' : X)
    (hψ : T.Acts ψ c h) (hh' : T.L.pr h' = 1) :
    conv T.K₀ ψ (T.tf h') = c • conv T.K₀ (T.tf h) (T.tf h') := by
  funext g
  have hΦ : T.IsTy (fun x => T.tf h' (x⁻¹ * g)) := by
    intro k hk x
    have hk' : k⁻¹ ∈ T.K := T.K.inv_mem hk
    simp only [_root_.mul_inv_rev, mul_assoc]
    rw [((hA X M T h' hh').2 k⁻¹ hk' (x⁻¹ * g)).1, smul_eq_mul]
    congr 1
    have e : ∀ (p1 : T.L.pr k⁻¹ ∈ T.J) (p2 : T.L.pr k ∈ T.J),
        (⟨T.L.pr k⁻¹, p1⟩ : T.J) = (⟨T.L.pr k, p2⟩ : T.J)⁻¹ := fun p1 p2 =>
      Subtype.ext (map_inv _ _)
    rw [e _ (T.fact.2 k hk)]
    simp
  have key := congrFun (hψ.2.2 ℂ _ hΦ) 1
  rw [Pi.smul_apply, conv_eq_hAct, conv_eq_hAct, key, Pi.smul_apply]

theorem UpperTheory.Gal.W2.Seed.pActsConv :
    TfAdm → TfIdem → ActsConv := by
  intro hA hI X M _ _ T ψ c h hψ
  constructor
  · rw [conv_tf hA T ψ c h 1 hψ (map_one _), (hI X M T h hψ.2.1).2.1]
  · intro c' h' hh'
    have hlin : ∀ f : X → ℂ, conv T.K₀ ψ (c' • f) = c' • conv T.K₀ ψ f := by
      intro f
      funext g
      rw [Pi.smul_apply]
      unfold conv
      rw [smul_finsum]
      congr 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hlin, conv_tf hA T ψ c h h' hψ hh', smul_smul, mul_comm c' c]
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pMemFn :
    SeenShape → SeenActs → ActsConv → TyFact → MemFn := by
  intro hSh hAc hAC hTF E _ _ _ A n p _ S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨-, hcase⟩ := hSh E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨hsupp, hdeck, hgen⟩ := hAc E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨tf1, tf2, -⟩ := hTF E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy
  rcases hcase with ⟨hD, hh, hθ⟩ | ⟨w, t, z, i, B, hFree, hAp, -, -, -, -, -, hinv, hCen, hWpr, hFg, -⟩
  · have hA := hdeck hD hh
    have hhK : g.h ∈ Ty.K := ((Ty.mem_kerK _).1 hh).1
    refine ⟨hA.1, ?_, Or.inl ⟨hD, hθ, ?_⟩⟩
    · intro a ha u hu
      obtain ⟨k, hk, hka⟩ := hsupp a ha
      have haK : a ∈ Ty.K := by
        have e : a = (g.h * k)⁻¹ * (g.h * k * a) := by group
        rw [e]
        exact Ty.K.mul_mem (Ty.K.inv_mem (Ty.K.mul_mem hhK hk)) hka
      exact (tf1 u hu).1.2 a haK
    · have e := (hAC _ _ Ty _ _ _ hA).1
      rwa [one_smul] at e
  · obtain ⟨hfac, hap⟩ := tf2 w hFree.2.1 hFree.2.2.1 hAp
    have hA := hgen _ (L w) _ t⁻¹ (F.j (z ^ i)⁻¹) hfac hFg hap hCen hinv
    have hpr : Ty.L.pr g.h = 1 := by
      have e := hA.2.1
      rwa [map_inv, inv_eq_one] at e
    refine ⟨hA.1, ?_, Or.inr ⟨hpr, hWpr, (hAC _ _ Ty _ _ _ hA).1⟩⟩
    intro a ha u hu
    obtain ⟨k, hk, hka⟩ := hsupp a ha
    have f := (tf1 u hu).1.2
    have e : (L u).pr (g.h * k * a) = (L u).pr k * (L u).pr a := by
      rw [map_mul, map_mul, hWpr u hu, one_mul]
    have h6 := f _ hka
    rw [e] at h6
    exact (Subgroup.mul_mem_cancel_left _ (f k hk)).1 h6
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pPhiEx :
    PhiTy → SeenShape → SeenActs → TyFact → TfAct → TfCen → TEig → AtApart → FacEq → JEq → UpperTheory.Gal.W2.Seed.LocComm → PhiEx := by
  intro hTy hShape hActs hFact hTfAct hTfCen hTEig hAt hFac hJ hc E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok
  obtain ⟨h0, h1, h2, -⟩ := hTy E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok
  refine ⟨fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h)), h0, h1, ?_, ?_⟩
  · intro g hg
    have := h2 g hg
    rw [th_eq F]
    exact this
  · intro g θ hs
    obtain ⟨-, hcase⟩ := hShape E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok g θ hs
    have hA := hActs E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok g θ hs
    rcases hcase with ⟨hd, hk, rfl⟩ | ⟨w, t, z, i, B, hfree, hap, hi, hT, hz, hB, hzp, hh, hcen, -, hLf, rfl⟩
    · have h3 := (hA.2.1 hd hk).2.2 _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1
      rw [h3]
      funext a
      have h4 := hTfCen _ _ Ty 1 ⟨fun _ => by simp, map_one _⟩ _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1 a
      simp only [Pi.smul_apply, one_smul]
      rw [h4, mul_one]
    · obtain ⟨hLK, hLA⟩ := (hFact E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok).2.1 w
        hfree.2.1 hfree.2.2.1 hap
      have hAc := hA.2.2 _ (L w) _ t⁻¹ (F.j (z ^ i)⁻¹) hLK hLf hLA hcen hh
      have h3 := hAc.2.2 _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1
      have hsz : F.tr.sec (F.j (z ^ i)⁻¹) = (z ^ i)⁻¹ := by
        apply (hJ E A n p S F.tr.toAdT F.tr.μ F.tr.mu F.tr.a F.tr.j F.tr.j_mx).1
        intro u
        by_cases hu : (p : 𝓞 E) ∈ u.asIdeal
        · rw [F.tr.sec_p _ u hu]
          simp [hzp u hu]
        · exact (F.tr.j_eq _ _).1 (by rw [F.tr.j_sec, F.j_tr]) u hu
      have hsl : ∀ y, F.tr.sec ((L w).loc y) = CertificateRingHomMap.loc w.2.1 y := by
        intro y
        have hL : L w = fac F.tr hc w := (hFac E A n p S F hc w).2 _ (hok.fac w)
        rw [hL]
        exact (hAt E A n p S F.tr hc w.1 w.2.1 w.2.2).1 y
      rw [h3, hh]
      funext a
      have h4 := hTfAct _ _ _ Ty (L w) _ hLK hLA t⁻¹ (F.j (z ^ i)⁻¹) hcen _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1 a
      have h5 := hTEig E n hodd.pos x U w₀ Up V w.1 w.2.1 hfree i hi t hT z hz B hB (F.tr.sec a)
      simp only [Pi.smul_apply]
      rw [h4, mul_smul, ← h5]
      congr 1
      refine finsum_congr fun y => ?_
      simp only [map_mul, hsz, hsl]
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pMemDeck :
    MemSum → TfCen → MemDeck := by
  intro hSum hCen X M _ _ T K hT k hk hnorm
  have hconj : ∀ a ∈ T.K₀, ∀ u ∈ T.K₀, a * u * a⁻¹ ∈ T.K₀ := fun a ha u hu =>
    T.K₀.mul_mem (T.K₀.mul_mem ha hu) (T.K₀.inv_mem ha)
  have hmem := hSum X T.K₀ T.K₀ T.K₀ k le_rfl (by simp) hconj (fun a ha u hu => by
    have h1 := hnorm (a * u * a⁻¹) (hconj a ha u hu)
    simpa [mul_assoc, _root_.mul_inv_rev] using h1)
  refine ⟨hmem.1, map_one _, ?_⟩
  intro V _ _ Φ hΦ
  funext g
  have hc : T.Cen 1 := ⟨fun g => by simp, map_one _⟩
  rw [one_smul, hCen X M T 1 hc V Φ hΦ g, mul_one]
  have hinv0 : ∀ k' ∈ T.K₀, ∀ g, Φ (g * k') = Φ g := fun k' hk' g => by
    rw [hΦ k' (T.le hk') g, T.ker k' hk' _]
    simp
  rw [hmem.2.2 V Φ hinv0 g]
  have hall : ∀ a b : ↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀, a = b := by
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact SetLike.coe_mem _
  letI : Unique (↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀) :=
    ⟨⟨QuotientGroup.mk (1 : ↥T.K₀)⟩, fun a => hall a _⟩
  rw [finsum_unique]
  have hx : (↑(Quotient.out (default : ↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀)) : X) ∈ T.K₀ :=
    SetLike.coe_mem _
  rw [_root_.mul_inv_rev, ← mul_assoc, hΦ k⁻¹ (hT.1 (K.inv_mem hk)) _,
    hT.2 k⁻¹ (K.inv_mem hk) _]
  simp only [Units.val_one, one_smul]
  exact hinv0 _ (T.K₀.inv_mem hx) g
end

section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pTfCen :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → TfAdm → TfCen := by
  intro hsum hadm X M _ _ T z hz V _ _ Φ hΦ g
  have hidx : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr T.idx
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : X → V, ∀ x, Ψ x = T.tf z x • Φ (g * x) := ⟨_, fun _ => rfl⟩
  have hinv : ∀ k ∈ T.K, ∀ x, Ψ (x * k) = Ψ x := by
    intro k hk x
    have h1 := ((hadm X M T z hz.2).2 k hk x).2
    have h2 := hΦ k hk (g * x)
    rw [hΨ, hΨ, h1, ← mul_assoc, h2, smul_smul, mul_right_comm, Units.inv_mul, one_mul]
  have hsingle : ∑ᶠ y : X ⧸ T.K, Ψ y.out = Ψ z := by
    rw [finsum_eq_single _ (QuotientGroup.mk z : X ⧸ T.K)]
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul T.K z
      rw [hk]
      exact hinv k k.2 z
    · intro y hy
      have h0 : dosetInd ℂ T.K z y.out = 0 := by
        apply Set.indicator_of_notMem
        intro hm
        obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.mp hm
        have e' : y.out = z * (a * b) := by
          rw [e, ← hz.1 a, mul_assoc]
        have h2 : ((y.out : X) : X ⧸ T.K) = (z : X ⧸ T.K) := by
          rw [e']
          exact QuotientGroup.mk_mul_of_mem z (T.K.mul_mem ha hb)
        exact hy ((QuotientGroup.out_eq' y).symm.trans h2)
      rw [hΨ, TyLev.tf, h0, mul_zero, zero_smul]
  have hty : tyFn T.J T.ψ 1 = 1 := by
    unfold tyFn
    rw [dif_pos T.J.one_mem]
    have h1 : (⟨1, T.J.one_mem⟩ : T.J) = 1 := rfl
    rw [h1, map_one]
    simp
  have hdz : dosetInd ℂ T.K z z = 1 := by
    unfold dosetInd
    rw [Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.mpr ⟨1, T.K.one_mem, 1, T.K.one_mem, by simp⟩)]
    rfl
  have hzz : T.tf z z = ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ := by
    rw [TyLev.tf, hz.2, hty, hdz, mul_one, mul_one]
  have hs := hsum X V T.K T.K₀ T.le T.idx Ψ hinv
  unfold hAct
  simp only [hΨ] at hs hsingle
  rw [hs, hsingle, hzz, smul_smul, mul_inv_cancel₀ hidx, one_smul]
end

section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pAvgK :
    ∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out := by
  intro X V _ _ _ K K₀ hle hidx Ψ hΨ
  haveI : Finite (K ⧸ K₀.subgroupOf K) := Nat.finite_of_card_ne_zero hidx
  haveI : Fintype (K ⧸ K₀.subgroupOf K) := Fintype.ofFinite _
  let e := Subgroup.quotientEquivProdOfLE hle
  let F : X ⧸ K → V := fun y => Ψ y.out
  have he : ∀ x : X ⧸ K₀, Ψ x.out = F (e x).1 := by
    intro x
    have h1 : (e x).1 = ((x.out : X) : X ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' x]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x.out
    simp only [F, h1, hk, hΨ k k.2]
  have hcard : Fintype.card (K ⧸ K₀.subgroupOf K) = K₀.relIndex K := by
    rw [Fintype.card_eq_nat_card]
    rfl
  have h2 : ∑ᶠ x : X ⧸ K₀, Ψ x.out = ∑ᶠ p : (X ⧸ K) × (K ⧸ K₀.subgroupOf K), F p.1 :=
    (finsum_congr he).trans (finsum_comp_equiv e (f := fun p => F p.1))
  rw [h2]
  by_cases hfin : (Function.support F).Finite
  · have hG : Function.HasFiniteSupport (fun p : (X ⧸ K) × (K ⧸ K₀.subgroupOf K) => F p.1) := by
      refine (hfin.prod (Set.finite_univ (α := K ⧸ K₀.subgroupOf K))).subset ?_
      intro p hp
      exact ⟨hp, trivial⟩
    rw [finsum_curry _ hG, smul_finsum]
    refine finsum_congr fun a => ?_
    show ∑ᶠ _ : K ⧸ K₀.subgroupOf K, Ψ a.out = _
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, hcard, Nat.cast_smul_eq_nsmul ℂ]
  · have h3 : ∑ᶠ y : X ⧸ K, Ψ y.out = 0 := finsum_of_infinite_support hfin
    rw [h3, smul_zero]
    apply finsum_of_infinite_support
    intro hG
    apply hfin
    refine (hG.image Prod.fst).subset ?_
    intro a ha
    exact ⟨(a, ((1 : K) : K ⧸ K₀.subgroupOf K)), ha, rfl⟩
end

section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem comm_conv (hRing : ConvRing) {X : Type} [Group X] {K : Subgroup X} (hK : IsCommensurated K)
    {f g h : X → ℂ} (hf : f ∈ Hecke ℂ K) (hg : g ∈ Hecke ℂ K) (hh : h ∈ Hecke ℂ K)
    (c₁ : conv K f h = conv K h f) (c₂ : conv K g h = conv K h g) :
    conv K (conv K f g) h = conv K h (conv K f g) := by
  calc conv K (conv K f g) h = conv K f (conv K g h) := (hRing X K hK f hf g hg).2 h hh
    _ = conv K f (conv K h g) := by rw [c₂]
    _ = conv K (conv K f h) g := ((hRing X K hK f hf h hh).2 g hg).symm
    _ = conv K (conv K h f) g := by rw [c₁]
    _ = conv K h (conv K f g) := (hRing X K hK h hh f hf).2 g hg

private theorem comm_cen (hAdm : TfAdm) (hCen : TfMulCen) (hRing : ConvRing) {X M : Type} [Group X] [Group M]
    (T : TyLev X M) {a b z z' : X} (ha : T.L.pr a = 1) (hb : T.L.pr b = 1) (hz : T.Cen z) (hz' : T.Cen z')
    (hab : conv T.K₀ (T.tf a) (T.tf b) = conv T.K₀ (T.tf b) (T.tf a)) :
    conv T.K₀ (T.tf (a * z)) (T.tf (b * z')) = conv T.K₀ (T.tf (b * z')) (T.tf (a * z)) := by
  have hK := T.cms
  have mA := (hAdm X M T a ha).1.1
  have mB := (hAdm X M T b hb).1.1
  have mZ := (hAdm X M T z hz.2).1.1
  have mZ' := (hAdm X M T z' hz'.2).1.1
  have cz := hCen X M T a z ha hz
  have cz' := hCen X M T b z' hb hz'
  have eBZ : conv T.K₀ (T.tf b) (T.tf z) = conv T.K₀ (T.tf z) (T.tf b) :=
    (hCen X M T b z hb hz).2.trans (hCen X M T b z hb hz).1.symm
  have eAZ' : conv T.K₀ (T.tf a) (T.tf z') = conv T.K₀ (T.tf z') (T.tf a) :=
    (hCen X M T a z' ha hz').2.trans (hCen X M T a z' ha hz').1.symm
  have eZZ' : conv T.K₀ (T.tf z) (T.tf z') = conv T.K₀ (T.tf z') (T.tf z) :=
    (hCen X M T z z' hz.2 hz').2.trans (hCen X M T z z' hz.2 hz').1.symm
  have mAZ := (hRing X T.K₀ hK _ mA _ mZ).1
  have h1 := comm_conv hRing hK mA mZ mB hab eBZ.symm
  have h2 := comm_conv hRing hK mA mZ mZ' eAZ' eZZ'
  have h3 := comm_conv hRing hK mB mZ' mAZ h1.symm h2.symm
  rw [← cz.2, ← cz'.2]
  exact h3.symm

theorem UpperTheory.Gal.W2.Seed.pTfComm : TfAdm → ConvRing → TfMulCen → TfMulL → TfMulR → TfLoc → TfComm := by
  intro hAdm hRing hCen hL hR hLoc X M M' M'' _ _ _ _ T L' Kw hF hAp z z' hz hz' t
  refine ⟨fun L'' t' h1 h2 => ?_, fun t' hc => ?_⟩
  · have ha : T.L.pr (L'.loc t) = 1 := hAp.1 t
    have hb : T.L.pr (L''.loc t') = 1 := h1.1 t'
    have hb' : L'.pr (L''.loc t') = 1 := h2.1 t'
    exact comm_cen hAdm hCen hRing T ha hb hz hz'
      ((hL X M M' T L' Kw hF hAp t _ hb hb').trans (hR X M M' T L' Kw hF hAp t _ hb hb').symm)
  · have ha : T.L.pr (L'.loc t) = 1 := hAp.1 t
    have hb : T.L.pr (L'.loc t') = 1 := hAp.1 t'
    refine comm_cen hAdm hCen hRing T ha hb hz hz' ?_
    funext g
    rw [hLoc X M M' T L' Kw hF hAp t t' g, hLoc X M M' T L' Kw hF hAp t' t g, hc]
end

section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pConvRing :
    ConvRing := by
  intro X _ K hK f hf f' hf'
  refine ⟨Formalism.UG.Final.HeckeConvMem X K ℂ hK f hf f' hf', fun f'' hf'' => ?_⟩
  exact Formalism.UG.Final.HeckeAssoc X K ℂ hK f hf f' hf' f'' hf''
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pSphComm :
    SphComm := by
  intro E _ _ n w t t'
  have hb : ∀ s : GL (Fin n) (w.adicCompletion E), IsBiInv (GlobalTheory.LFun.KGL w n) (dosetInd ℂ (GlobalTheory.LFun.KGL w n) s) := fun s => (Formalism.UG.Final.DosetIndMem _ _ ℂ s).1
  exact Formalism.UG.P.heckecomm_gelfand (GlobalTheory.LFun.KGL w n) Formalism.UG.P.heckecomm_tr Formalism.UG.P.heckecomm_tr_mul
    Formalism.UG.P.heckecomm_tr_tr (fun x hx => Formalism.UG.P.heckecomm_tr_mem _ x hx)
    (Formalism.UG.P.heckecomm_tr_dc Formalism.UG.P.cartan_decomposition_holds E w n) _ _ (hb t) (hb t')
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pPPart :
    JEq → PPart := by
  intro hJ E _ _ _ A n p _ S T g
  have hext := (hJ E A n p S T.toAdT T.μ T.mu T.a T.j T.j_mx).1
  have hoff : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w (T.sec (T.j g)) = comp w g :=
    fun w hw => (T.j_eq (T.sec (T.j g)) g).1 (T.j_sec _) w hw
  have hk1 : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w ((T.sec (T.j g))⁻¹ * g) = 1 := by
    intro w hw
    rw [map_mul, map_inv, hoff w hw, inv_mul_cancel]
  have hk2 : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w ((T.sec (T.j g))⁻¹ * g) = comp w g := by
    intro w hw
    rw [map_mul, map_inv, T.sec_p _ w hw, inv_one, one_mul]
  refine ⟨(T.sec (T.j g))⁻¹ * g, by group, hk1, hk2, fun h => hext _ _ fun w => ?_⟩
  rw [map_mul (comp w) (T.sec h), map_mul (comp w) _ (T.sec h)]
  by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
  · rw [T.sec_p h w hw, one_mul, mul_one]
  · rw [hk1 w hw, one_mul, mul_one]
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem apart_or {E : Type} [Field E] [NumberField E] [IsCMField E] (u w : Plc E) :
    GlobalTheory.Cong.Apart u w ∨ u = w ∨ u = UpperTheory.Gal.CertificateRingHomMap.cj w := by
  by_cases h : GlobalTheory.Cong.Apart u w
  · exact Or.inl h
  · exact Or.inr (GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc (not_not.1 h))

private theorem cj_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Plc E) :
    UpperTheory.Gal.CertificateRingHomMap.cj (UpperTheory.Gal.CertificateRingHomMap.cj w) = w := GlobalTheory.CompanionTheory.OnlyStab.conjSrc_invol w

theorem UpperTheory.Gal.W2.Seed.pLevFact :
    AtApart → IntConj → LevFact := by
  intro hA hI E _ _ _ A n p _ S T hc S₀ Kw w hw hp hcj
  have hsec : ∀ x, T.sec ((T.at hc w hw hp).loc x) = CertificateRingHomMap.loc hw x := (hA E A n p S T hc w hw hp).1
  have hn : 0 < n := S.facts.pos
  refine ⟨fun hwS => ⟨fun x hx => ?_, fun g hg => ?_⟩, fun hwS => ⟨fun x hx => ?_, fun g hg => ?_⟩⟩
  · show T.sec _ ∈ lev S₀ Kw
    rw [hsec, CertificateRingHomMap.mem_lev]
    refine ⟨by rw [CertificateRingHomMap.sim_loc]; exact one_mem _, fun u hu => ?_, fun u hu hcu => ?_⟩
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; rw [CertificateRingHomMap.comp_loc]; exact hx
      · subst h; exact absurd hu hcj
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; exact absurd hwS hu
      · subst h; exact absurd (by rwa [cj_cj]) hcu
  · exact (CertificateRingHomMap.mem_lev.1 hg).2.1 w hwS
  · show T.sec _ ∈ lev S₀ Kw
    rw [hsec, CertificateRingHomMap.mem_lev]
    refine ⟨by rw [CertificateRingHomMap.sim_loc]; exact one_mem _, fun u hu => ?_, fun u hu hcu => ?_⟩
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; exact absurd hu hwS
      · subst h; exact absurd hu hcj
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; rw [CertificateRingHomMap.comp_loc]; exact hx
      · subst h
        refine (hI E n (CertificateRingHomMap.loc hw x) w hn).1 ?_ ?_
        · rw [CertificateRingHomMap.sim_loc]; exact one_mem _
        · rw [CertificateRingHomMap.comp_loc]; exact hx
  · exact (CertificateRingHomMap.mem_lev.1 hg).2.2 w hwS hcj
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed.HeckeRelations


end UpperTheory.Gal.W2.Seed.HeckeRelations
end

section
namespace UpperTheory.Gal.W2.Seed

open UpperTheory.Gal.Int.Geo.Pl (dict_holds sides_holds levBasic_holds)
open UpperTheory.Gal.CertificateRingHomMap (pLocComm_of pThLoc_of)

theorem tfCen_holds : TfCen := pTfCen pAvgK pTfAdm
theorem tfAct_holds : TfAct := pTfAct pAvgK pDosetCosets pTfAdm
theorem tfIdem_holds : TfIdem := pTfIdem pTfAdm tfCen_holds
theorem tfMulL_holds : TfMulL := pTfMulL pTfAdm tfAct_holds pDosetIff
theorem tfMulR_holds : TfMulR := pTfMulR pAvgK pTfAdm pDosetIff
theorem tfLoc_holds : TfLoc := pTfLoc pTfAdm tfAct_holds pDosetIff
theorem knIff_holds : KNIff := pKNIff latCoord_holds
theorem atApart_holds : AtApart := pAtApart pJEq
theorem levFact_holds : LevFact := pLevFact atApart_holds pIntConj
theorem knIdx_holds : KNIdx := pKNIdx (pKNOpen knIff_holds)
theorem pPart_holds : PPart := pPPart pJEq
theorem memAct_holds : MemAct := pMemAct pMemSum pSumDoset tfAct_holds pDosetCosets
theorem memDeck_holds : MemDeck := pMemDeck pMemSum tfCen_holds
theorem levSec_holds : LevSec := pLevSec pIntConj
theorem knFact_holds : KNFact :=
  pKNFact knIff_holds pFacEq atApart_holds pCongGrpEx (pCongConj pLocComm_of) pLocComm pLocComm_of
theorem siteFact_holds : SiteFact := pSiteFact dict_holds sides_holds pIntConj pLocComm_of
theorem stabKer_holds : StabKer := pStabKer pFacEq knFact_holds pCongGrpEx
theorem seenShape_holds : SeenShape := pSeenShape stabKer_holds siteFact_holds (pCenFacts sides_holds) levBasic_holds pLocComm_of
theorem seenActs_holds : SeenActs := pSeenActs pMemSum memAct_holds memDeck_holds seenShape_holds levBasic_holds knIdx_holds
theorem actsConv_holds : ActsConv := pActsConv pTfAdm tfIdem_holds
theorem phiTy_holds : PhiTy := pPhiTy pPart_holds levSec_holds pFacEq pLocComm

theorem tyFact_holds : Spc.TyFact :=
  pTyFact pFacEq levSec_holds levFact_holds atApart_holds pCongGrpEx pDenom pLocComm pLocComm_of
theorem memFn_holds : Spc.MemFn := pMemFn seenShape_holds seenActs_holds actsConv_holds tyFact_holds
theorem phiEx_holds : Spc.PhiEx :=
  pPhiEx phiTy_holds seenShape_holds seenActs_holds tyFact_holds tfAct_holds tfCen_holds (tEig_of_thLoc (pThLoc_of pLocComm_of CertificateRingHomMap.pOfUBij_of)) atApart_holds pFacEq pJEq
    pLocComm

end UpperTheory.Gal.W2.Seed
end
