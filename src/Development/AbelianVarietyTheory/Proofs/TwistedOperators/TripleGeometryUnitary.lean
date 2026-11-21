import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityFiniteOfUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleSupNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDerivativePolynomialFockArchimedeanUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsIntertwining

section
open NumberField IsDedekindDomain
open scoped Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HoweNonsplitKer

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

theorem det_ne_of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r s : ℕ}
    (B : Base F E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ w, HasSig (J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [← e, h0, map_zero]

theorem det_ne_of_sig' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r s : ℕ}
    (B : Base F E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ w, HasSig (Complex.I • J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

theorem howe_nonsplit_ker : GlobalTheory.Published.HoweDualityFinite → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, IsEmpty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p v φ = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v hv
  have hT := hM.triple
  have P := GlobalTheory.ThKConst.isPair_big hT
  obtain ⟨hbdd, hsum⟩ := hHD F E σ P.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om P.base.std
    P.herm.herm (det_ne_of_sig Bs G.V.J P.herm.sig) P.skew.skew (det_ne_of_sig' Bs G.W.J P.skew.sig)
    P.resX P.resW P.hX P.hW P.weil v hv
  refine ⟨hbdd, ?_⟩
  intro N hN hNe φ hφ
  have h1 : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := by
    intro u _
    show u • (mat (1 : UA σ G.V.J) - 1) = 0
    have : mat (1 : UA σ G.V.J) = 1 := rfl
    rw [this, sub_self, smul_zero]
  have hex : ∀ h ∈ UAt σ G.W (evFin F v), ∀ ψ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ ψ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) ψ ψ₁ :=
    fun h hh ψ hψ => GlobalTheory.ThK.LocalOps.acts_exists P v (1, h) h1 hh ψ hψ
  set K : Submodule ℂ ((Fin a × Fin (a + a') → Fv F v) → ℂ) :=
    LinearMap.ker (Rf.p v) ⊓ SB (Fin a × Fin (a + a') → Fv F v) with hKdef
  have haugSB : augAt om v ≤ SB (Fin a × Fin (a + a') → Fv F v) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨g, -, ψ, hψ, ψ₁, hψ₁, -, rfl⟩
    exact sub_mem hψ₁ hψ
  have hK : GlobalTheory.Published.ThetaSub om v K := by
    refine ⟨le_inf (hM.fin.inv v) haugSB, inf_le_right, ?_⟩
    intro h hh ψ hψ ψ₁ hψ₁ hact
    have hψ' := Submodule.mem_inf.1 hψ
    have h0 : Acts (evFin F v) (om' (1, h)) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) 0 := by
      intro r _
      have e : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
        funext x; simp [tens]
      rw [e, map_zero]
    have hp := hM.fin.equiv v h hh ψ hψ'.2 0 (zero_mem _) ψ₁ hψ₁ 0 (zero_mem _) hact h0
      (by rw [map_zero]; exact LinearMap.mem_ker.1 hψ'.1)
    rw [map_zero] at hp
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp, hψ₁⟩
  have hKne : K ≠ SB (Fin a × Fin (a + a') → Fv F v) := by
    intro hKe
    have hbot : (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨ψ, hψ, rfl⟩
      rw [← hKe] at hψ
      exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 hψ).1
    rw [hM.fin.onto v] at hbot
    haveI := hM.fin.nontriv v
    exact top_ne_bot hbot
  have hNK : N ⊔ K ≠ SB (Fin a × Fin (a + a') → Fv F v) := hsum N K hN hK hNe hKne
  rcases hM.fin.irred v (N.map (Rf.p v)) (by
    intro h hh ψ hψ ψ₁ hψ₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    have hnSB : n ∈ SB (Fin a × Fin (a + a') → Fv F v) := hN.2.1 hn
    have hkSB : ψ - n ∈ SB (Fin a × Fin (a + a') → Fv F v) := sub_mem hψ hnSB
    have hk : ψ - n ∈ K := Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hpn, sub_self]), hkSB⟩
    obtain ⟨n₁, hn₁, hactn⟩ := hex h hh n hnSB
    obtain ⟨k₁, hk₁, hactk⟩ := hex h hh (ψ - n) hkSB
    have hlin := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (hex h hh) hnSB hkSB hactn hactk 1 1
    simp only [one_smul, add_sub_cancel] at hlin
    have he : ψ₁ = n₁ + k₁ := GlobalTheory.ThK.LocalOps.acts_unique v _ hψ hact hlin
    have hn₁N : n₁ ∈ N := hN.2.2 h hh n hn n₁ hn₁ hactn
    have hk₁K : k₁ ∈ K := hK.2.2 h hh (ψ - n) hk k₁ hk₁ hactk
    have hpk : Rf.p v k₁ = 0 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hk₁K).1
    rw [he, map_add, hpk, add_zero]
    exact Submodule.mem_map_of_mem hn₁N) with h0 | htop
  · have hmem : Rf.p v φ ∈ N.map (Rf.p v) := Submodule.mem_map_of_mem hφ
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  · exfalso
    apply hNK
    refine le_antisymm (sup_le hN.2.1 inf_le_right) ?_
    intro ψ hψ
    have hm : Rf.p v ψ ∈ N.map (Rf.p v) := by rw [htop]; exact Submodule.mem_top
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hm
    have hk : ψ - n ∈ K :=
      Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hpn, sub_self]), sub_mem hψ (hN.2.1 hn)⟩
    have := Submodule.add_mem_sup hn hk
    rwa [add_sub_cancel] at this

end GlobalTheory.HoweNonsplitKer

end
end

section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_global_sum : GlobalTheory.Published.HoweDualityFinite → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, IsEmpty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p v φ = 0 := by
  first | exact @GlobalTheory.HoweNonsplitKer.howe_nonsplit_ker | exact GlobalTheory.HoweNonsplitKer.howe_nonsplit_ker | (intros; apply GlobalTheory.HoweNonsplitKer.howe_nonsplit_ker <;> assumption)
end

section
open NumberField IsDedekindDomain

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_embedding_at_every_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      ∃ (χ : GL (Fin a) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →* ℂˣ)
        (ι : ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ]
          (Matrix (Fin a) (Fin (a + a')) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        IsOpen {g | χ g = 1} ∧
        Set.BijOn ι (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) : Set _)
          (GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) : Set _) ∧
        ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
          N ≤ GlobalTheory.WeilM.SB _ → (GlobalTheory.Published.ThetaSub om v N ↔ GlobalTheory.ThetaGLSub.IsSub χ (N.map ι)) := by
  first | exact @GlobalTheory.SplitTransport.transport | exact GlobalTheory.SplitTransport.transport | (intros; apply GlobalTheory.SplitTransport.transport <;> assumption)
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_submodule_sup_ne_top : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n m : ℕ), 1 ≤ n → 1 ≤ m → ∀ χ : GL (Fin n) k →* ℂˣ, IsOpen {g | χ g = 1} →
    ∀ N N' : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ), GlobalTheory.ThetaGLSub.IsSub χ N → GlobalTheory.ThetaGLSub.IsSub χ N' →
      N ≠ GlobalTheory.SplitWeil.SB _ → N' ≠ GlobalTheory.SplitWeil.SB _ → N ⊔ N' ≠ GlobalTheory.SplitWeil.SB _ := by
  first | exact @GlobalTheory.ThetaGLSub.SumProper.main | exact GlobalTheory.ThetaGLSub.SumProper.main | (intros; apply GlobalTheory.ThetaGLSub.SumProper.main <;> assumption)
end

section
section
open NumberField IsDedekindDomain

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HoweSplitPlace

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

theorem ker_thetaSub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    {R : RealMaps F a a'} {Rf : FinMaps F a a'} (hm : IsMatched Bs G Xc om om' R Rf) (v : Pl F) :
    GlobalTheory.Published.ThetaSub om v (LinearMap.ker (Rf.p v) ⊓ GlobalTheory.WeilM.SB _) := by
  refine ⟨le_inf (hm.fin.inv v) ?_, inf_le_right, ?_⟩
  · rw [augAt, Submodule.span_le]
    rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  · intro h hh φ hφ φ₁ hφ₁ hact
    refine ⟨?_, hφ₁⟩
    have h0 : Acts (evFin F v) (om' (1, h)) 0 0 := by
      intro r _
      have : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) r = 0 :=
        funext fun x => by simp [tens]
      rw [this, map_zero]
    have := hm.fin.equiv v h hh φ hφ.2 0 (Submodule.zero_mem _) φ₁ hφ₁ 0 (Submodule.zero_mem _) hact h0
      (by rw [map_zero]; exact hφ.1)
    rw [map_zero] at this
    exact this

theorem main : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p v φ = 0 := by
  intro hP hMin F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hm v hv
  obtain ⟨χ, ι, hχ, hbij, htr⟩ := GlobalTheory.T.exists_embedding_at_every_place hP F E σ Bs a a' G Xc om om' hm.triple v hv
  have ha : 1 ≤ a := by have := hm.triple.geo.lt; omega
  have hd : 1 ≤ a + a' := by omega
  have hSB : (GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)).map ι = GlobalTheory.SplitWeil.SB _ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hbij.mapsTo hx
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
      exact ⟨x, hx, rfl⟩
  have hinj : ∀ N N' : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
      N ≤ GlobalTheory.WeilM.SB _ → N' ≤ GlobalTheory.WeilM.SB _ → N.map ι ≤ N'.map ι → N ≤ N' := by
    intro N N' hN hN' hle x hx
    obtain ⟨y, hy, hyx⟩ := hle ⟨x, hx, rfl⟩
    rw [hbij.injOn (hN' hy) (hN hx) hyx] at hy
    exact hy
  have hne : ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
      N ≤ GlobalTheory.WeilM.SB _ → N ≠ GlobalTheory.WeilM.SB _ → N.map ι ≠ GlobalTheory.SplitWeil.SB _ := by
    intro N hN hN' he
    exact hN' (le_antisymm hN (hinj _ _ le_rfl hN (by rw [hSB, he])))
  refine ⟨?_, ?_⟩
  · obtain ⟨L, hL⟩ := GlobalTheory.T.theta_submodule_chain_bounded hP _ a (a + a') χ hχ
    refine ⟨L, fun r N hN hT => hL r (fun i => (N i).map ι) ?_ fun i => (htr _ (hT i).2.1).1 (hT i)⟩
    intro i j hij
    refine lt_of_le_of_ne (Submodule.map_mono (hN hij).le) fun heq => (hN hij).ne ?_
    exact le_antisymm (hN hij).le (hinj _ _ (hT j).2.1 (hT i).2.1 heq.ge)
  · intro N hN hNne φ hφ
    set K := LinearMap.ker (Rf.p v) ⊓ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) with hKdef
    have hK : GlobalTheory.Published.ThetaSub om v K := ker_thetaSub hm v
    have hKne : K ≠ GlobalTheory.WeilM.SB _ := by
      intro he
      haveI := hm.fin.nontriv v
      obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
      have hy' : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p v) := by rw [hm.fin.onto v]; trivial
      obtain ⟨x, hx, rfl⟩ := hy'
      rw [← he] at hx
      exact hy hx.1
    have hNK : N ⊔ K ≤ GlobalTheory.WeilM.SB _ := sup_le hN.2.1 inf_le_right
    have hsub : GlobalTheory.Published.ThetaSub om v (N ⊔ K) := by
      refine (htr _ hNK).2 ?_
      rw [Submodule.map_sup]
      exact ((htr _ hN.2.1).1 hN).sup ((htr _ inf_le_right).1 hK)
    have hNKne : N ⊔ K ≠ GlobalTheory.WeilM.SB _ := by
      intro he
      have := GlobalTheory.T.theta_submodule_sup_ne_top hP hMin _ a (a + a') ha hd χ hχ _ _ ((htr _ hN.2.1).1 hN) ((htr _ inf_le_right).1 hK)
        (hne _ hN.2.1 hNne) (hne _ inf_le_right hKne)
      apply this
      rw [← Submodule.map_sup, he, hSB]
    have hmem : ∀ x ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v),
        Rf.p v x ∈ (N ⊔ K).map (Rf.p v) → x ∈ N ⊔ K := by
      intro x hx hpx
      obtain ⟨y, hy, hyx⟩ := hpx
      have hxy : x - y ∈ K := ⟨by simp [LinearMap.mem_ker, map_sub, hyx], Submodule.sub_mem _ hx (hNK hy)⟩
      have : x = y + (x - y) := by abel
      rw [this]
      exact Submodule.add_mem _ hy (Submodule.mem_sup_right hxy)
    rcases hm.fin.irred v ((N ⊔ K).map (Rf.p v)) (fun h hh x hx x₁ hx₁ hact hpx =>
        ⟨x₁, hsub.2.2 h hh x (hmem x hx hpx) x₁ hx₁ hact, rfl⟩) with hbot | htop
    · have : Rf.p v φ ∈ (N ⊔ K).map (Rf.p v) := ⟨φ, Submodule.mem_sup_left hφ, rfl⟩
      rw [hbot] at this
      exact this
    · exfalso
      apply hNKne
      refine le_antisymm hNK fun x hx => hmem x hx ?_
      rw [htop]
      trivial

end GlobalTheory.HoweSplitPlace
end

open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_local_sum : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p v φ = 0 := by
  atlas_forward_decl GlobalTheory.HoweSplitPlace.main
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.HoweRealKer

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    simp
  intro hM
  apply hD
  rw [← Matrix.det_submatrix_equiv_self e.symm, ← hA', Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul]

theorem det_ne_zero_of_sig {E : Type} [Field E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) {r s : ℕ} (h : HasSig (J.map f) r s) : J.det ≠ 0 := by
  intro hJ
  apply det_ne_zero_of_hasSig h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero]

theorem det_ne_zero_of_sigI {E : Type} [Field E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) {r s : ℕ} (h : HasSig (Complex.I • J.map f) r s) : J.det ≠ 0 := by
  intro hJ
  apply det_ne_zero_of_hasSig h
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero, mul_zero]

theorem resEtaPow_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} {n m : ℕ}
    (h : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n)
    (h' : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ' m) :
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (χ / χ') (n + m) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem actsD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ℝ → ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) :
    ActsD (evI F) (fun t => T t) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) ((0 : SInf F κ) : _) := by
  intro r _ x
  have h0 : tens (evI F) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = 0 := by
    funext y; simp [tens]
  simp only [h0, map_zero, Pi.zero_apply]
  exact hasDerivAt_const 0 0

theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) :
    Acts (evI F) T ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) ((0 : SInf F κ) : _) := by
  intro r _
  have h0 : tens (evI F) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = 0 := by
    funext y; simp [tens]
  simp only [h0, map_zero]

theorem main : GlobalTheory.Published.HoweDualityReal → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hMt
  obtain ⟨ht, hr, -⟩ := hMt
  have w0 : InfinitePlace F := Classical.arbitrary _
  have hVdet : G.V.J.det ≠ 0 := det_ne_zero_of_sig _ _ (ht.geo.hV.sig w0)
  have hV'det : G.V'.J.det ≠ 0 := det_ne_zero_of_sig _ _ (ht.geo.hV'.sig w0)
  have hWdet : G.W.J.det ≠ 0 := det_ne_zero_of_sigI _ _ (ht.geo.hW.sig w0)
  have hresW : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (Xc.β / Xc.α) (a + a') :=
    resEtaPow_div ht.chars.resβ ht.chars.resα
  have hresW' : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (Xc.α / Xc.β) (a' + a) :=
    resEtaPow_div ht.chars.resα ht.chars.resβ
  rw [Nat.add_comm a' a] at hresW'
  have hHk := isHecke_div ht.chars.heckeβ ht.chars.heckeα
  have hHk' := isHecke_div ht.chars.heckeα ht.chars.heckeβ
  obtain ⟨hchain, hsum⟩ := hHD F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have L := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have L' := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ ht.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' ht.base.std
    ht.geo.hV'.herm hV'det ht.geo.hW.skew hWdet ht.chars.resα hresW' ht.chars.heckeα hHk' ht.weil' Bs.emb
    ht.geo.hV'.cartan ht.geo.hW.cartan
  have C := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have C' := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ ht.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' ht.base.std
    ht.geo.hV'.herm hV'det ht.geo.hW.skew hWdet ht.chars.resα hresW' ht.chars.heckeα hHk' ht.weil' Bs.emb
    ht.geo.hV'.cartan ht.geo.hW.cartan
  refine ⟨hchain, ?_⟩
  intro N hN hNP

  set P := G.M.Pol Bs.ψ Bs.emb with hPdef
  let K : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) := LinearMap.ker R.p ⊓ P
  have hK : GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om K := by
    refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
    · intro γ hγ g hg g₁ hg₁
      exact ⟨LinearMap.mem_ker.mpr (hr.quot.lie γ hγ g hg g₁ hg₁), hN.1 (hN.2.1 γ hγ g hg g₁ hg₁)⟩
    · intro k hk g hg g₁ hg₁
      refine ⟨?_, hN.1 (hN.2.2.1 k hk g hg g₁ hg₁)⟩
      show R.p (g₁ - g) = 0
      rw [map_sub, hr.quot.cpt k hk g hg g₁ hg₁, sub_self]
    · intro γ hγ g hg g₁ hg₁
      refine ⟨?_, (L γ hγ g hg.2).2 g₁ hg₁⟩
      have e := hr.lie γ hγ g hg.2 0 (Submodule.zero_mem _) g₁ 0 hg₁ (actsD_zero _)
        (by rw [LinearMap.mem_ker.mp hg.1, map_zero])
      show R.p g₁ = 0
      rw [e, map_zero]
    · intro k hk g hg g₁ hg₁
      refine ⟨?_, (C k hk g hg.2).2 g₁ hg₁⟩
      have e := hr.cpt k hk g hg.2 0 (Submodule.zero_mem _) g₁ 0 hg₁ (acts_zero _)
        (by rw [LinearMap.mem_ker.mp hg.1, map_zero])
      show R.p g₁ = 0
      rw [e, map_zero]
  have hKP : K ≠ P := by
    intro hKP
    haveI := hr.nontriv
    have hle : P ≤ LinearMap.ker R.p := hKP ▸ inf_le_left
    have hbot : P.map R.p = ⊥ := by
      rw [eq_bot_iff, Submodule.map_le_iff_le_comap]
      intro x hx
      simpa [Submodule.mem_comap] using hle hx
    exact bot_ne_top (hbot.symm.trans hr.quot.onto)

  have hirr := hr.irred (N.map R.p) ?_ ?_
  · rcases hirr with hbot | htop
    · intro f hf
      have : R.p f ∈ N.map R.p := Submodule.mem_map_of_mem hf
      rw [hbot] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exfalso
      apply hsum N K hN hK hNP hKP
      refine le_antisymm (sup_le hN.1 inf_le_right) ?_
      intro g hg
      have hpg : R.p g ∈ N.map R.p := htop ▸ Submodule.mem_top
      obtain ⟨n₀, hn₀, hpn⟩ := hpg
      have hk : g - n₀ ∈ K := ⟨show R.p (g - n₀) = 0 by rw [map_sub, hpn, sub_self], P.sub_mem hg (hN.1 hn₀)⟩
      have := Submodule.add_mem_sup hn₀ hk
      simpa using this
  · intro γ hγ g hg g₁ hg₁ hpg
    obtain ⟨n₀, hn₀, hpn⟩ := hpg
    have hg' : R.p g ∈ (G.M'.Pol Bs.ψ Bs.emb).map R.p' := hr.quot'.onto ▸ Submodule.mem_top
    obtain ⟨g', hg'P, hpg'⟩ := hg'
    obtain ⟨g₁', hg₁'⟩ := (L' γ hγ g' hg'P).1
    obtain ⟨n₁, hn₁⟩ := (L γ hγ n₀ (hN.1 hn₀)).1
    have e1 := hr.lie γ hγ g hg g' hg'P g₁ g₁' hg₁ hg₁' hpg'.symm
    have e2 := hr.lie γ hγ n₀ (hN.1 hn₀) g' hg'P n₁ g₁' hn₁ hg₁' (hpn.trans hpg'.symm)
    exact ⟨n₁, hN.2.2.2.1 γ hγ n₀ hn₀ n₁ hn₁, e2.trans e1.symm⟩
  · intro k hk g hg g₁ hg₁ hpg
    obtain ⟨n₀, hn₀, hpn⟩ := hpg
    have hg' : R.p g ∈ (G.M'.Pol Bs.ψ Bs.emb).map R.p' := hr.quot'.onto ▸ Submodule.mem_top
    obtain ⟨g', hg'P, hpg'⟩ := hg'
    obtain ⟨g₁', hg₁'⟩ := (C' k hk g' hg'P).1
    obtain ⟨n₁, hn₁⟩ := (C k hk n₀ (hN.1 hn₀)).1
    have e1 := hr.cpt k hk g hg g' hg'P g₁ g₁' hg₁ hg₁' hpg'.symm
    have e2 := hr.cpt k hk n₀ (hN.1 hn₀) g' hg'P n₁ g₁' hn₁ hg₁' (hpn.trans hpg'.symm)
    exact ⟨n₁, hN.2.2.2.2 k hk n₀ hn₀ n₁ hn₁, e2.trans e1.symm⟩

end GlobalTheory.HoweRealKer
end
end

open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift : GlobalTheory.Published.HoweDualityReal → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0 := by
  atlas_forward_decl GlobalTheory.HoweRealKer.main
end

section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_intertwining : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p v φ = 0) →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      N ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb →
      ∀ ΦD ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0 := by
  first | exact @GlobalTheory.HoweGlobal.allInKer | exact GlobalTheory.HoweGlobal.allInKer | (intros; apply GlobalTheory.HoweGlobal.allInKer <;> assumption)
end

section
section
open NumberField IsDedekindDomain

namespace GlobalTheory.HoweEveryPlace

theorem allInKer : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      N ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb →
      ∀ ΦD ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0 := by
  intro hU hR hMin hP F E _ _ _ _ _ σ Bs a a' G Xc om om' _ R Rf hM N hN hne
  refine GlobalTheory.T.matched_maps_intertwining hP F E σ Bs a a' G Xc om om' R Rf hM (fun v => ?_)
    (GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift hR F E σ Bs a a' G Xc om om' R Rf hM) N hN hne
  rcases isEmpty_or_nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) with h | h
  · exact GlobalTheory.T.matched_maps_global_sum (GlobalTheory.T.howe_duality_finite_of_unitary hP hU) F E σ Bs a a' G Xc om om' R Rf hM v h
  · exact GlobalTheory.T.matched_maps_local_sum hP hMin F E σ Bs a a' G Xc om om' R Rf hM v h

end GlobalTheory.HoweEveryPlace
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_geometry_unitary : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      N ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb →
      ∀ ΦD ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0 := by
  atlas_forward_decl GlobalTheory.HoweEveryPlace.allInKer
end
