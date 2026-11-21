import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseSeesawTripleOverHermitian
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUMeasurableEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockDenseArchimedeanSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductDecayVacuumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialFock_dense_archimedeanSchwartz : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → Dense (M.Pol B.ψ B.emb : Set (SInf F (Fin n × Fin d))) := by
  first | exact @GlobalTheory.PolDense.pol_dense | exact GlobalTheory.PolDense.pol_dense | (intros; apply GlobalTheory.PolDense.pol_dense <;> assumption)
end

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in

theorem kapX_surjective : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • Matrix.reindex e e X.gramᵀ), Function.Surjective (GlobalTheory.SquareAgree.kapX X e hJ) := by
  intro D X d e J hJ y
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin X.rank) (AE D), u.1 = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y).submatrix e e :=
    ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom y.1, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y = M := ⟨_, rfl⟩
  obtain ⟨Gt, hGt⟩ : ∃ Gt : Matrix (Fin X.rank) (Fin X.rank) (AE D), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ = Gt := ⟨_, rfl⟩
  have hy : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := y.2
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) = reindex e e Gt := by rw [← hGt]; rfl
  rw [hM, hJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul, e1] at hy
  have hx : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by
    rw [← map_mul, inv_mul_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one]
  have h1 : Mᵀ * reindex e e Gt * M.map (cA D) = reindex e e Gt := by
    have := congrArg (fun A => incA D D.host.xi0⁻¹ • A) hy
    simpa only [smul_smul, hx, one_smul] using this
  have h2 : (M.submatrix e e)ᵀ * Gt * (M.submatrix e e).map (cA D) = Gt := by
    have := congrArg (fun A => A.submatrix e e) h1
    rw [← submatrix_mul_equiv _ _ _ e _, ← submatrix_mul_equiv _ _ _ e _] at this
    simpa [reindex_apply, transpose_submatrix, submatrix_submatrix, ← Matrix.submatrix_map] using this
  have hT : Gtᵀ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram := by rw [← hGt]; exact Matrix.ext fun _ _ => rfl
  have h3 := congrArg transpose h2
  rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc, hT] at h3
  rw [← hM, ← hu] at h3
  refine ⟨(⟨u, h3⟩ : HR (AF D.host.F) D.sp.cm.sig X.gram), ?_⟩
  apply Subtype.ext
  apply Units.ext
  show reindex e e u.1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat y
  rw [hu]
  ext a b
  simp

end GlobalTheory.SquareAgree
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryToTransposeGramGroupMap_surjective : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • Matrix.reindex e e X.gramᵀ), Function.Surjective (GlobalTheory.SquareAgree.kapX X e hJ) := by
  atlas_forward_decl GlobalTheory.SquareAgree.kapX_surjective
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DefThetaNZ

section Darboux

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_zero {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (om : Rep σ Y Wd) (h : UA σ Wd.J) :
    M.I om 0 h = 0 := by
  simp [Model.I, theta, GlobalTheory.WeilM.thetaSum]

theorem I_smul' {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (om : Rep σ Y Wd) (c : ℂ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h : UA σ Wd.J) : M.I om (c • Φ) h = c * M.I om Φ h := by
  simp only [Model.I, theta, map_smul, GlobalTheory.WeilM.thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left,
    MeasureTheory.integral_const_mul]

theorem I_add' {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (om : Rep σ Y Wd)
    {Φ Ψ : (Fin n × Fin d → AF F) → ℂ} {h : UA σ Wd.J}
    (hΦ : MeasureTheory.IntegrableOn (fun g => theta om Φ g h) M.dom M.μ)
    (hΨ : MeasureTheory.IntegrableOn (fun g => theta om Ψ g h) M.dom M.μ)
    (hs : ∀ g, om (g, h) Φ ∈ GlobalTheory.WeilM.schA F _ ∧ om (g, h) Ψ ∈ GlobalTheory.WeilM.schA F _) :
    M.I om (Φ + Ψ) h = M.I om Φ h + M.I om Ψ h := by
  unfold Model.I
  rw [← MeasureTheory.integral_add hΦ hΨ]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun g => ?_)
  show GlobalTheory.WeilM.thetaSum F (om (g, h) (Φ + Ψ)) = GlobalTheory.WeilM.thetaSum F (om (g, h) Φ) + GlobalTheory.WeilM.thetaSum F (om (g, h) Ψ)
  rw [map_add, GlobalTheory.WeilM.thetaSum_add F (hs g).1 (hs g).2]

theorem exists_algD_ne (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') (hDec : Decay B G om om')
    {Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ} (hΦ' : Φ' ∈ G.M'.So B.ψ B.τ₁) (hne : G.M'.I om' Φ' ≠ 0) :
    ∃ ΦD ∈ GlobalTheory.SquareAgree.algD G.M' B.ψ B.emb, G.M'.I om' ΦD ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hne
  clear hne
  funext h
  have hPair := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), om' x Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')) :=
    hPair.weil.isUSplitting.pres
  have hdense := GlobalTheory.T.polynomialFock_dense_archimedeanSchwartz F E σ B _ _ _ _ G.M' _ _ om' _ _ _ _ hPair
  have hsch : ∀ Ψ ∈ G.M'.So B.ψ B.τ₁, Ψ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')) := by
    intro Ψ hΨ
    refine (Submodule.span_le.2 ?_) hΨ
    rintro _ ⟨f, φ, hSB, hvac, -, rfl⟩
    refine GlobalTheory.TensUniq.pure_mem_schA f φ hSB ?_
    filter_upwards [hvac, hT.geo.hM'.std] with v h1 h2
    rw [h1, h2]
  show G.M'.I om' Φ' h = 0
  induction hΦ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hSB, hvac, hv₁, rfl⟩ := hx
    have hc := GlobalTheory.T.restricted_product_decay_vacuum hP F E σ B a a' G X om om' hT hDec φ hSB hvac hv₁ h
    have hz : ∀ P ∈ (G.M'.Pol B.ψ B.emb : Set (SInf F (Fin a' × Fin (a + a')))), G.M'.I om' (pure P φ) h = 0 := fun P hP' =>
      congrFun (hall _ (Submodule.subset_span ⟨P, φ, hP', hSB, hvac, rfl⟩)) h
    have hcl : IsClosed {f : SInf F (Fin a' × Fin (a + a')) | G.M'.I om' (pure f φ) h = 0} := isClosed_eq hc continuous_const
    have hsub := hcl.closure_subset_iff.2 hz
    rw [hdense.closure_eq] at hsub
    exact hsub (Set.mem_univ f)
  | zero => exact I_zero _ _ h
  | add x y hx hy ihx ihy =>
    rw [I_add' G.M' om' ((hDec.2 x hx).2.1 h) ((hDec.2 y hy).2.1 h) (fun g => ⟨hpres _ _ (hsch x hx), hpres _ _ (hsch y hy)⟩),
      ihx, ihy, add_zero]
  | smul c x hx ihx => rw [I_smul', ihx, mul_zero]

end Darboux

end GlobalTheory.DefThetaNZ

namespace GlobalTheory.DefThetaNZ

open scoped Matrix

theorem exists_algF_thetaInt_ne_zero : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
  GlobalTheory.SquareComm.IsTriple W W₁ X α β → (∀ τ, Formalism.UG.HasSignature (gramAt D W₁ τ) W₁.rank 0) →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∃ Φ ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B, GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ ≠ 0 := by
  intro hP hK hL D ψ θ _hψ hθ W W₁ X A A₁ B α β hT _hdef ν₁ 𝓕₁ hν₁ ωA ωB Pi rf rl p p' hM
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D W
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hM.weilA hM.weilB
  obtain ⟨R, Rf, hR⟩ := hL D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨hDec, hK'⟩ := hK.1 D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTD
  obtain ⟨⟨⟨Φ', hΦ'So, hne⟩, -⟩, -⟩ := hK' R Rf hR
  obtain ⟨ΦD, hΦD, hneD⟩ := exists_algD_ne hP hTD hDec hΦ'So hne
  obtain ⟨Φ, hΦ, hDat⟩ := hO.algB' ΦD hΦD
  refine ⟨Φ, hΦ, fun h0 => ?_⟩
  obtain ⟨h', hh'⟩ := Function.ne_iff.1 hneD
  obtain ⟨h, rfl⟩ := GlobalTheory.T.unitaryToTransposeGramGroupMap_surjective D X e hO.JX h'
  have := GlobalTheory.SquareAgree.thetaInt_eq_modelI D W₁ X _ _ _ Γ.M' (-1) hO.JW₁ ν₁ 𝓕₁ ωB om' (GlobalTheory.SquareAgree.kapX X e hO.JX) ΦD Φ
    hO.measW₁ hO.domW₁ (hO.theta_eq_B hDat) h
  rw [h0] at this
  exact hh' this.symm

end GlobalTheory.DefThetaNZ
end
end
