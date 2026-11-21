import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFiniteIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolynomialMatchingInduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationPairDerivation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitIdentityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFiniteIdentityStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.LineMatch
open Filter GlobalTheory.WeilM GlobalTheory.AdelicU
theorem polarization_match_deriv : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ Φ', GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' →
    ∀ (Φ₁ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ₁' : (Fin a' × Fin (a + a') → AF F) → ℂ),
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) →
    (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ' x) (Φ₁' x) 0) →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ₁ Φ₁' := by
  intro hP F E _ _ _ _ _ σ a a' B G X om om' R Rf hMt γ hγ Φ Φ' hPM Φ₁ Φ₁' hd hd'
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_lieDerivative_polynomialFock_seesaw B G X om om' hMt.triple γ hγ
  obtain ⟨δ', hδ'⟩ := _root_.GlobalTheory.T.twist_lie_derivative_model hP B G X om om' hMt.triple γ hγ
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', rfl, rfl, heq⟩ := hPM
  have hcof : ∀ {κ : Type} (ψs vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ), (∀ v ∉ T, ψs v = vac v) →
      ∀ᶠ v in cofinite, ψs v = vac v := fun ψs vac h =>
    Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => by
      by_contra h'
      exact hv (h v h'))
  have hpd : ∀ i x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i) x) 0 := fun i x =>
    (hδ (f i) (hf i).1).2 _ (GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz F _ (φ i) (hf i).2.1
      (((hcof _ _ (hf i).2.2).and hMt.triple.geo.hM.std).mono fun v h => h.1.trans h.2) (f i)) x
  have hpd' : ∀ j x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f' j) (φ' j)) x)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ' (f' j)) (φ' j) x) 0 := fun j x =>
    (hδ' (f' j) (hf' j).1).2 _ (GlobalTheory.T.restricted_finprod_pure_tensor_adelic_schwartz F _ (φ' j) (hf' j).2.1
      (((hcof _ _ (hf' j).2.2).and hMt.triple.geo.hM'.std).mono fun v h => h.1.trans h.2) (f' j)) x
  have hΦ₁ : Φ₁ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i) := by
    funext x
    have hs := HasDerivAt.sum (u := Finset.univ) fun i _ => hpd i x
    have e : (∑ i, fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x) =
        fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x := by
      funext t
      rw [Finset.sum_apply, map_sum, Finset.sum_apply]
    rw [e] at hs
    rw [(hd x).unique hs, Finset.sum_apply]
  have hΦ₁' : Φ₁' = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ' (f' j)) (φ' j) := by
    funext x
    have hs := HasDerivAt.sum (u := Finset.univ) fun j _ => hpd' j x
    have e : (∑ j, fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f' j) (φ' j)) x) =
        fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f' j) (φ' j)) x := by
      funext t
      rw [Finset.sum_apply, map_sum, Finset.sum_apply]
    rw [e] at hs
    rw [(hd' x).unique hs, Finset.sum_apply]
  have hR := hMt.real
  set P := G.M.Pol B.ψ B.emb with hPdef
  let pP : P →ₗ[ℂ] R.Pi := R.p ∘ₗ P.subtype
  have hsurj : Function.Surjective pP := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype]
    exact hR.quot.onto
  let g : P →ₗ[ℂ] R.Pi := R.p ∘ₗ δ ∘ₗ P.subtype
  have h0' := hδ' 0 (zero_mem _)
  have hker : LinearMap.ker pP ≤ LinearMap.ker g := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have := hR.lie γ hγ x.1 x.2 0 (zero_mem _) (δ x.1) (δ' 0) (hδ x.1 x.2).2 h0'.2
      (by simpa [pP] using hx)
    simpa [g] using this
  let L : R.Pi →ₗ[ℂ] R.Pi :=
    (LinearMap.ker pP).liftQ g hker ∘ₗ (pP.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hL : ∀ x ∈ P, L (R.p x) = R.p (δ x) := by
    intro x hx
    have e : (pP.quotKerEquivOfSurjective hsurj).symm (R.p x) = Submodule.Quotient.mk ⟨x, hx⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, e, Submodule.liftQ_apply]
    rfl
  have hL' : ∀ x ∈ G.M'.Pol B.ψ B.emb, L (R.p' x) = R.p' (δ' x) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (Submodule.eq_top_iff'.mp hR.quot.onto (R.p' x))
    rw [← hyx, hL y hy]
    exact hR.lie γ hγ y hy x hx (δ y) (δ' x) (hδ y hy).2 (hδ' x hx).2 hyx
  subst hΦ₁ hΦ₁'
  refine ⟨T, hT, m, m', fun i => δ (f i), φ, fun j => δ' (f' j), φ',
    fun i => ⟨(hδ (f i) (hf i).1).1, (hf i).2.1, (hf i).2.2⟩,
    fun j => ⟨(hδ' (f' j) (hf' j).1).1, (hf' j).2.1, (hf' j).2.2⟩, rfl, rfl, ?_⟩
  have := congrArg (LinearMap.rTensor _ L) heq
  simp only [map_sum, LinearMap.rTensor_tmul] at this
  simpa only [hL _ (hf _).1, hL' _ (hf' _).1] using this
end GlobalTheory.LineMatch
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_polarization_match_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ Φ', GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' →
    ∀ (Φ₁ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ₁' : (Fin a' × Fin (a + a') → AF F) → ℂ),
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) →
    (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ' x) (Φ₁' x) 0) →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ₁ Φ₁' := by
  first | exact @_root_.GlobalTheory.LineMatch.polarization_match_deriv | exact _root_.GlobalTheory.LineMatch.polarization_match_deriv | (intros; apply _root_.GlobalTheory.LineMatch.polarization_match_deriv <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.KerDSub
open Filter GlobalTheory.WeilM GlobalTheory.AdelicU
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
theorem ker_derivation_isThetaSubgroup : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∃ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ),
      (∀ Φ, Φ ∈ N ↔ Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ) ∧
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N ∧ N ≠ algD Γ.M' Bs.ψ Bs.emb := by
  intro hP F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM
  obtain ⟨h0, hlin⟩ := GlobalTheory.PolMatchLin.polMatch_linear Bs Γ Xc om om' R Rf hM.fin
  let N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ) :=
    { carrier := {Φ | Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ}
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by simpa using hlin 0 0 x y 1 hx.2 hy.2⟩
      zero_mem' := ⟨zero_mem _, h0⟩
      smul_mem' := fun c x hx => ⟨Submodule.smul_mem _ c hx.1, by simpa using hlin 0 0 0 x c h0 hx.2⟩ }
  have hN : ∀ Φ, Φ ∈ N ↔ Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ := fun _ => Iff.rfl
  have hmem : ∀ Φ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ → Φ ∈ N := fun Φ h =>
    ⟨polMatch_mem_algD Bs Γ Xc R Rf h, h⟩
  have hpa : ∀ f φ, f ∈ Γ.M'.Pol Bs.ψ Bs.emb → (∀ w, φ w ∈ SB _) → (∀ᶠ w in cofinite, φ w = Γ.M'.vac w) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ algD Γ.M' Bs.ψ Bs.emb := fun f φ hf hφ hv =>
    Submodule.subset_span ⟨f, φ, hf, hφ, hv, rfl⟩
  obtain ⟨Φp, hΦp, hnot⟩ := GlobalTheory.T.exists_algebraicDatum_not_matched_zero_by_localMaps Bs Γ Xc om om' R Rf hM
  refine ⟨N, hN, ⟨fun Φ h => h.1, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun e => hnot ((hN Φp).mp (e ▸ hΦp)).2⟩
  ·
    intro v f φ hf hφ hv hφv
    have hz : Rf.p' v (φ v) = 0 := hM.fin.inv' v hφv
    refine hmem _ (polMatch_zero_pure Bs Γ Xc R Rf f hf φ hφ hv {v} fun T hT => ?_)
    rw [MultilinearMap.map_coord_zero _ (⟨v, hT (Finset.mem_singleton_self v)⟩ : T) hz, TensorProduct.tmul_zero]
  ·
    intro γ hγ f hf f₁ hf₁ hact φ hφ hv
    have hz : R.p' f₁ = 0 := hM.real.quot'.lie γ hγ f hf f₁ hact
    exact hmem _ (polMatch_zero_pure Bs Γ Xc R Rf f₁ hf₁ φ hφ hv ∅ fun T _ => by rw [hz, TensorProduct.zero_tmul])
  ·
    intro k hk f hf f₁ hf₁ hact φ hφ hv
    have hz : R.p' (f₁ - f) = 0 := by rw [map_sub, hM.real.quot'.cpt k hk f hf f₁ hact, sub_self]
    rw [← pure_sub]
    exact hmem _ (polMatch_zero_pure Bs Γ Xc R Rf (f₁ - f) (sub_mem hf₁ hf) φ hφ hv ∅ fun T _ => by
      rw [hz, TensorProduct.zero_tmul])
  ·
    classical
    intro v h hh Φ hΦ
    obtain ⟨T, hXT, hOn⟩ := (GlobalTheory.ThK.PolynomialMatching.polMatch_iff Bs Γ Xc R Rf 0 Φ).mp hΦ.2
    have hOn' : GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf (insert v T) 0 Φ := by
      by_cases hvT : v ∈ T
      · rwa [Finset.insert_eq_of_mem hvT]
      · exact GlobalTheory.ThK.PolynomialMatching.polMatchOn_insert F E σ Bs a a' Γ Xc R Rf v
          (hM.fin.sph v fun h' => hvT (hXT h')).1 T 0 Φ hOn
    have := _root_.GlobalTheory.T.polynomial_matching_induction hP F E σ Bs a a' Γ Xc om om' R Rf hM (insert v T) v (Finset.mem_insert_self v T) h hh 0 Φ hOn'
    rw [map_zero] at this
    exact hmem _ ((GlobalTheory.ThK.PolynomialMatching.polMatch_iff Bs Γ Xc R Rf 0 _).mpr
      ⟨insert v T, hXT.trans (Finset.subset_insert v T), this⟩)
  ·
    intro γ hγ Φ hΦ Φ₁ _ hd
    refine hmem _ (_root_.GlobalTheory.T.line_polarization_match_derivative hP Bs Γ Xc om om' R Rf hM γ hγ 0 Φ hΦ.2 0 Φ₁ (fun x => ?_) hd)
    simp only [map_zero, Pi.zero_apply]
    exact hasDerivAt_const 0 (0 : ℂ)
  ·
    intro k hk Φ hΦ
    have := polMatch_kInf Bs Γ Xc om om' R Rf hM k hk 0 Φ hΦ.2
    rw [map_zero] at this
    exact hmem _ this
end GlobalTheory.KerDSub
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSubgroup_of_ker_derivation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∃ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ),
      (∀ Φ, Φ ∈ N ↔ Φ ∈ algD Γ.M' Bs.ψ Bs.emb ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ) ∧
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N ∧ N ≠ algD Γ.M' Bs.ψ Bs.emb := by
  first | exact @_root_.GlobalTheory.KerDSub.ker_derivation_isThetaSubgroup | exact _root_.GlobalTheory.KerDSub.ker_derivation_isThetaSubgroup | (intros; apply _root_.GlobalTheory.KerDSub.ker_derivation_isThetaSubgroup <;> assumption)
end
end
