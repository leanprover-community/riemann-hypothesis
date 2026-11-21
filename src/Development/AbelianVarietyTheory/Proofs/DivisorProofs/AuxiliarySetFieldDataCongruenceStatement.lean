import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodConjugateIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetReductionGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodProductIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealEmbeddingOrdering
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalAppellHumbertRealMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingFractionEmbeddingStatement

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Div.ConjugateOrderConductor
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

theorem conj_orderC_bot {E : Type} [Field E] [NumberField E] [IsCMField E] (a : orderC (⊥ : Ideal (OF E))) :
    IsCMField.complexConj E (a : E) = (a : E) := by
  have hle : orderC (⊥ : Ideal (OF E)) ≤ RingHom.eqLocus ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →+* E) (RingHom.id E) := by
    unfold orderC
    rw [Subring.closure_le]
    rintro x (⟨b, rfl⟩ | ⟨b, hb, rfl⟩)
    · show IsCMField.complexConj E (algebraMap (OF E) E b) = algebraMap (OF E) E b
      rw [IsScalarTower.algebraMap_apply (OF E) (maximalRealSubfield E) E]
      exact IsCMField.complexConj_apply_eq_self E _
    · rw [Ideal.map_bot, Ideal.mem_bot] at hb
      subst hb
      show IsCMField.complexConj E (algebraMap (𝓞 E) E 0) = algebraMap (𝓞 E) E 0
      simp
  exact hle a.2

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (H : Type) [AddCommGroup H]
    [Module R H] (I : Type) (φ : I → E →+* K) (ρ : orderC c →+* Module.End R H) (Fil : Submodule R H)
    (B : LinearMap.BilinForm R H) (e f : I → H) (N : Module.End K (K ⊗[R] H)) (i : I),
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice φ ρ Fil B → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens φ ρ e f →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsLower ρ (φ i) (e i) (f i) N → c ≠ ⊥ := by
  intro E _ _ _ c R _ _ _ K _ _ _ H _ _ I φ ρ Fil B e f N i hL hG hN hc
  subst hc
  obtain ⟨hfree, -, -, hline, -⟩ := hL
  have heq : eigK ρ (φ i) = eigK ρ (bar (φ i)) := by
    unfold eigK
    congr 1
    funext a
    congr 1
    show φ i (a : E) = φ i (IsCMField.complexConj E (a : E))
    rw [conj_orderC_bot]
  have he : inK (O := R) K H (e i) ∈ eigK ρ (bar (φ i)) := by
    rw [← heq]
    show e i ∈ eigLat ρ (φ i)
    rw [(hG i).1]; exact Submodule.mem_span_singleton_self _
  have h0 : inK (O := R) K H (f i) = 0 := by
    rw [← hN.1]
    exact hN.2 _ (GlobalTheory.LowerOps.bar_ne_self _) _ he
  have hf : f i = 0 := by
    by_contra hf
    exact GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero hfree hf h0
  obtain ⟨g, hg0, hg⟩ := GlobalTheory.EigenLattice.exists_ne_mem ρ (bar (φ i)) (hline _)
  rw [(hG i).2, hf, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hg
  exact hg0 hg

end GlobalTheory.Div.ConjugateOrderConductor
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EigLineSumCM

open Classical in

theorem eigK_isInternal_of_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ (R : Type) [CommRing R] [IsDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq (E →+* K)] (H : Type)
    [AddCommGroup H] [Module R H] (I : Type) [Fintype I] (φ : I → E →+* K) (ρ : orderC c →+* Module.End R H)
    (Fil : Submodule R H) (B : LinearMap.BilinForm R H), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice φ ρ Fil B →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMTypeIn φ → 2 * Fintype.card I = Module.finrank ℚ E →
    DirectSum.IsInternal (fun σ : E →+* K ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) := by
  intro E _ _ _ c hc R _ _ K _ _ _ _ H _ _ I _ φ ρ Fil B hL hT hI
  obtain ⟨hfree, hfin, hrank, hline, -⟩ := hL

  let g : I × Bool → (E →+* K) := fun p => if p.2 then φ p.1 else GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ p.1)
  have hg_or : ∀ p : I × Bool, g p = φ p.1 ∨ g p = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ p.1) := by
    rintro ⟨i, b⟩; cases b <;> simp [g]
  have hgbij : Function.Bijective g := by
    constructor
    · rintro ⟨i, b⟩ ⟨j, b'⟩ h
      have hij : i = j := by
        obtain ⟨k, -, hk⟩ := hT (g (i, b))
        have h1 := hk i (hg_or (i, b))
        have h2 := hk j (by rw [h]; exact hg_or (j, b'))
        rw [h1, h2]
      subst hij
      have hne := GlobalTheory.LowerOps.bar_ne_self (φ i)
      cases b <;> cases b'
      · rfl
      · have h' : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) = φ i := by simpa [g] using h
        exact absurd h' hne
      · have h' : φ i = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) := by simpa [g] using h
        exact absurd h'.symm hne
      · rfl
    · intro σ
      obtain ⟨i, hi, -⟩ := hT σ
      rcases hi with h | h
      · exact ⟨(i, true), by simp [g, h]⟩
      · exact ⟨(i, false), by simp [g, h]⟩
  have hcard : Nat.card (E →+* K) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_of_bijective g hgbij, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_bool, ← hI, mul_comm]
  let f : orderC c → Module.End K (K ⊗[R] H) := fun a => (ρ a).baseChange K
  have hcomm : ∀ a b, Commute (f a) (f b) := fun a b => by
    show (ρ a).baseChange K * (ρ b).baseChange K = (ρ b).baseChange K * (ρ a).baseChange K
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, ← map_mul, ← map_mul, mul_comm]
  have hind0 := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  have hinj : Function.Injective (fun σ : E →+* K => fun a : orderC c => σ a) := fun σ σ' h =>
    GlobalTheory.EigLineSum.ringHom_eq_of_eq_on_orderC hc (fun a => congrFun h a)
  have hind : iSupIndep (fun σ : E →+* K => GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) :=
    (hind0.comp hinj).mono fun σ => iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace
  haveI : Finite (E →+* K) := Finite.of_surjective g hgbij.2
  haveI := Fintype.ofFinite (E →+* K)
  have htot : Module.finrank K (K ⊗[R] H) = Module.finrank ℚ E := by
    rw [Module.finrank_baseChange, hrank]
  have hinjD : Function.Injective (DirectSum.coeLinearMap (fun σ : E →+* K => GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ)) :=
    hind.dfinsupp_lsum_injective
  have hdim : Module.finrank K (DirectSum (E →+* K) fun σ => GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) =
      Module.finrank K (K ⊗[R] H) := by
    rw [Module.finrank_directSum, htot, ← hcard, Nat.card_eq_fintype_card]
    simp [hline]
  exact ⟨hinjD, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinjD⟩

end GlobalTheory.EigLineSumCM
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.PairingEigenspaceOrthogonal

theorem pairing_eig_orth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K] (H : Type) [AddCommGroup H] [Module R H]
    (I : Type) (φ : I → E →+* K) (ρ : orderC c →+* Module.End R H) (Fil : Submodule R H) (B : LinearMap.BilinForm R H),
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice φ ρ Fil B → ∀ σ σ' : E →+* K, σ' ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ →
    ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ, ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ', B.baseChange K x y = 0 := by
  intro E _ _ _ c hc R _ K _ _ H _ _ I φ ρ Fil B hL σ σ' hne x hx y hy
  have hadj := hL.2.2.2.2.2.2.2.2

  have hne' : σ ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' := by
    intro h; apply hne; rw [h]; ext z; simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar, IsCMField.complexConj_apply_apply]
  obtain ⟨a, ha⟩ : ∃ a : orderC c, σ a ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' a := by
    by_contra hall; push_neg at hall
    exact hne' (GlobalTheory.EigLineSum.ringHom_eq_of_eq_on_orderC hc hall)
  let b : orderC c := ⟨IsCMField.complexConj E (a : E), GlobalTheory.LatModel.HalfFormUnit.conj_mem_orderC a.2⟩
  have hK : ∀ u v : K ⊗[R] H, B.baseChange K ((ρ a).baseChange K u) v = B.baseChange K u ((ρ b).baseChange K v) := by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u1 u2 h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2]
    | tmul r m =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v1 v2 h1 h2 => simp only [map_add, h1, h2]
      | tmul r' m' =>
        simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul]
        rw [hadj a b rfl m m']
  have h1 := hK x y
  rw [GlobalTheory.LowerOps.act_of_mem_eigK hx a, GlobalTheory.LowerOps.act_of_mem_eigK hy b] at h1
  simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have hb : σ' (b : E) = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' a := rfl
  rw [hb] at h1
  have h2 : (σ a - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ' a) * B.baseChange K x y = 0 := by rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)

end GlobalTheory.Div.PairingEigenspaceOrthogonal
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.LowerPairFormula

theorem lower_pair_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq (E →+* K)] (H : Type) [AddCommGroup H]
    [Module R H] (I : Type) (φ : I → E →+* K) (ρ : orderC c →+* Module.End R H) (Fil : Submodule R H)
    (B : LinearMap.BilinForm R H) (e f : I → H) (N : Module.End K (K ⊗[R] H)) (i : I),
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) →
    (∀ σ σ' : E →+* K, σ' ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ,
      ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ', B.baseChange K x y = 0) →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens φ ρ e f → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsLower ρ (φ i) (e i) (f i) N →
    B (e i) (f i) ≠ 0 ∧ ∀ w, N w = (B.baseChange K w (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i)) / algebraMap R K (B (e i) (f i))) •
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i) := by
  intro E _ _ _ c R _ _ _ K _ _ _ _ H _ _ I φ ρ Fil B e f N i hL hdir horth hG hN
  obtain ⟨hfree, -, -, hlines, -, -, hbij, -, -⟩ := hL
  have hBK : ∀ u v : H, B.baseChange K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H u) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H v) = algebraMap R K (B u v) := by
    intro u v
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK, LinearMap.BilinForm.baseChange_tmul, Algebra.algebraMap_eq_smul_one]
  have he_mem : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (e i) ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (φ i) := by
    have hm : e i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (K := K) ρ (φ i) := by rw [(hG i).1]; exact Submodule.mem_span_singleton_self _
    exact hm
  have hf_mem : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i) ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)) := by
    have hm : f i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (K := K) ρ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)) := by
      rw [(hG i).2]; exact Submodule.mem_span_singleton_self _
    exact hm
  have hei : e i ≠ 0 := by
    intro h0
    obtain ⟨g, hg0, hg⟩ := GlobalTheory.EigenLattice.exists_ne_mem ρ (φ i) (hlines (φ i))
    rw [(hG i).1, h0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hg
    exact hg0 hg
  have he0 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (e i) ≠ 0 := GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero hfree hei
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ z : K ⊗[R] H, z ∈ ⨆ σ : E →+* K, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ := fun z => by
    rw [hdir.submodule_iSup_eq_top]; exact Submodule.mem_top
  have hb : B (e i) (f i) ≠ 0 := by
    intro hb0
    have hBe : B (e i) ≠ 0 := fun h => hei (hbij.1 (by rw [h, map_zero]))
    obtain ⟨u, hu⟩ : ∃ u, B (e i) u ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hBe (LinearMap.ext hcon)
    have hall : ∀ v : K ⊗[R] H, B.baseChange K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (e i)) v = 0 := by
      intro v
      refine Submodule.iSup_induction (fun σ : E →+* K => GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ)
        (motive := fun v => B.baseChange K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (e i)) v = 0) (hmem v) ?_ (by simp) ?_
      · intro σ' v hv
        by_cases hσ : σ' = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)
        · subst hσ
          obtain ⟨k, rfl⟩ := GlobalTheory.Div.eigen_line_bilinear.eq_smul_of_line (hlines _) hf_mem
            (GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero hfree (fun h0 => by
              obtain ⟨g, hg0, hg⟩ := GlobalTheory.EigenLattice.exists_ne_mem ρ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)) (hlines _)
              rw [(hG i).2, h0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hg
              exact hg0 hg)) hv
          rw [map_smul, hBK, hb0, map_zero, smul_zero]
        · exact horth (φ i) σ' hσ _ he_mem v hv
      · intro x y hx hy
        rw [map_add, hx, hy, add_zero]
    have := hall (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H u)
    rw [hBK] at this
    exact hu (hinj (by rw [this, map_zero]))
  have hb' : algebraMap R K (B (e i) (f i)) ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
  refine ⟨hb, fun w => ?_⟩
  refine Submodule.iSup_induction (fun σ : E →+* K => GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ)
    (motive := fun w => N w = (B.baseChange K w (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i)) / algebraMap R K (B (e i) (f i))) •
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i)) (hmem w) ?_ (by simp) ?_
  · intro σ w hw
    by_cases hσ : σ = φ i
    · subst hσ
      obtain ⟨k, rfl⟩ := GlobalTheory.Div.eigen_line_bilinear.eq_smul_of_line (hlines _) he_mem he0 hw
      rw [map_smul, hN.1, map_smul, LinearMap.smul_apply, hBK, smul_eq_mul, mul_div_assoc, div_self hb', _root_.mul_one]
    · have hne : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ := by
        intro h
        apply hσ
        have := congrArg GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar h
        rw [GlobalTheory.Div.eigen_line_bilinear.bar_bar, GlobalTheory.Div.eigen_line_bilinear.bar_bar] at this
        exact this.symm
      rw [hN.2 σ hσ w hw, horth σ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)) hne w hw _ hf_mem, zero_div, zero_smul]
  · intro x y hx hy
    rw [map_add, hx, hy, map_add, LinearMap.add_apply, add_div, add_smul]

end GlobalTheory.Div.LowerPairFormula
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.CorrespondenceTransfer

theorem corr_smul' {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {b : Sp R' ⟶ Sp R} {q : A'.left ⟶ A.left}
    {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b q} {x : HdR A} {x' : HdR A'}
    (hx : m.Corr x x') (r : R) : m.Corr (r • x) (σ r • x') := fun c ↦ by
  simp only [LinearMap.smul_apply, smul_eq_mul, hx c, map_mul]

theorem transfer : ∀ (R : Subring ℂ) (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp ℂ)) [GrpObj A'] (p : A'.left ⟶ A.left)
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 ℂ) (𝟙 _) A' (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC →
    ∀ (n : ℕ) (eH : HdR A ≃ₗ[R] (Fin n → R)) (x y : Fin n → R) (k : FractionRing R),
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) x = k • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) y →
    ∀ X Y, m.Corr (eH.symm x) X → m.Corr (eH.symm y) Y → X = j k • Y := by
  intro R j hj A _ A' _ p m hm n eH x y k hk X Y hX hY
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) k
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hs (Subtype.ext (by simpa using h0))
  have hsK : algebraMap R (FractionRing R) s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs

  have hlin : s • x = r • y := by
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (s • x - r • y) = 0 := by
      rw [map_sub, map_smul, map_smul, hk, ← algebraMap_smul (FractionRing R) s,
        ← algebraMap_smul (FractionRing R) r, smul_smul,
        show algebraMap R (FractionRing R) s * (algebraMap R (FractionRing R) r / algebraMap R (FractionRing R) s)
          = algebraMap R (FractionRing R) r by field_simp, sub_self]
    by_contra hne
    exact GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero (K := FractionRing R) inferInstance (sub_ne_zero.2 hne) h1
  have e1 : m.Corr (eH.symm (s • x)) (algebraMap R ℂ s • X) := by
    rw [map_smul]; exact corr_smul' hX s
  have e2 : m.Corr (eH.symm (s • x)) (algebraMap R ℂ r • Y) := by
    rw [hlin, map_smul]; exact corr_smul' hY r
  have heq := hm.unique e1 e2
  have hjk : j (algebraMap R (FractionRing R) r / algebraMap R (FractionRing R) s) = (r : ℂ) / s := by
    rw [map_div₀, hj, hj]
  rw [hjk]
  have hs' : algebraMap R ℂ s = (s : ℂ) := rfl
  have hr' : algebraMap R ℂ r = (r : ℂ) := rfl
  rw [hs', hr'] at heq
  rw [div_eq_inv_mul, mul_smul, ← heq, smul_smul, inv_mul_cancel₀ hs0, one_smul]

end GlobalTheory.Div.CorrespondenceTransfer
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowerCx

theorem numeric_product_inequality (Dc ψe ψx lam n' bu be : ℂ) (hlam : lam ≠ 0) (hψe : ψe ≠ 0) (hbe : be ≠ 0)
    (hX : lam * ψx = n' * bu) (hE : lam * ψe = n' * be) : Dc / ψe * ψx = Dc * (bu / be) := by
  have key : ψx * be = ψe * bu :=
    mul_left_cancel₀ hlam (by linear_combination be * hX - bu * hE)
  field_simp
  linear_combination Dc * key

theorem baseChange_inK {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {H : Type} [AddCommGroup H]
    [Module R H] (B : LinearMap.BilinForm R H) (u v : H) :
    B.baseChange K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) K H u) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) K H v) = algebraMap R K (B u v) := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK, LinearMap.BilinForm.baseChange_tmul, Algebra.algebraMap_eq_smul_one]

theorem polForm_bc' {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply Limits.pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

theorem formRel : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔠 : FracId (FR E))
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left),
    X.IsPullBy X₀ (spMap R.subtype) p →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p) (c₀ c₁ : 𝔠.elt),
    (c₁ : FR E) ≠ 0 → ∀ (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)) (ψ : LinearMap.BilinForm ℂ (HdR X.A)),
    IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ψ₀ → IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag c₁) ψ →
    ∃ (n' : ℕ) (t : 𝓞 (FR E)), n' ≠ 0 ∧ ∀ x₀ y₀ x y, m.Corr x₀ x → m.Corr y₀ y →
      ψ x (act (dp0 ℂ) (𝟙 _) X.rm t y) = n' * algebraMap R ℂ (ψ₀ x₀ y₀) := by
  intro hADR E _ _ _ 𝔠 R X₀ X p hpull m c₀ c₁ hc₁ ψ₀ ψ hψ₀ hψ
  obtain ⟨ψ₀', hψ₀', hcorr⟩ := polForm_bc' (algebraMap R ℂ) hpull m c₀ hψ₀
  obtain ⟨n', t, hn', ht⟩ := GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq hADR (FR E) 𝔠 ℂ X c₀ c₁ hc₁ ψ₀' ψ hψ₀' hψ
  exact ⟨n', t, hn', fun x₀ y₀ x y hx hy ↦ by rw [← ht, hcorr x₀ x y₀ y hx hy]⟩

set_option maxHeartbeats 1000000 in

theorem lower_cx : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E))
    (y : (Af E)ˣ) (𝔠 : FracId (FR E)) (R : Subring ℂ) [IsDiscreteValuationRing R]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X)
    (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC c) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
    (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) →
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
      ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMTypeIn (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) →
    ∀ (D : R), D ≠ 0 →
    ∀ (e' f' : I → (Fin n → R)), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) e' f' →
    ∀ (N : I → Module.End (FractionRing R) (FractionRing R ⊗[R] (Fin n → R))) (M : I → Module.End R (Fin n → R)),
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsLower (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (e' i) (f' i) (N i)) →
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsScaledRestr D (N i) (M i)) →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC → ∀ (ψ : LinearMap.BilinForm ℂ (HdR X.A)), IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ →
    ∀ (yv ev : I → HdR X.A), (∀ i, m.Corr (eH.symm (f' i)) (yv i)) → (∀ i, m.Corr (eH.symm (e' i)) (ev i)) →
    ∀ i, ψ (ev i) (yv i) ≠ 0 ∧ ∀ x₀ x, m.Corr x₀ x →
      m.Corr (eH.symm.conjRingEquiv (M i) x₀) ((((D : ℂ) / ψ (ev i) (yv i)) • (ψ.flip (yv i)).smulRight (yv i)) x) := by
  intro hPC hADR hADC E _ _ _ I _ φ c y 𝔠 R _ X₀ X U p cm hpull hcm hα j hj φK hφK n eH c₀ ψ₀ hc₀ hψ₀ hlat hcmt D hD
    e' f' hgens N M hlow hscal m hbc ψ hψ yv ev hyv hev i
  classical
  set ρ := eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm) with hρ
  set B := (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) with hB
  have hc : c ≠ ⊥ := GlobalTheory.Div.ConjugateOrderConductor.main E c R (FractionRing R) (Fin n → R) I _ ρ _ B e' f' (N i) i hlat hgens (hlow i)
  have hcard : 2 * Fintype.card I = Module.finrank ℚ E := by
    rw [← Fintype.card_congr U.e, Fintype.card_fin, ← Module.finrank_mul_finrank ℚ (FR E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (FR E) E, mul_comm]
  have hint := GlobalTheory.EigLineSumCM.eigK_isInternal_of_cmType E c hc R (FractionRing R) (Fin n → R) I _ ρ _ B hlat hcmt hcard
  have horth := GlobalTheory.Div.PairingEigenspaceOrthogonal.pairing_eig_orth E c hc R (FractionRing R) (Fin n → R) I _ ρ _ B hlat
  obtain ⟨hBef, hN⟩ := GlobalTheory.Div.LowerPairFormula.lower_pair_formula E c R (FractionRing R) (Fin n → R) I _ ρ _ B e' f' (N i) i hlat hint horth hgens (hlow i)
  have hU : ((U.c : FR E)) ≠ 0 := by
    intro h0
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace (FR E)))
    have hw : w.IsReal := NumberField.IsTotallyReal.isReal w
    have := U.pos (NumberField.InfinitePlace.embedding_of_isReal hw)
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨n', t, hn', hrel⟩ : ∃ (n' : ℕ) (t : 𝓞 (FR E)), n' ≠ 0 ∧ ∀ x₀ y₀ x y, m.Corr x₀ x → m.Corr y₀ y →
      ψ x (act (dp0 ℂ) (𝟙 _) X.rm t y) = n' * algebraMap R ℂ (ψ₀ x₀ y₀) := by
    obtain ⟨n₁, t, hn₁, h⟩ := formRel hADR E 𝔠 R X₀ X p hpull m c₀ U.c hU _ ψ hψ₀ hψ
    refine ⟨n₁ * 2, t, mul_ne_zero hn₁ two_ne_zero, fun x₀ y₀ x y hx hy ↦ ?_⟩
    rw [h x₀ y₀ x y hx hy, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, map_ofNat]
    push_cast
    ring
  set a : orderC c := GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t
  have hact : ∀ y₀ y', m.Corr y₀ y' →
      m.Corr (act (dp0 R) (𝟙 _) X₀.rm t y₀) (act (dp0 ℂ) (𝟙 _) X.rm t y') := by
    intro y₀ y' h
    haveI := X₀.rm.hom t
    haveI := X.rm.hom t
    exact GrpMor.Corr.push m (X₀.rm.act t) (X.rm.act t) (hpull.act t).symm h
  have hcmt' : act (dp0 R) (𝟙 _) X₀.rm t = act (dp0 R) (𝟙 _) cm a := by
    haveI := X₀.rm.hom t
    haveI := cm.hom a
    rw [act_apply, act_apply]
    exact push_congr _ _ (hcm t).symm
  have hρa : ∀ v, eH.symm (ρ a v) = act (dp0 R) (𝟙 _) cm a (eH.symm v) := by
    intro v
    simp [hρ, LinearEquiv.conjRingEquiv]
  have hfmem : f' i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (K := FractionRing R) ρ
      (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) := by
    rw [(hgens i).2]; exact Submodule.mem_span_singleton_self _
  have hinKa : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (ρ a (f' i)) =
      (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) (a : E) •
        GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (f' i) := by
    rw [GlobalTheory.EigenLattice.inK_apply_map]
    exact GlobalTheory.LowerOps.act_of_mem_eigK hfmem a
  set lam := j ((GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) (a : E))
  have hty : act (dp0 ℂ) (𝟙 _) X.rm t (yv i) = lam • yv i := by
    refine GlobalTheory.Div.CorrespondenceTransfer.transfer R j hj X₀.A X.A p m hbc n eH (ρ a (f' i)) (f' i) _ hinKa _ _ ?_ (hyv i)
    rw [hρa, ← hcmt']
    exact hact _ _ (hyv i)
  have hrel' : ∀ x₀ x, m.Corr x₀ x → lam * ψ x (yv i) = n' * algebraMap R ℂ (ψ₀ x₀ (eH.symm (f' i))) := by
    intro x₀ x hx
    rw [← hrel x₀ _ x (yv i) hx (hyv i), hty, map_smul, smul_eq_mul]
  have hE := hrel' _ _ (hev i)
  have hσB : ∀ u, algebraMap R ℂ (ψ₀ (eH.symm u) (eH.symm (f' i))) = j (algebraMap R (FractionRing R) (B u (f' i))) :=
    fun u ↦ (hj _).symm
  have hBne : j (algebraMap R (FractionRing R) (B (e' i) (f' i))) ≠ 0 := by
    rw [hj]
    intro h0
    exact hBef (Subtype.ext (by simpa using h0))
  have hne : (n' : ℂ) * algebraMap R ℂ (ψ₀ (eH.symm (e' i)) (eH.symm (f' i))) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hn') (by rw [hσB]; exact hBne)
  rw [← hE] at hne
  have hlam : lam ≠ 0 := left_ne_zero_of_mul hne
  have hψne : ψ (ev i) (yv i) ≠ 0 := right_ne_zero_of_mul hne
  refine ⟨hψne, fun x₀ x hx ↦ ?_⟩
  have hx₀ : x₀ = eH.symm (eH x₀) := (eH.symm_apply_apply x₀).symm
  have hX := hrel' x₀ x hx
  rw [hx₀, hσB] at hX
  rw [hσB] at hE
  have hMK : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (M i (eH x₀)) =
      (algebraMap R (FractionRing R) D * (algebraMap R (FractionRing R) (B (eH x₀) (f' i)) /
        algebraMap R (FractionRing R) (B (e' i) (f' i)))) •
        GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (O := R) (FractionRing R) (Fin n → R) (f' i) := by
    rw [hscal i (eH x₀), hN, smul_smul]
    rw [baseChange_inK]
  obtain ⟨Z, hZ⟩ := hbc.exists (eH.symm (M i (eH x₀)))
  have hZ' := GlobalTheory.Div.CorrespondenceTransfer.transfer R j hj X₀.A X.A p m hbc n eH (M i (eH x₀)) (f' i) _ hMK Z (yv i) hZ (hyv i)
  have hL : eH.symm.conjRingEquiv (M i) x₀ = eH.symm (M i (eH x₀)) := by
    simp [LinearEquiv.conjRingEquiv]
  rw [hL]
  convert hZ using 1
  rw [hZ', LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.BilinForm.flip_apply, smul_smul, map_mul, map_div₀, hj D]
  congr 1
  exact numeric_product_inequality _ _ _ _ _ _ _ hlam hψne hBne hX hE

end GlobalTheory.LowerCx
end
end

section
section
open NumberField GlobalTheory.CMVal
open scoped ComplexConjugate

namespace GlobalTheory

theorem cmType_trace_im_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (h : I → ℝ) (mu : E), (∀ z : E, ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) = ∑ i, h i * (φ i z).im) →
    ∀ i, 2 * Complex.I * φ i mu = (h i : ℂ) := by
  intro E _ _ _ I _ φ hφ h mu hmu i0
  classical
  let ψ : I ⊕ I → (E →+* ℂ) := fun k => Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)) k
  have hnr : ∀ i, φ i ≠ ComplexEmbedding.conjugate (φ i) := by
    intro i hi
    exact IsTotallyComplex.complexEmbedding_not_isReal (φ i) (ComplexEmbedding.isReal_iff.mpr hi.symm)
  have hinj : Function.Injective ψ := by
    rintro (i | i) (j | j) hij <;> simp only [ψ, Sum.elim_inl, Sum.elim_inr] at hij
    · obtain ⟨k, -, hk⟩ := hφ (φ i)
      rw [(hk i (Or.inl rfl)).trans (hk j (Or.inl hij)).symm]
    · obtain ⟨k, -, hk⟩ := hφ (φ i)
      have e := (hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm
      subst e; exact absurd hij (hnr i)
    · obtain ⟨k, -, hk⟩ := hφ (φ j)
      have e := (hk j (Or.inl rfl)).trans (hk i (Or.inr hij.symm)).symm
      subst e; exact absurd hij.symm (hnr j)
    · obtain ⟨k, -, hk⟩ := hφ (ComplexEmbedding.conjugate (φ i))
      rw [(hk i (Or.inr rfl)).trans (hk j (Or.inr hij)).symm]
  have hsurj : Function.Surjective ψ := by
    intro σ
    obtain ⟨k, hk, -⟩ := hφ σ
    rcases hk with hk | hk
    · exact ⟨Sum.inl k, hk.symm⟩
    · exact ⟨Sum.inr k, hk.symm⟩
  let e : I ⊕ I ≃ (E →+* ℂ) := Equiv.ofBijective ψ ⟨hinj, hsurj⟩
  have htr : ∀ x : E, ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ k, ψ k x := by
    intro x
    have h0 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
    rw [eq_ratCast] at h0
    rw [h0, ← Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ => σ x) (fun f => f x)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])]
    exact (Fintype.sum_equiv e (fun k => ψ k x) (fun σ => σ x) (fun _ => rfl)).symm
  let c : I ⊕ I → ℂ := Sum.elim (fun i => φ i mu - (h i : ℂ) / (2 * Complex.I))
    (fun i => conj (φ i mu) + (h i : ℂ) / (2 * Complex.I))
  have hz : ∀ z, ∑ k, c k * ψ k z = 0 := by
    intro z
    have h2 : ((Algebra.trace ℚ E (mu * z) : ℚ) : ℂ) =
        ∑ i, (h i : ℂ) * ((φ i z - conj (φ i z)) / (2 * Complex.I)) := by
      have h3 := congrArg (fun r : ℝ => (r : ℂ)) (hmu z)
      simp only [Complex.ofReal_ratCast, Complex.ofReal_sum, Complex.ofReal_mul] at h3
      rw [h3]
      simp_rw [Complex.im_eq_sub_conj]
    rw [htr (mu * z)] at h2
    simp only [Fintype.sum_sum_type, ψ, c, Sum.elim_inl, Sum.elim_inr, map_mul,
      ComplexEmbedding.conjugate_coe_eq] at h2 ⊢
    rw [← Finset.sum_add_distrib] at h2 ⊢
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hli : LinearIndependent ℂ (fun k => ((ψ k).toMonoidHom : E → ℂ)) := by
    refine (linearIndependent_monoidHom E ℂ).comp (fun k => (ψ k).toMonoidHom) ?_
    intro a b hab
    apply hinj
    ext x
    exact DFunLike.congr_fun hab x
  have hc := Fintype.linearIndependent_iff.mp hli c (by
    funext z
    simpa [Finset.sum_apply, smul_eq_mul] using hz z) (Sum.inl i0)
  simp only [c, Sum.elim_inl, sub_eq_zero] at hc
  have h2I : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  rw [hc, mul_div_cancel₀ _ h2I]

end GlobalTheory
end

open NumberField GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_trace_imaginary_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (h : I → ℝ) (mu : E), (∀ z : E, ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) = ∑ i, h i * (φ i z).im) →
    ∀ i, 2 * Complex.I * φ i mu = (h i : ℂ) := by
  atlas_forward_decl GlobalTheory.cmType_trace_im_coeff
end

section
open NumberField

namespace GlobalTheory

theorem linearMap_rat_valued_eq_trace : ∀ (E : Type) [Field E] [NumberField E] (g : E →ₗ[ℚ] ℝ), (∀ z, ∃ q : ℚ, g z = q) →
    ∃ mu : E, ∀ z, g z = ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) := by
  intro E _ _ g hg
  choose f hf using hg
  let g' : E →ₗ[ℚ] ℚ :=
    { toFun := f
      map_add' := by
        intro x y
        apply (Rat.cast_injective (α := ℝ))
        rw [Rat.cast_add, ← hf, ← hf, ← hf, map_add]
      map_smul' := by
        intro c x
        apply (Rat.cast_injective (α := ℝ))
        rw [smul_eq_mul, RingHom.id_apply, Rat.cast_mul, ← hf, ← hf, map_smul, Rat.smul_def] }
  have hB := traceForm_nondegenerate ℚ E
  refine ⟨(LinearMap.BilinForm.toDual _ hB).symm g', fun z => ?_⟩
  have h1 : (LinearMap.BilinForm.toDual _ hB ((LinearMap.BilinForm.toDual _ hB).symm g')) z = g' z := by
    rw [LinearEquiv.apply_symm_apply]
  rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h1
  rw [h1]
  exact hf z

end GlobalTheory

alias _root_.GlobalTheory.T.rational_functional_trace_representation := _root_.GlobalTheory.linearMap_rat_valued_eq_trace
end

section
section
open NumberField GlobalTheory.CMVal GlobalTheory.RealMult

namespace GlobalTheory.PolGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eq_zero_of_trace {F : Type} [Field F] [NumberField F] (D : F)
    (h : ∀ a : 𝓞 F, Algebra.trace ℚ F ((a : F) * D) = 0) : D = 0 := by
  by_contra hD
  have halg : IsAlgebraic ℤ D⁻¹ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  have h1 : Algebra.trace ℚ F ((m • D⁻¹) * D) = 0 := h ⟨m • D⁻¹, hint⟩
  have e : (m • D⁻¹) * D = algebraMap ℚ F (m : ℚ) := by
    rw [zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hD]; simp
  rw [e, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
  have h2 : (Module.finrank ℚ F : ℚ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h3 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  exact mul_ne_zero h2 h3 h1

omit [IsCMField E] in

theorem trace_coe_mul (k : maximalRealSubfield E) (w : E) :
    Algebra.trace ℚ E ((k : E) * w) =
      Algebra.trace ℚ (maximalRealSubfield E) (k * Algebra.trace (maximalRealSubfield E) E w) := by
  rw [← Algebra.trace_trace (S := maximalRealSubfield E)]
  congr 1
  rw [← smul_eq_mul k, ← map_smul]
  rfl

theorem genAt_polMod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E) (𝔠 : FracId (maximalRealSubfield E))
    (mu : E) (c1 : maximalRealSubfield E) (Q : E → E → maximalRealSubfield E) (l : ℕ) (c₀ : 𝔠.elt), c1 ≠ 0 →
    IsCMField.complexConj E mu = -mu →
    (∀ (a : OF E), ∀ x ∈ L, ∀ x' ∈ L, Q (algebraMap (OF E) E a * x) x' = (a : maximalRealSubfield E) * Q x x') →
    (∀ x ∈ L, ∀ x' ∈ L, Algebra.trace ℚ E (mu * x * IsCMField.complexConj E x') =
      2 * Algebra.trace ℚ (maximalRealSubfield E) (c1 * Q x x')) →
    (∀ x ∈ L, ∀ x' ∈ L, Q x x' ∈ dualLat 𝔠) →
    (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 (maximalRealSubfield E)) {t | ∃ x ∈ L, ∃ x' ∈ L, t = Q x x'}) →
    (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (maximalRealSubfield E)), n.Coprime l ∧ n • c = t • c₀) →
    mu ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod L)
      ((((c₀ : maximalRealSubfield E) / (2 * c1) : maximalRealSubfield E) : E) * mu) := by
  intro E _ _ _ L 𝔠 mu c1 Q l c₀ h1 h2 h3 h4 h5 h6 h7
  have hL : ∀ (a : OF E), ∀ x ∈ L, algebraMap (OF E) E a * x ∈ L := fun a x hx => by
    rw [← Algebra.smul_def]; exact L.smul_mem a hx
  have hcoe : ∀ a : OF E, algebraMap (OF E) E a = ((a : maximalRealSubfield E) : E) := fun a => rfl
  have hc0 : (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E)) ≠ 0 :=
    𝔠.ne_zero
  have hd0 : dualLat 𝔠 ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ hc0
  have key : ∀ x ∈ L, ∀ x' ∈ L, Algebra.trace (maximalRealSubfield E) E (mu * x * IsCMField.complexConj E x') =
      2 * c1 * Q x x' := by
    intro x hx x' hx'
    rw [← sub_eq_zero]
    apply eq_zero_of_trace
    intro a
    have h := h4 _ (hL a x hx) x' hx'
    rw [h3 a x hx x' hx'] at h
    have e : mu * (algebraMap (OF E) E a * x) * IsCMField.complexConj E x' =
        ((a : maximalRealSubfield E) : E) * (mu * x * IsCMField.complexConj E x') := by
      rw [hcoe]; ring
    rw [e, trace_coe_mul] at h
    have e2 : (a : maximalRealSubfield E) * (2 * c1 * Q x x') =
        c1 * (a * Q x x') + c1 * (a * Q x x') := by ring
    rw [mul_sub, map_sub, h, e2, map_add]; ring
  have key2 : ∀ (k : maximalRealSubfield E), ∀ x ∈ L, ∀ x' ∈ L,
      Algebra.trace ℚ E ((k : E) * mu * x * IsCMField.complexConj E x') =
        Algebra.trace ℚ (maximalRealSubfield E) (k * (2 * c1 * Q x x')) := by
    intro k x hx x' hx'
    rw [← key x hx x' hx', ← trace_coe_mul]
    congr 1; ring
  have h2c : (2 * c1 : maximalRealSubfield E) ≠ 0 := mul_ne_zero two_ne_zero h1
  have hmu : mu ≠ 0 := by
    rintro rfl
    apply hd0
    rw [FractionalIdeal.eq_zero_iff]
    intro t ht
    have h := h6 t ht
    have hle : Submodule.span (𝓞 (maximalRealSubfield E)) {t | ∃ x ∈ L, ∃ x' ∈ L, t = Q x x'} ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, x', hx', rfl⟩
      have := key x hx x' hx'
      rw [zero_mul, zero_mul, map_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left h2c
    exact hle h
  have hfix : ∀ k : maximalRealSubfield E, IsCMField.complexConj E (k : E) = k := fun k =>
    (IsCMField.complexConj E).commutes k
  refine ⟨hmu, ⟨?_, ?_⟩, ?_⟩
  · show IsCMField.complexConj E _ = _
    rw [map_mul, hfix, h2]; ring
  · intro x hx x' hx'
    obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual hc0).1 (h5 x hx x' hx') c₀ c₀.2
    refine ⟨n, ?_⟩
    refine (key2 _ x hx x' hx').trans ?_
    rw [Algebra.traceForm_apply] at hn
    have e : (c₀ : maximalRealSubfield E) / (2 * c1) * (2 * c1 * Q x x') = Q x x' * c₀ := by
      field_simp
    rw [e, ← hn]; simp
  · rintro ν ⟨hν1, hν2⟩
    have hs : IsCMField.complexConj E (ν / mu) = ν / mu := by
      have hν1' : IsCMField.complexConj E ν = -ν := hν1
      rw [map_div₀, hν1', h2, neg_div_neg_eq]
    let s : maximalRealSubfield E := ⟨ν / mu, (IsCMField.complexConj_eq_self_iff E _).1 hs⟩
    have hνs : ν = (s : E) * mu := by
      show ν = ν / mu * mu
      field_simp
    have hmem : 2 * c1 * s ∈ (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E)) := by
      rw [← FractionalIdeal.dual_dual ℤ ℚ (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E))]
      refine (FractionalIdeal.mem_dual hd0).2 ?_
      intro t ht
      have h : ∀ a : OF E, Algebra.trace ℚ (maximalRealSubfield E) (2 * c1 * s * (a * t)) ∈ (algebraMap ℤ ℚ).range := by
        have h := h6 t ht
        clear ht
        induction h using Submodule.span_induction with
        | mem t ht =>
          obtain ⟨x, hx, x', hx', rfl⟩ := ht
          intro a
          obtain ⟨n, hn⟩ := hν2 _ (hL a x hx) x' hx'
          refine ⟨n, ?_⟩
          rw [hνs] at hn
          have h := (key2 s _ (hL a x hx) x' hx').symm.trans hn
          rw [h3 a x hx x' hx'] at h
          have e : 2 * c1 * s * (a * Q x x') = s * (2 * c1 * (a * Q x x')) := by ring
          rw [e, h]; simp
        | zero => intro a; simp
        | add t u _ _ ht hu =>
          intro a
          rw [mul_add, mul_add, map_add]
          exact add_mem (ht a) (hu a)
        | smul b t _ ht =>
          intro a
          have e : (a : maximalRealSubfield E) * b • t = ((a * b : OF E) : maximalRealSubfield E) * t := by
            rw [Algebra.smul_def, ← mul_assoc]
            congr 1
          rw [e]; exact ht _
      have := h 1
      rw [Algebra.traceForm_apply]
      simpa using this
    obtain ⟨n, t, hn, hnt⟩ := h7 ⟨2 * c1 * s, hmem⟩
    refine ⟨n, hn, t, ?_⟩
    have e : (n : maximalRealSubfield E) * (2 * c1 * s) = (t : maximalRealSubfield E) * c₀ := by
      have := congrArg Subtype.val hnt
      simpa [nsmul_eq_mul, Algebra.smul_def] using this
    have e2 : (n : maximalRealSubfield E) * s = (t : maximalRealSubfield E) * (c₀ / (2 * c1)) := by
      rw [mul_div_assoc', ← e]; field_simp
    have e3 := congrArg (fun z : maximalRealSubfield E => (z : E)) e2
    simp only [Subfield.coe_mul, SubringClass.coe_natCast] at e3
    rw [hcoe, hνs, ← mul_assoc, ← mul_assoc, e3]

end GlobalTheory.PolGen
end

open NumberField GlobalTheory.CMVal GlobalTheory.RealMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_hermitian_trace_form_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E) (𝔠 : FracId (maximalRealSubfield E))
    (mu : E) (c1 : maximalRealSubfield E) (Q : E → E → maximalRealSubfield E) (l : ℕ) (c₀ : 𝔠.elt), c1 ≠ 0 →
    IsCMField.complexConj E mu = -mu →
    (∀ (a : OF E), ∀ x ∈ L, ∀ x' ∈ L, Q (algebraMap (OF E) E a * x) x' = (a : maximalRealSubfield E) * Q x x') →
    (∀ x ∈ L, ∀ x' ∈ L, Algebra.trace ℚ E (mu * x * IsCMField.complexConj E x') =
      2 * Algebra.trace ℚ (maximalRealSubfield E) (c1 * Q x x')) →
    (∀ x ∈ L, ∀ x' ∈ L, Q x x' ∈ dualLat 𝔠) →
    (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 (maximalRealSubfield E)) {t | ∃ x ∈ L, ∃ x' ∈ L, t = Q x x'}) →
    (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (maximalRealSubfield E)), n.Coprime l ∧ n • c = t • c₀) →
    mu ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod L)
      ((((c₀ : maximalRealSubfield E) / (2 * c1) : maximalRealSubfield E) : E) * mu) := by
  atlas_forward_decl GlobalTheory.PolGen.genAt_polMod
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.PolScale

open GlobalTheory.AbDual

theorem nat_mul_polForm_eq_of_smul_eq (H : GlobalTheory.Published.AbelianDeRham) {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (c c₀ : 𝔠.elt) (n : ℕ) (t : 𝓞 F) (e : (n : 𝓞 F) • c = t • c₀)
    (ψ ψ₀ : LinearMap.BilinForm R (HdR X.A)) (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ)
    (hψ₀ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c₀) ψ₀) :
    ∀ x y, (n : R) * ψ x y = ψ₀ x (act (dp0 R) (𝟙 _) X.rm t y) := by
  have C := cupSquare_of_free H.1 X.ab X.dim
  have hD : ∀ d : 𝔠.elt, (X.diag d).IsLB := fun d ↦ pull_isLB (X.isLB d) _
  obtain ⟨φ, hφ⟩ := exists_corrForm H.1 X c
  obtain ⟨φ₀, hφ₀⟩ := exists_corrForm H.1 X c₀
  obtain ⟨φn, hφn, kn⟩ := exists_corrForm_smul X (n : 𝓞 F) c hφ
  obtain ⟨φt, hφt, kt⟩ := exists_corrForm_smul X t c₀ hφ₀
  rw [e] at hφn
  have u := Published.AbelianDualCrystal.polForm_unique C (hD _) (isPolForm_diag X _ hφn) (isPolForm_diag X _ hφt)
  have u₁ := Published.AbelianDualCrystal.polForm_unique C (hD c) hψ (isPolForm_diag X c hφ)
  have u₂ := Published.AbelianDualCrystal.polForm_unique C (hD c₀) hψ₀ (isPolForm_diag X c₀ hφ₀)
  intro x y
  have v := LinearMap.congr_fun (LinearMap.congr_fun u x) y
  rw [u₁, u₂]
  simp only [LinearMap.sub_apply, LinearMap.flip_apply, kn, kt, act_natCast, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at v ⊢
  have a₁ := corrForm_antisymm H.1 X _ hφt y x
  have a₂ := corrForm_antisymm H.1 X c₀ hφ₀ (act (dp0 R) (𝟙 _) X.rm t y) x
  rw [kt, kt] at a₁
  linear_combination v + a₂ - a₁

end GlobalTheory.RealMult.PolScale

namespace GlobalTheory.RatioForm

set_option maxHeartbeats 1000000 in

theorem form_ratio : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt)
      (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) (2 • ψ₀) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) →
      (∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x)) →
    ∀ (D : R) (cv : ℚ), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D)) = (cv : WithTop ℚ) → (cv : ℝ) = c_vp 𝔣 l →
    ∀ (e' f' : I → (Fin n → R)), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) e' f' →
      (∀ i, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D))) →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC → ∀ (ψ : LinearMap.BilinForm ℂ (HdR X.A)), IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ →
    ∀ (yv ev : I → HdR X.A) (w : I → ℂ), (∀ i, U.IsCMVec i (yv i) (w i)) →
      (∀ i, m.Corr (eH.symm (f' i)) (yv i)) → (∀ i, m.Corr (eH.symm (e' i)) (ev i)) →
      (∀ i, ((e i (hL.toLie X₀.rm (eH.symm (f' i))) : R) : ℂ) = a i * w i) →
    ∃ ξ : E, GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y)) ξ ∧
      ∀ i, U.h i ≠ 0 ∧ ψ (ev i) (yv i) * (2 * Complex.I * φ i ξ) = (U.h i : ℂ) * ((ψ₀ (eH.symm (e' i)) (eH.symm (f' i)) : R) : ℂ) := by
  intro hPer hAdR hAdC hPM E _ _ _ _ I _ d φ hFD 𝔣 hB l _ Q hQ hQl y hy lam 𝔠 R _ hPR X₀ X U p cm hPB hcm hα j hj φK hφK e a hea hL n eH c₀ ψ₀ hc₀ hgen hpol hCM hdual D cv hD hcv e' f' hGens hval m hBC ψ hψ yv ev w hCMv hf he hw
  classical
  have hφ : IsCMType φ := hFD.2.2.2.2.2.2.1
  have hcQ : condQ 𝔣 Q ≠ ⊥ := by
    unfold condQ
    refine mul_ne_zero hB.1 ?_
    rw [Finset.prod_ne_zero_iff]
    intro q _
    exact q.ne_bot
  have hUc : ((U.c : FR E)) ≠ 0 := by
    intro h0
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace (FR E)))
    have hw : w.IsReal := NumberField.IsTotallyReal.isReal w
    have := U.pos (NumberField.InfinitePlace.embedding_of_isReal hw)
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨eR, heR⟩ := GlobalTheory.CMTypeRestrict.exists_equiv_realEmbeddings E I φ hφ U.e
  have hact : ∀ (a : 𝓞 (FR E)) w, U.u.ex (fun j ↦ (eR j (a : FR E) : ℂ) * w j) = U.u.ex w ≫ X.rm.act a := by
    intro a w
    have := U.act a w
    simpa [heR] using this
  obtain ⟨χ, hχ⟩ := U.ah
  obtain ⟨P, hPanti, hPadd, hPsmul, hPim, hPdual, hPspan⟩ :=
    GlobalTheory.T.diagonal_appell_humbert_real_mult (FR E) 𝔠 X U.c U.pos U.u eR hact (fun j ↦ U.h (U.e j)) χ hχ

  let co : E → (Fin (Module.finrank ℚ (FR E)) → ℂ) := fun x j ↦ φ (U.e j) x
  have hcoΛ : ∀ x ∈ lattice (condQ 𝔣 Q) y, co x ∈ U.u.Λ := fun x hx ↦
    (U.lat _).2 ⟨x, hx, by funext j; simp [co, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  have hΛco : ∀ w ∈ U.u.Λ, ∃ x ∈ lattice (condQ 𝔣 Q) y, w = co x := fun w hw ↦ by
    obtain ⟨x, hx, rfl⟩ := (U.lat w).1 hw
    exact ⟨x, hx, by funext j; simp [co, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  let toΛ : E → U.u.Λ := fun x ↦ if hx : co x ∈ U.u.Λ then ⟨co x, hx⟩ else 0
  have htoΛ : ∀ x ∈ lattice (condQ 𝔣 Q) y, (toΛ x : Fin (Module.finrank ℚ (FR E)) → ℂ) = co x := fun x hx ↦ by
    simp [toΛ, hcoΛ x hx]
  let Qf : E → E → FR E := fun x x' ↦ P (toΛ x) (toΛ x')

  let fR : E → ℝ := fun z ↦ ∑ i, U.h i * (φ i z).im
  have hsum : ∀ x x' : E, (∑ j, ((U.h (U.e j) : ℝ) : ℂ) * (co x j * starRingEnd ℂ (co x' j))).im =
      fR (x * IsCMField.complexConj E x') := by
    intro x x'
    simp only [fR, co, Complex.im_sum, map_mul, IsCMField.complexEmbedding_complexConj, Complex.im_ofReal_mul]
    exact Equiv.sum_comp U.e (fun i ↦ U.h i * (φ i x * starRingEnd ℂ (φ i x')).im)
  have hfrel : ∀ x ∈ lattice (condQ 𝔣 Q) y, ∀ x' ∈ lattice (condQ 𝔣 Q) y, fR (x * IsCMField.complexConj E x') =
      2 * ((Algebra.trace ℚ (FR E) ((U.c : FR E) * Qf x x') : ℚ) : ℝ) := by
    intro x hx x' hx'
    rw [← hsum, ← hPim (toΛ x) (toΛ x'), htoΛ x hx, htoΛ x' hx']

  let gR : E →ₗ[ℚ] ℝ :=
    { toFun := fR
      map_add' := fun z z' ↦ by
        simp only [fR, map_add, Complex.add_im, mul_add, Finset.sum_add_distrib]
      map_smul' := fun q z ↦ by
        simp only [fR, RingHom.id_apply]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Rat.smul_def, map_mul, map_ratCast, ← Complex.ofReal_ratCast, Complex.im_ofReal_mul, Rat.smul_def]
        ring }
  have hgR : ∀ z, gR z = fR z := fun z ↦ rfl
  obtain ⟨N, hN0, hNL, -⟩ := GlobalTheory.CMVal.LatBound.lattice_between E (condQ 𝔣 Q) hcQ y
  have hrat : ∀ z, ∃ q : ℚ, gR z = q := by
    intro z
    obtain ⟨b, k, hk, hb⟩ : ∃ (b : 𝓞 E) (k : ℤ), k ≠ 0 ∧ (k : E) * z = algebraMap (𝓞 E) E b := by
      obtain ⟨k, hk, hi⟩ := IsAlgebraic.exists_integral_multiple
        ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z))
      exact ⟨⟨k • z, hi⟩, k, hk, by simp [zsmul_eq_mul]⟩
    have hx : (N : E) * algebraMap (𝓞 E) E b ∈ lattice (condQ 𝔣 Q) y := hNL b
    have hx' : (N : E) * algebraMap (𝓞 E) E 1 ∈ lattice (condQ 𝔣 Q) y := hNL 1
    have e1 := hfrel _ hx _ hx'
    have e2 : (N : E) * algebraMap (𝓞 E) E b * IsCMField.complexConj E ((N : E) * algebraMap (𝓞 E) E 1) =
        (((N : ℚ) * N * k : ℚ) : E) * z := by
      rw [map_one, _root_.mul_one, map_natCast]; push_cast; rw [← hb]; ring
    rw [e2] at e1
    have e3 : gR ((((N : ℚ) * N * k : ℚ) : E) * z) = (((N : ℚ) * N * k : ℚ) : ℝ) * gR z := by
      rw [← Rat.smul_def, map_smul, Rat.smul_def]
    refine ⟨2 * Algebra.trace ℚ (FR E) ((U.c : FR E) * Qf ((N : E) * algebraMap (𝓞 E) E b) ((N : E) * algebraMap (𝓞 E) E 1)) /
      ((N : ℚ) * N * k), ?_⟩
    have hne : (((N : ℚ) * N * k : ℚ) : ℝ) ≠ 0 := by
      have : ((N : ℚ) * N * k : ℚ) ≠ 0 := by
        have : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
        have : (k : ℚ) ≠ 0 := by exact_mod_cast hk
        positivity
      exact_mod_cast this
    rw [← hgR, e3] at e1
    rw [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    exact eq_div_of_mul_eq hne (by rw [mul_comm]; exact e1)
  obtain ⟨mu, hmu⟩ := GlobalTheory.T.rational_functional_trace_representation E gR hrat
  have hmu' : ∀ z : E, ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) = ∑ i, U.h i * (φ i z).im := fun z ↦ (hmu z).symm
  have hmuh := GlobalTheory.T.cm_type_trace_imaginary_part E I φ hφ U.h mu hmu'

  have hIne : Nonempty I := by
    have : 2 ≤ Fintype.card I := hFD.2.2.2.2.2.1
    exact Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hIne
  have hbar : IsCMField.complexConj E mu = -mu := by
    apply (φ i₀).injective
    have h1 := hmuh i₀
    rw [IsCMField.complexEmbedding_complexConj, map_neg]
    have h2 : starRingEnd ℂ (2 * Complex.I * φ i₀ mu) = starRingEnd ℂ (U.h i₀ : ℂ) := by rw [h1]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat] at h2
    have h3 : (2 : ℂ) * Complex.I ≠ 0 := by simp
    apply mul_left_cancel₀ h3
    linear_combination -h2 + h1
  have hQa : ∀ (a : OF E), ∀ x ∈ lattice (condQ 𝔣 Q) y, ∀ x' ∈ lattice (condQ 𝔣 Q) y,
      Qf (algebraMap (OF E) E a * x) x' = (a : FR E) * Qf x x' := by
    intro a x hx x' hx'
    have hax : algebraMap (OF E) E a * x ∈ lattice (condQ 𝔣 Q) y := by
      have : algebraMap (OF E) E a ∈ orderC (condQ 𝔣 Q) := GlobalTheory.CMVal.algebraMap_mem_orderC _ a
      exact GlobalTheory.CMVal.mul_mem_lattice this hx
    refine hPsmul a (toΛ x) (toΛ x') (toΛ (algebraMap (OF E) E a * x)) ?_
    rw [htoΛ _ hax, htoΛ _ hx]
    funext k
    simp only [co, map_mul, heR]
    rfl
  have htr : ∀ x ∈ lattice (condQ 𝔣 Q) y, ∀ x' ∈ lattice (condQ 𝔣 Q) y, Algebra.trace ℚ E (mu * x * IsCMField.complexConj E x') =
      2 * Algebra.trace ℚ (FR E) ((U.c : FR E) * Qf x x') := by
    intro x hx x' hx'
    have h1 := hmu (x * IsCMField.complexConj E x')
    rw [hgR, hfrel x hx x' hx', ← _root_.mul_assoc] at h1
    exact_mod_cast h1.symm
  have hdl : ∀ x ∈ lattice (condQ 𝔣 Q) y, ∀ x' ∈ lattice (condQ 𝔣 Q) y, Qf x x' ∈ dualLat 𝔠 := fun x _ x' _ ↦ hPdual _ _
  have hsp : ∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 (FR E)) {t | ∃ x ∈ lattice (condQ 𝔣 Q) y, ∃ x' ∈ lattice (condQ 𝔣 Q) y, t = Qf x x'} := by
    intro t ht
    refine Submodule.span_mono ?_ (hPspan t ht)
    rintro s ⟨l₁, l₂, rfl⟩
    obtain ⟨x, hx, hx1⟩ := hΛco l₁ l₁.2
    obtain ⟨x', hx', hx2⟩ := hΛco l₂ l₂.2
    refine ⟨x, hx, x', hx', ?_⟩
    have e1 : toΛ x = l₁ := Subtype.ext (by rw [htoΛ x hx, ← hx1])
    have e2 : toΛ x' = l₂ := Subtype.ext (by rw [htoΛ x' hx', ← hx2])
    simp only [Qf, e1, e2]
  obtain ⟨hmu0, hGen⟩ := GlobalTheory.T.cm_hermitian_trace_form_integral E (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y) 𝔠 mu (U.c : FR E) Qf l c₀ hUc hbar
    hQa htr hdl hsp hgen

  obtain ⟨n₁, t, hn₁, het⟩ := GlobalTheory.RealMult.PolScale.exists_nat_smul_eq c₀ U.c hUc
  obtain ⟨ψc, hψc, hcorr⟩ := GlobalTheory.LowerCx.polForm_bc' (algebraMap R ℂ) hPB m c₀ hpol
  have hsc := GlobalTheory.RealMult.PolScale.nat_mul_polForm_eq_of_smul_eq hAdR X c₀ U.c n₁ t het ψc ψ hψc hψ
  have hty : ∀ i, act (dp0 ℂ) (𝟙 _) X.rm t (yv i) = φ i ((t : FR E) : E) • yv i := by
    intro i
    haveI := X.rm.hom t
    rw [act_apply]
    exact (hCMv i).1 ((t : FR E) : E) (X.rm.act t) (fun w' ↦ U.act t w')
  have hkey : ∀ i, φ i ((t : FR E) : E) * ψ (ev i) (yv i) =
      (n₁ : ℂ) * (2 * ((ψ₀ (eH.symm (e' i)) (eH.symm (f' i)) : R) : ℂ)) := by
    intro i
    have h1 := hsc (ev i) (yv i)
    rw [hty i, map_smul, smul_eq_mul, hcorr _ _ _ _ (he i) (hf i)] at h1
    rw [← h1, two_smul, LinearMap.add_apply, LinearMap.add_apply, map_add, two_mul]
    rfl
  have hcF : ((c₀ : FR E)) * (n₁ : FR E) = ((t : FR E)) * (U.c : FR E) := by
    have := congrArg (fun z : 𝔠.elt ↦ (z : FR E)) het
    simp only [Submodule.coe_smul, Algebra.smul_def, map_natCast] at this
    rw [mul_comm]; exact this
  refine ⟨(((c₀ : FR E) / (2 * (U.c : FR E)) : FR E) : E) * mu, hGen, fun i ↦ ⟨?_, ?_⟩⟩
  · intro h0
    have h1 := hmuh i
    rw [h0, Complex.ofReal_zero] at h1
    have h2 : φ i mu = 0 := by
      have h3 : (2 : ℂ) * Complex.I ≠ 0 := by simp
      exact (mul_eq_zero.1 h1).resolve_left h3
    exact hmu0 ((map_eq_zero (φ i)).1 h2)
  · have hc : φ i ((c₀ : FR E) : E) * n₁ = φ i ((t : FR E) : E) * φ i ((U.c : FR E) : E) := by
      have := congrArg (fun z : FR E ↦ φ i (z : E)) hcF
      simpa using this
    have hC1 : φ i ((U.c : FR E) : E) ≠ 0 := by
      intro h0
      exact hUc (by simpa using h0)
    have hn₁' : (n₁ : ℂ) ≠ 0 := by exact_mod_cast hn₁
    have hk := hkey i
    have hm := hmuh i
    have hdiv : φ i ((((c₀ : FR E) / (2 * (U.c : FR E)) : FR E) : E)) =
        φ i ((c₀ : FR E) : E) / (2 * φ i ((U.c : FR E) : E)) := by
      change (φ i).comp (algebraMap (FR E) E) (_ / (2 * _)) = (φ i).comp (algebraMap (FR E) E) _ / (2 * (φ i).comp (algebraMap (FR E) E) _)
      rw [map_div₀, map_mul, map_ofNat]
    rw [map_mul, hdiv]
    set A := ψ (ev i) (yv i)
    set B := ((ψ₀ (eH.symm (e' i)) (eH.symm (f' i)) : R) : ℂ)
    have e1 : A * (2 * Complex.I * (φ i ((c₀ : FR E) : E) / (2 * φ i ((U.c : FR E) : E)) * φ i mu)) =
        A * φ i ((c₀ : FR E) : E) * (2 * Complex.I * φ i mu) / (2 * φ i ((U.c : FR E) : E)) := by ring
    rw [e1, hm, div_eq_iff (mul_ne_zero two_ne_zero hC1)]
    apply mul_left_cancel₀ hn₁'
    linear_combination (A * (U.h i : ℂ)) * hc + (φ i ((U.c : FR E) : E) * (U.h i : ℂ)) * hk

end GlobalTheory.RatioForm
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.auxiliary_set_field_data_congruence : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt)
      (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) (2 • ψ₀) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) →
      (∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x)) →
    ∀ (D : R) (cv : ℚ), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D)) = (cv : WithTop ℚ) → (cv : ℝ) = c_vp 𝔣 l →
    ∀ (e' f' : I → (Fin n → R)), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) e' f' →
      (∀ i, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D))) →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC → ∀ (ψ : LinearMap.BilinForm ℂ (HdR X.A)), IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ →
    ∀ (yv ev : I → HdR X.A) (w : I → ℂ), (∀ i, U.IsCMVec i (yv i) (w i)) →
      (∀ i, m.Corr (eH.symm (f' i)) (yv i)) → (∀ i, m.Corr (eH.symm (e' i)) (ev i)) →
      (∀ i, ((e i (hL.toLie X₀.rm (eH.symm (f' i))) : R) : ℂ) = a i * w i) →
    ∃ ξ : E, GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y)) ξ ∧
      ∀ i, U.h i ≠ 0 ∧ ψ (ev i) (yv i) * (2 * Complex.I * φ i ξ) = (U.h i : ℂ) * ((ψ₀ (eH.symm (e' i)) (eH.symm (f' i)) : R) : ℂ) := by
  atlas_forward_decl GlobalTheory.RatioForm.form_ratio
end
end
