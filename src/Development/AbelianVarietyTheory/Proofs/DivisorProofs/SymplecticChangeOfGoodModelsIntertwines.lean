module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenLatticePointAtPlaceLocalIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProduStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedLeviLowerUnipotentWeylStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalWeilOperatorLeviBlockStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfSchroedingerTranslatesThetaSumZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentHasRationalWeilOperatorQuadraticChStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourierStatement

@[expose] public section

noncomputable section

namespace GlobalTheory.RatWeilOp

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F : Type} [Field F] [NumberField F]

theorem hasOp_of_symplectic (hF : IsTotallyReal F) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (ha : aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0) : HasOp ψ a :=
  GlobalTheory.T.symplecticGroup_generated_levi_lowerUnipotent_weyl F κ (HasOp ψ) (fun _ _ => HasOp.mul) (GlobalTheory.T.hasRationalWeilOperator_leviBlock F ψ κ) (GlobalTheory.T.lowerUnipotent_hasRationalWeilOperator_quadraticChar F ψ hψ κ) (GlobalTheory.T.weylElement_hasRationalWeilOperator_adelicFourier F hF ψ hψ κ) a ha

section Pure

variable {κ : Type} [Fintype κ]

theorem pure_mem (f : SInf F κ) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F κ :=
  Submodule.subset_span ⟨f, fun y => ∏ᶠ v, φ v fun i => evalV F v (y i),
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ.1 hφ.2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ.1 hφ.2⟩, rfl⟩

theorem schA_le {N : Submodule ℂ ((κ → AF F) → ℂ)} (h : ∀ f φ, IsFam φ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N) : schA F κ ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  replace hg := GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F _ g hg
  induction hg using Submodule.span_induction with
  | zero => rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; exact N.zero_mem
  | add a b _ _ ha hb =>
    rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; exact N.add_mem ha hb
  | smul c a _ ha =>
    rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; exact N.smul_mem c ha
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    exact h f φ ⟨hφ, hs⟩

def schrL {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) :
    ((κ → R) → ℂ) →ₗ[ℂ] (κ → R) → ℂ where
  toFun := schr ψ w
  map_add' φ φ' := funext fun x => by simp only [schr, Pi.add_apply]; ring
  map_smul' a φ := funext fun x => by simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

variable {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F} {e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ} {c : ℂ}
  {ei : SInf F κ →L[ℂ] SInf F κ} {ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ}

theorem IsOp.maps (h : IsOp ψ a e c ei ev) : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ := fun _ hΦ =>
  schA_le (N := (schA F κ).comap e) (fun f φ hφ => by
    rw [Submodule.mem_comap, (h.2.2.2.2.2 f φ hφ).1]
    exact pure_mem _ (h.isFam hφ)) hΦ

theorem IsOp.Heisenberg₂ (h : IsOp ψ a e c ei ev) (w : (κ → AF F) × (κ → AF F)) :
    ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (act (a.map (algebraMap F (AF F))) w) (e Φ) := fun _ hΦ =>
  schA_le (N := LinearMap.eqLocus (e ∘ₗ schrL ψ w) (schrL ψ (act (a.map (algebraMap F (AF F))) w) ∘ₗ e))
    (fun f φ hφ => (h.2.2.2.2.2 f φ hφ).2.1 w) hΦ

theorem IsOp.theta (h : IsOp ψ a e c ei ev) : ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = c * thetaSum F Φ := fun _ hΦ =>
  (schA_le (N := {
      carrier := {Φ | Φ ∈ schA F κ ∧ thetaSum F (e Φ) = c * thetaSum F Φ}
      zero_mem' := ⟨zero_mem _, by simp [thetaSum]⟩
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by
        rw [map_add (f := _), thetaSum_add F (h.maps _ hx.1) (h.maps _ hy.1), thetaSum_add F hx.1 hy.1, hx.2, hy.2, mul_add]⟩
      smul_mem' := fun r x hx => ⟨Submodule.smul_mem _ r hx.1, by
        rw [map_smul, thetaSum_smul, thetaSum_smul, hx.2, mul_left_comm]⟩ })
    (fun f φ hφ => ⟨pure_mem f hφ, (h.2.2.2.2.2 f φ hφ).2.2⟩) hΦ).2

theorem IsOp.bijOn (hψ : IsStd ψ) (h : IsOp ψ a e c ei ev) : Set.BijOn e (schA F κ : Set _) (schA F κ : Set _) := by
  classical
  refine ⟨h.maps, fun Φ hΦ Φ' hΦ' he => ?_, ?_⟩
  · have hd : Φ - Φ' ∈ schA F κ := sub_mem hΦ hΦ'
    refine sub_eq_zero.1 (GlobalTheory.T.eq_zero_of_schroedingerTranslates_thetaSum_zero F ψ hψ κ _ hd fun w => ?_)
    have h1 := h.theta _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ w _ hd)
    rw [h.Heisenberg₂ w _ hd, map_sub, he, sub_self, show schr ψ _ (0 : (κ → AF F) → ℂ) = 0 from (schrL ψ _).map_zero] at h1
    exact (mul_eq_zero.1 (h1.symm.trans (by simp [thetaSum]))).resolve_left h.1
  · refine schA_le (N := (schA F κ).map e) fun g φ' hφ' => ?_
    obtain ⟨f, rfl⟩ := h.2.1 g
    have key : ∀ v, ∃ p ∈ SB (κ → Fv F v), ev v p = φ' v ∧ (φ' v = ind κ v → ev v (ind κ v) = ind κ v → p = ind κ v) := by
      intro v
      by_cases hv : φ' v = ind κ v ∧ ev v (ind κ v) = ind κ v
      · exact ⟨ind κ v, hv.1 ▸ hφ'.1 v, hv.2.trans hv.1.symm, fun _ _ => rfl⟩
      · obtain ⟨p, hp, hp'⟩ := (h.2.2.1 v).surjOn (hφ'.1 v)
        exact ⟨p, hp, hp', fun h1 h2 => absurd ⟨h1, h2⟩ hv⟩
    choose φ h1 h2 h3 using key
    have hφ : IsFam φ := ⟨h1, by filter_upwards [hφ'.2, h.2.2.2.2.1] with v p q using h3 v p q⟩
    exact ⟨_, pure_mem f hφ, by rw [(h.2.2.2.2.2 f φ hφ).1]; simp only [h2]⟩

end Pure

section Vac

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

end Vac

end GlobalTheory.RatWeilOp

end
