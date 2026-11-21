import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepFamilyBoundedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeightDataIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanning
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStableRationalLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSignatureDataSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBasisFreeModulePlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCharSpreadCommutesWithRestriction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvalueCoprimeConjugation
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaActsOnTameRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTameQuotientJointPowersTameGenerator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityCongrUnitAtPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharEqOfTameRepCongr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverRealSubfieldSplitStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_lattice_finitely_generated_spanning : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    (BsupT D T S i j b).FG ∧
      Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤ := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.bsupT_fg_span_all | exact GlobalTheory.HeightCounting.FormsStep.bsupT_fg_span_all | (intros; apply GlobalTheory.HeightCounting.FormsStep.bsupT_fg_span_all <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCentralGroupAlgebraIdempotent_universal : ∀ D : D7, EIdem D := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.eIdem_all | exact GlobalTheory.HeightCounting.FormsStep.eIdem_all | (intros; apply GlobalTheory.HeightCounting.FormsStep.eIdem_all <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem cHkT_eq_of_isFrob : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool) (P : PlE D.host), P ∉ T.S0 i →
    ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    cHkT D T i b P = Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom
      (if b then T.delta i σ else (T.delta i σ)⁻¹) := by
  intro D T i b P hP σ hσ
  have hA := D.nd.plOm.2 P
  have key : ∀ τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) τ →
      T.delta i τ = T.delta i σ := by
    intro τ hτ
    have hmem := inv_mul_mem_Ine_of_isFrob hσ hτ
    have h1 : T.delta i (σ⁻¹ * τ) = 1 := by
      by_contra hne
      exact hP (T.primes_subset_exceptional i ((T.delta_ram i P _ hA).1 ⟨_, hmem, hne⟩))
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  unfold cHkT
  rw [dif_pos ⟨σ, hσ⟩, key _ (Exists.choose_spec (⟨σ, hσ⟩ : ∃ τ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om,
    IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) τ))]

end GlobalTheory.HeightCounting.FormsStep
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeComparisonUnitAtFrobenius_eq_delta : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool) (P : PlE D.host), P ∉ T.S0 i →
    ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    cHkT D T i b P = Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom
      (if b then T.delta i σ else (T.delta i σ)⁻¹) := by
  atlas_forward_decl GlobalTheory.HeightCounting.FormsStep.cHkT_eq_of_isFrob
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem formsExport_eq : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (hE : IsEmpty D.nd.Loc)
    (hfg : ∀ i j b, (BsupT D T S i j b).FG) (hst : HkStab D T S In) (sd : SigData D T) (rho : RhoFam D T)
    (hrho : ∀ i σ b, Continuous fun g =>
      ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) (he : EIdem D)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T)
    (i : (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
    ∃ e : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b ≃ₗ[FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)]
        Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b,
      (∀ x, x ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ↔
        e x ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b) ∧
      (∀ g x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).actG i j b g x) =
        actG ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
          (In.rho j h1 h2) (In.chi j h1 h2) g (e x)) ∧
      ∀ k P x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).hkF i j b k P x) =
        algebraMap ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)
            (FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)) (cHkT D T i b P : T.O i) ^ k •
          GlobalTheory.HeightCounting.hkF D ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
            (In.hL j) (In.hs j h1 h2) k P (e x) := by
  intro D S In T hE hfg hst sd rho hrho he Pq wt i j b h1 h2
  let i' : T.Tw := i
  have hW : WKr D S j = (S.A j).WK := WKr_of D S h1 h2
  let e : (KT D T i' b ⊗[S.Ks] ↥(WKr D S j)) ≃ₗ[KT D T i' b] (KT D T i' b ⊗[S.Ks] ↥(S.A j).WK) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (KT D T i' b) (KT D T i' b)) (LinearEquiv.ofEq _ _ hW)
  have he1 : ∀ (a : KT D T i' b) (w : ↥(WKr D S j)), e (a ⊗ₜ[S.Ks] w) = a ⊗ₜ[S.Ks] (LinearEquiv.ofEq _ _ hW w) :=
    fun a w => rfl
  have hbc : ∀ (f : Module.End S.Ks ↥(WKr D S j)) (f' : Module.End S.Ks ↥(S.A j).WK),
      (∀ w, ((f w : ↥(WKr D S j)) : S.WL j) = (f' (LinearEquiv.ofEq _ _ hW w) : S.WL j)) →
      ∀ y, e (Module.End.baseChangeHom S.Ks (KT D T i' b) _ f y) = Module.End.baseChangeHom S.Ks (KT D T i' b) _ f' (e y) := by
    intro f f' hf y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a w =>
      show a ⊗ₜ[S.Ks] (LinearEquiv.ofEq _ _ hW (f w)) = a ⊗ₜ[S.Ks] (f' (LinearEquiv.ofEq _ _ hW w))
      exact congrArg (a ⊗ₜ[S.Ks] ·) (Subtype.ext (hf w))
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  have hc : ∀ g', cR D S In.chi j g' = chiL S j (In.chi j h1 h2) g' := fun g' => dif_pos ⟨h1, h2⟩
  have hsm : ∀ (r : T.O i') (y : KT D T i' b ⊗[S.Ks] ↥(WKr D S j)),
      e ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • y) =
        (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • e y := fun r y => e.map_smul _ y
  have hsm' : ∀ (r : T.O i') (y : KT D T i' b ⊗[S.Ks] ↥(S.A j).WK),
      e.symm ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • y) =
        (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) r) • e.symm y := fun r y => e.symm.map_smul _ y
  refine ⟨e, ?_, ?_, ?_⟩
  · let eO : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b →ₗ[(T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i] Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b :=
      { toFun := fun y => e y, map_add' := fun y z => e.map_add y z, map_smul' := fun r y => hsm r y }
    let eO' : Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b →ₗ[(T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i] (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b :=
      { toFun := fun y => e.symm y, map_add' := fun y z => e.symm.map_add y z, map_smul' := fun r y => hsm' r y }
    have hle1 : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ≤ (Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b).comap eO := by
      show BsupT D T S i' j b ≤ _
      refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hw, rfl⟩
      exact (Submodule.subset_span ⟨LinearEquiv.ofEq _ _ hW w, hw, rfl⟩ : _ ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b)
    have hle2 : Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b ≤ ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b).comap eO' := by
      refine Submodule.span_le.mpr ?_
      rintro y ⟨w, hw, rfl⟩
      exact (Submodule.subset_span ⟨(LinearEquiv.ofEq _ _ hW).symm w, hw, rfl⟩ : _ ∈ BsupT D T S i' j b)
    intro x
    refine ⟨fun hx => hle1 hx, fun hx => ?_⟩
    have h := hle2 hx
    rw [Submodule.mem_comap] at h
    change e.symm (e x) ∈ _ at h
    exact Eq.mp (congrArg (fun (z : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b) => z ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b) (e.symm_apply_apply x)) h
  · intro g x
    change e ((actEndT D T S In.rho In.chi i' j b (S.eG.symm g)) x) =
      (actEnd ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b (In.rho j h1 h2) (In.chi j h1 h2) (S.eG.symm g)) (e x)
    change e ((readK D T i' b (cR D S In.chi j (S.eG.symm g)))⁻¹ •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(WKr D S j) (rhoR D S In.rho j (S.eG.symm g)) x) =
      (readK D T i' b (chiL S j (In.chi j h1 h2) (S.eG.symm g)))⁻¹ •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(S.A j).WK (rhoKG S j (In.rho j h1 h2) (S.eG.symm g)) (e x)
    rw [LinearEquiv.map_smul, hbc _ (rhoKG S j (In.rho j h1 h2) (S.eG.symm g)) (fun w => rfl) x, hc]
  · intro k P x
    change e ((show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) (cHkT D T i' b P : T.O i')) ^ k •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(WKr D S j) (hLr D S In j k P) x) =
      (show KT D T i' b from algebraMap (T.O i') (FractionRing (T.O i')) (cHkT D T i' b P : T.O i')) ^ k •
        Module.End.baseChangeHom S.Ks (KT D T i' b) ↥(S.A j).WK
          (((In.hL j k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK)
            fun x hx => In.hs j h1 h2 k P x hx) (e x)
    rw [LinearEquiv.map_smul, hbc _ _ ?_ x]
    intro w
    rw [hLr, dif_pos ⟨h1, h2⟩]
    rfl

end GlobalTheory.HeightCounting.FormsStep
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (hE : IsEmpty D.nd.Loc)
    (hfg : ∀ i j b, (BsupT D T S i j b).FG) (hst : HkStab D T S In) (sd : SigData D T) (rho : RhoFam D T)
    (hrho : ∀ i σ b, Continuous fun g =>
      ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) (he : EIdem D)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (wt : WtData D T)
    (i : (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
    ∃ e : (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Fm i j b ≃ₗ[FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)]
        Fm ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b,
      (∀ x, x ∈ (mkEx D T S In hE hfg hst sd rho hrho he Pq wt).Bsup i j b ↔
        e x ∈ Bsup ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b) ∧
      (∀ g x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).actG i j b g x) =
        actG ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
          (In.rho j h1 h2) (In.chi j h1 h2) g (e x)) ∧
      ∀ k P x, e ((mkEx D T S In hE hfg hst sd rho hrho he Pq wt).hkF i j b k P x) =
        algebraMap ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)
            (FractionRing ((T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T)).O i)) (cHkT D T i b P : T.O i) ^ k •
          GlobalTheory.HeightCounting.hkF D ({ S with } : RatDat (T.ntw hE (mkF D T S In hfg hst sd rho hrho) (TwL.empty T))) i j b
            (In.hL j) (In.hs j h1 h2) k P (e x) := by
  atlas_forward_decl GlobalTheory.HeightCounting.FormsStep.formsExport_eq
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting.FormsStep.CoverPl

section SlopeTestRemainingChoices

variable {K : Type} [Field K]

def vRing (v : AddValuation K (WithTop ℤ)) : ValuationSubring K where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    show 0 ≤ v (a * b)
    rw [v.map_mul]
    exact add_nonneg ha hb
  one_mem' := by
    show 0 ≤ v 1
    rw [v.map_one]
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (v.map_add a b)
  zero_mem' := by
    show 0 ≤ v 0
    rw [v.map_zero]
    exact le_top
  neg_mem' {a} ha := by
    show 0 ≤ v (-a)
    rw [v.map_neg]
    exact ha
  mem_or_inv_mem' x := by
    by_cases hx : 0 ≤ v x
    · exact Or.inl hx
    · right
      show 0 ≤ v x⁻¹
      by_contra hy
      push_neg at hx hy
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [v.map_zero] at hx
        exact absurd hx (not_lt.mpr le_top)
      have h1 : v x + v x⁻¹ = 0 := by
        rw [← v.map_mul, mul_inv_cancel₀ hx0, v.map_one]
      have h2 : v x + v x⁻¹ ≤ v x + 0 := add_le_add le_rfl hy.le
      rw [add_zero, h1] at h2
      exact absurd hx (not_lt.mpr h2)

theorem v_nonneg_int [NumberField K] (v : AddValuation K (WithTop ℤ)) (a : 𝓞 K) : 0 ≤ v (a : K) := by
  have h1 : IsIntegral ℤ (a : K) := NumberField.RingOfIntegers.isIntegral_coe a
  have h2 : IsIntegral (vRing v) (a : K) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  have h3 : algebraMap (vRing v) K y ∈ vRing v := y.2
  rw [hy] at h3
  exact h3

theorem emb_int_mem [NumberField K] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (e : K →+* FractionRing O) (a : 𝓞 K) : ∃ y : O, algebraMap O (FractionRing O) y = e a := by
  obtain ⟨p, hp, hev⟩ := NumberField.RingOfIntegers.isIntegral_coe a
  have h1 : IsIntegral O (e (a : K)) := by
    refine ⟨p.map (algebraMap ℤ O), hp.map _, ?_⟩
    have hc : (algebraMap O (FractionRing O)).comp (algebraMap ℤ O) = e.comp (algebraMap ℤ K) := RingHom.ext_int _ _
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hev, map_zero]
  exact IsIntegrallyClosed.isIntegral_iff.mp h1

theorem exists_frac_compl {A : Type} [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
    (q : Ideal A) [q.IsPrime] (hq : q ≠ ⊥) (z : K) :
    ∃ a s : A, s ∉ q ∧ (z * algebraMap A K s = algebraMap A K a ∨ z * algebraMap A K a = algebraMap A K s) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective A z
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq (Localization.AtPrime q)
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
    IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
  have hy0 : algebraMap A K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime q) x)
    (algebraMap A (Localization.AtPrime q) y)
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl c
  have hs := IsLocalization.mk'_spec (Localization.AtPrime q) a s
  rcases hc with hc | hc
  · have h : x * a = y * s := hinj (by
      rw [map_mul, map_mul, ← hs, ← hc]
      ring)
    refine ⟨a, s, s.2, Or.inr ?_⟩
    rw [div_mul_eq_mul_div, div_eq_iff hy0, ← map_mul, ← map_mul, h, mul_comm]
  · have h : y * a = x * s := hinj (by
      rw [map_mul, map_mul, ← hs, ← hc]
      ring)
    refine ⟨a, s, s.2, Or.inl ?_⟩
    rw [div_mul_eq_mul_div, div_eq_iff hy0, ← map_mul, ← map_mul, ← h, mul_comm]

end SlopeTestRemainingChoices

section Cen

variable {K : Type} [Field K] [NumberField K]

def cen (v : AddValuation K (WithTop ℤ)) : Ideal (𝓞 K) where
  carrier := {a | 0 < v (a : K)}
  add_mem' {a b} ha hb := by
    show 0 < v ((a : K) + (b : K))
    exact lt_of_lt_of_le (lt_min ha hb) (v.map_add _ _)
  zero_mem' := by
    show 0 < v (0 : K)
    rw [v.map_zero]
    exact WithTop.coe_lt_top 0
  smul_mem' c a ha := by
    show 0 < v ((c : K) * (a : K))
    rw [v.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (v_nonneg_int v c))

theorem mem_cen {v : AddValuation K (WithTop ℤ)} {a : 𝓞 K} : a ∈ cen v ↔ 0 < v (a : K) := Iff.rfl

theorem cen_isPrime (v : AddValuation K (WithTop ℤ)) : (cen v).IsPrime where
  ne_top' h := by
    have h1 : (1 : 𝓞 K) ∈ cen v := h ▸ Submodule.mem_top
    change 0 < v (1 : K) at h1
    rw [v.map_one] at h1
    exact lt_irrefl _ h1
  mem_or_mem' {a b} hab := by
    by_contra hn
    push_neg at hn
    have ha : v (a : K) = 0 := le_antisymm (not_lt.mp (fun h => hn.1 h)) (v_nonneg_int v a)
    have hb : v (b : K) = 0 := le_antisymm (not_lt.mp (fun h => hn.2 h)) (v_nonneg_int v b)
    have h := (mem_cen (v := v)).mp hab
    change 0 < v ((a : K) * (b : K)) at h
    rw [v.map_mul, ha, hb, add_zero] at h
    exact lt_irrefl _ h

theorem v_nonneg_iff (v : AddValuation K (WithTop ℤ)) (q : Ideal (𝓞 K)) [q.IsPrime] (hq0 : q ≠ ⊥)
    (hq : ∀ a : 𝓞 K, a ∈ q ↔ 0 < v (a : K)) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (e : K →+* FractionRing O)
    (he : ∀ a : 𝓞 K, a ∈ q ↔ ∃ y ∈ IsLocalRing.maximalIdeal O, algebraMap O (FractionRing O) y = e (a : K)) (x : K) :
    0 ≤ v x ↔ e x ∈ (algebraMap O (FractionRing O)).range := by
  have hφ : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O (FractionRing O)
  have hout : ∀ a : 𝓞 K, a ∉ q → v (a : K) = 0 ∧ ∃ u : O, IsUnit u ∧ algebraMap O (FractionRing O) u = e (a : K) := by
    intro a ha
    refine ⟨le_antisymm (not_lt.mp (fun h => ha ((hq a).mpr h))) (v_nonneg_int v a), ?_⟩
    obtain ⟨u, hu⟩ := emb_int_mem e a
    exact ⟨u, IsLocalRing.notMem_maximalIdeal.mp (fun hm => ha ((he a).mpr ⟨u, hm, hu⟩)), hu⟩
  obtain ⟨a, s, hs, h⟩ := exists_frac_compl q hq0 x
  obtain ⟨hvs, us, hus, hes⟩ := hout s hs
  rcases h with h | h
  · obtain ⟨ua, hua⟩ := emb_int_mem e a
    have h1 : 0 ≤ v x := by
      have h' := congrArg v h
      rw [v.map_mul] at h'
      change v x + v (s : K) = v (a : K) at h'
      rw [hvs, add_zero] at h'
      rw [h']
      exact v_nonneg_int v a
    have h2 : e x ∈ (algebraMap O (FractionRing O)).range := by
      refine ⟨ua * ↑hus.unit⁻¹, ?_⟩
      have h' := congrArg e h
      rw [map_mul] at h'
      change e x * e (s : K) = e (a : K) at h'
      rw [← hes, ← hua] at h'
      rw [map_mul, ← h', mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
    exact ⟨fun _ => h2, fun _ => h1⟩
  · by_cases ha : a ∈ q
    · have hva := (hq a).mp ha
      obtain ⟨ua, hum, hua⟩ := (he a).mp ha
      have h1 : ¬ 0 ≤ v x := by
        intro hx
        have h' := congrArg v h
        rw [v.map_mul] at h'
        change v x + v (a : K) = v (s : K) at h'
        rw [hvs] at h'
        have h3 : 0 < v x + v (a : K) := lt_of_lt_of_le hva (le_add_of_nonneg_left hx)
        rw [h'] at h3
        exact lt_irrefl _ h3
      have h2 : e x ∉ (algebraMap O (FractionRing O)).range := by
        rintro ⟨y, hy⟩
        have h' := congrArg e h
        rw [map_mul] at h'
        change e x * e (a : K) = e (s : K) at h'
        rw [← hy, ← hua, ← hes, ← map_mul] at h'
        have h4 := hφ h'
        apply IsLocalRing.notMem_maximalIdeal.mpr hus
        rw [← h4]
        exact Ideal.mul_mem_left _ y hum
      exact ⟨fun hx => absurd hx h1, fun hx => absurd hx h2⟩
    · obtain ⟨hva, ua, hua', hua⟩ := hout a ha
      have h1 : 0 ≤ v x := by
        have h' := congrArg v h
        rw [v.map_mul] at h'
        change v x + v (a : K) = v (s : K) at h'
        rw [hvs, hva, add_zero] at h'
        rw [h']
      have h2 : e x ∈ (algebraMap O (FractionRing O)).range := by
        refine ⟨us * ↑hua'.unit⁻¹, ?_⟩
        have h' := congrArg e h
        rw [map_mul] at h'
        change e x * e (a : K) = e (s : K) at h'
        rw [← hes, ← hua] at h'
        rw [map_mul, ← h', mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
      exact ⟨fun _ => h2, fun _ => h1⟩

end Cen

section Main

theorem exists_setting_of_place : ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D) (Sx : Finset (PlE D.host))
    (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (w : D.what₂.places.Pl), ∃ i, T.l i = D.what₂.places.resChar w ∧
      ∀ x : D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔
        T.emb0 i x ∈ (algebraMap (T.O0 i) (FractionRing (T.O0 i))).range := by
  intro D cf b0 b1 Sx T Sp w
  let v : AddValuation D.LL0 (WithTop ℤ) := (D.what₂.places.val w).comap (algebraMap D.LL0 D.what₂.LL)
  have hv : ∀ x : D.LL0, v x = D.what₂.places.val w (x : D.what₂.LL) := fun x => rfl
  haveI := cen_isPrime v
  have hp := D.what₂.places.resChar_prime w
  have hpc : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.LL0) ∈ cen v := by
    rw [mem_cen, hv]
    have h1 : ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.LL0) : D.LL0) : D.what₂.LL) =
        ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by simp
    rw [h1, D.what₂.places.val_resChar w]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hne : cen v ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpc
    exact hp.ne_zero (by exact_mod_cast hpc)
  let q : HeightOneSpectrum (𝓞 D.LL0) := ⟨cen v, cen_isPrime v, hne⟩
  refine ⟨Sp.eTw.symm q, ?_, ?_⟩
  · obtain ⟨hl, -⟩ := Sp.pl_emb (Sp.eTw.symm q)
    rw [Equiv.apply_symm_apply] at hl
    change _ ∈ cen v at hl
    by_contra hne'
    have hcop : Nat.Coprime (T.l (Sp.eTw.symm q)) (D.what₂.places.resChar w) :=
      (Nat.coprime_primes Fact.out hp).mpr hne'
    obtain ⟨u, u', huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have h1 : (1 : 𝓞 D.LL0) ∈ cen v := by
      have h2 := congrArg (Int.cast : ℤ → 𝓞 D.LL0) huv
      push_cast at h2
      rw [← h2]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hpc)
    exact (cen_isPrime v).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · intro x
    obtain ⟨-, hq⟩ := Sp.pl_emb (Sp.eTw.symm q)
    rw [Equiv.apply_symm_apply] at hq
    exact v_nonneg_iff v (cen v) hne (fun a => mem_cen) (T.emb0 (Sp.eTw.symm q)) hq x

end Main

end GlobalTheory.HeightCounting.FormsStep.CoverPl
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistIndex_of_coefficientField_place : ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd)
    (Sp : RingSpec D cf b0 b1 Sx T) (w : D.what₂.places.Pl), ∃ i, T.l i = D.what₂.places.resChar w ∧
      ∀ x : D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔
        T.emb0 i x ∈ (algebraMap (T.O0 i) (FractionRing (T.O0 i))).range := by
  atlas_forward_decl GlobalTheory.HeightCounting.FormsStep.CoverPl.exists_setting_of_place
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem star_mul_self_of_pow (D : D7) (ζ : (↥D.LL0)ˣ) (n : ℕ) (hn : n ≠ 0) (h : ζ ^ n = 1) :
    star ((ζ : ↥D.LL0) : D.what₂.LL) * ((ζ : ↥D.LL0) : D.what₂.LL) = 1 := by
  apply D.what₂.embLL.injective
  rw [map_mul, map_one, D.starLL_cx]
  have hp : ((ζ : ↥D.LL0) : D.what₂.LL) ^ n = 1 := by
    have e := congrArg (fun u : (↥D.LL0)ˣ => ((u : ↥D.LL0) : D.what₂.LL)) h
    simpa using e
  have hz : (D.what₂.embLL ((ζ : ↥D.LL0) : D.what₂.LL)) ^ n = 1 := by
    rw [← map_pow, hp, map_one]
  have hn1 : ‖D.what₂.embLL ((ζ : ↥D.LL0) : D.what₂.LL)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hn
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn1]
  simp

theorem readT_false_eq (D : D7) (T : TwR D.LL0 D.nd) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (i : T.Tw) (x : ↥D.LL0) : readT D T i false x = readT D T i true ⟨star (x : D.what₂.LL), hstar x⟩ := by
  simp only [readT, RingHom.comp_apply, Bool.false_eq_true, if_false, if_true]
  rw [T.restX_coefficientEmbedding_conj i x ⟨star (x : D.what₂.LL), hstar x⟩ rfl]

theorem readT_false_mul_true (D : D7) (T : TwR D.LL0 D.nd) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (i : T.Tw) (ζ : (↥D.LL0)ˣ) (n : ℕ) (hn : n ≠ 0) (h : ζ ^ n = 1) :
    readT D T i false (ζ : ↥D.LL0) * readT D T i true (ζ : ↥D.LL0) = 1 := by
  rw [readT_false_eq D T hstar, ← map_mul]
  have e : (⟨star ((ζ : ↥D.LL0) : D.what₂.LL), hstar _⟩ : ↥D.LL0) * (ζ : ↥D.LL0) = 1 :=
    Subtype.ext (star_mul_self_of_pow D ζ n hn h)
  rw [e, map_one]

theorem mul_pow_g_eq_one (g : ℕ) (m : Multiplicative (ZMod g)) : m ^ g = 1 := by
  rw [← ofAdd_toAdd m, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem psiUT_eq_thSide : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    (∀ i b (u : Formalism.IndefR.NX.U D.nd), psiUT D T In.θ i b u = psiUOf D.nd (NX.xiRed D)
      (thSide D.host.g (fun k => (Units.map (readT D T i true).toMonoidHom).comp (In.θ k)) b) u) ∧
    (2 ≤ D.R.r → ∀ i k, (Units.map (readT D T i true).toMonoidHom).comp (In.θ k) ≠ 1) := by
  intro D S In T hstar
  refine ⟨fun i b u => ?_, fun _ i k h => ?_⟩
  · simp only [psiUT, MonoidHom.comp_apply, psiUOf_apply, map_prod]
    refine Finset.prod_congr rfl fun kv _ => ?_
    cases b
    · simp only [thSide, Bool.false_eq_true, if_false, MonoidHom.inv_apply, MonoidHom.comp_apply]
      apply Units.ext
      rw [Units.coe_map, Units.val_inv_eq_inv_val, Units.coe_map]
      refine eq_inv_of_mul_eq_one_left ?_
      exact readT_false_mul_true D T hstar i _ (D.host.g kv.1) (D.host.g_prime kv.1).ne_zero
        (by rw [← map_pow, mul_pow_g_eq_one, map_one])
    · rfl
  · apply In.θ_ne k
    refine MonoidHom.ext fun x => Units.ext ?_
    apply (readT D T i true).injective
    have e := congrArg (fun u : (FractionRing (T.O i))ˣ => (u : FractionRing (T.O i))) (DFunLike.congr_fun h x)
    simpa using e

end GlobalTheory.HeightCounting.FormsStep
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericUnipotentCharacterAtSide_eq_thetaSide : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    (∀ i b (u : Formalism.IndefR.NX.U D.nd), psiUT D T In.θ i b u = psiUOf D.nd (NX.xiRed D)
      (thSide D.host.g (fun k => (Units.map (readT D T i true).toMonoidHom).comp (In.θ k)) b) u) ∧
    (2 ≤ D.R.r → ∀ i k, (Units.map (readT D T i true).toMonoidHom).comp (In.θ k) ≠ 1) := by
  atlas_forward_decl GlobalTheory.HeightCounting.FormsStep.psiUT_eq_thSide
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem universalCharacter_admissibleConductor_inertia_surjective : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (hE : IsEmpty D.nd.Loc) (F : TwF T)
    (i : T.Tw) (Q : Finset (PlE D.host)) (M : ℕ), Formalism.MainNotions.NAdm.AdmQ (T.ntw hE F (TwL.empty T)) i Q M →
    ∀ P (hP : P ∈ Q),
      (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := D.host.E) A =>
          Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩) ∧
      ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' →
        ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩ = 0 := by
  intro _ D cf b0 b1 Sx T Sp hE F i Q M hQ P hP
  obtain ⟨-, hadm⟩ := hQ
  have hcl : ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q := fun P hP P' h => by
    obtain ⟨⟨P'', hP'', h''⟩, -⟩ := hadm P hP
    rw [GlobalTheory.GalChar.isConjPl_unique h h'']
    exact hP''
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hadm P hP
  have hsP : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
      ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
    obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
    exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
  have hDel : GlobalTheory.GalChar.IsDel D.host T.cc (T.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun w hw => h4 w (fun e => hw (Or.inl e)) (fun e => hw (Or.inr e)), fun w hw A hA b => ?_⟩
    rcases hw with rfl | hw
    · exact hsP A hA b
    · exact GlobalTheory.SpreadRestrict.surj_conj (X := T.ntw hE F (TwL.empty T)) χ h2 hw hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host T.cc (T.l i) ⟨χ, hDel⟩
  have hcoord := (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.2.2.2.2.2.1 Q M hcl P hP
  refine ⟨fun A hA c => ?_, fun P' _ hne hnc A hA σ hσ => ?_⟩
  · obtain ⟨σ, hσ, e⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd c)
    refine ⟨⟨σ, hσ⟩, ?_⟩
    show Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩ = c
    rw [hcoord, e, toAdd_ofAdd]
  · rw [hcoord, hD.2.2.2.1 P' (fun h => h.elim (fun e => hne e) (fun e => hnc e)) A hA σ hσ]
    rfl

end GlobalTheory.HeightCounting.FormsStep

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_surjective_of_admQ : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (hE : IsEmpty D.nd.Loc) (F : TwF T)
    (i : T.Tw) (Q : Finset (PlE D.host)) (M : ℕ), Formalism.MainNotions.NAdm.AdmQ (T.ntw hE F (TwL.empty T)) i Q M →
    ∀ P (hP : P ∈ Q),
      (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := D.host.E) A =>
          Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩) ∧
      ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' →
        ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (GlobalTheory.GalChar.delU D.host T.cc (T.l i) Q M σ) ⟨P, hP⟩ = 0 := by
  atlas_forward_decl GlobalTheory.HeightCounting.FormsStep.universalCharacter_admissibleConductor_inertia_surjective
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem tameChar_of_prime_residue : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (g - 1) = 1) → ∃ τ : (ZMod g)ˣ →* Oˣ, ∀ (x : (ZMod g)ˣ) (u : 𝓞 E), (((x : ZMod g).val : 𝓞 E) - u) ∈ P.asIdeal → τ x = NX.tameVal χ P 1 u := by
  intro E Ω _ _ _ _ _ P g hg hN hgP O _ _ _ _ _ hadic χ hχc hχI
  have : NeZero g := ⟨hg.ne_zero⟩
  have : Fact (1 < g) := ⟨hg.one_lt⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  set m := g - 1 with hm_def
  have hm0 : 0 < m := by have := hg.two_le; omega
  have hPtop : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hmP : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal := by
    intro h
    apply hPtop
    rw [Ideal.eq_top_iff_one]
    have h1 : ((g : ℕ) : 𝓞 E) = (m : 𝓞 E) + 1 := by
      have : g = m + 1 := by have := hg.two_le; omega
      rw [this]; push_cast; ring
    have := P.asIdeal.sub_mem hgP h
    rwa [h1, add_sub_cancel_left] at this
  have hNm : normV P - 1 = m := by rw [hN]
  obtain ⟨ϖ, hϖ, hϖ2⟩ : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 := by
    have hlt : P.asIdeal ^ (1 + 1) < P.asIdeal ^ 1 := Ideal.pow_succ_lt_pow P.ne_bot 1
    rw [pow_one] at hlt
    exact SetLike.exists_of_lt hlt
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ : E)) hm0
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0.ne', eq_comm, map_eq_zero_iff _ (algebraMap E Ω).injective] at hπ
    have hϖ0 : ϖ = 0 := by exact_mod_cast hπ
    exact hϖ2 (hϖ0 ▸ Ideal.zero_mem _)
  obtain ⟨A₀, hA₀⟩ := exists_isPlaceOver Ω P
  have hvm : ¬ A₀.valuation (m : Ω) < 1 := by
    intro h; apply hmP; rw [← hA₀]; simpa using h
  have hex : ∀ u : 𝓞 E, u ∉ P.asIdeal → ∃ σ : G E Ω, σ ∈ Ine (F := E) A₀ ∧ ∃ ζ : Ω, ζ ^ m = 1 ∧
      A₀.valuation (ζ - algebraMap E Ω (u : E)) < 1 ∧ σ π = ζ * π := by
    intro u hu
    obtain ⟨ζ, hζ, hζu⟩ := GlobalTheory.T.exists_rootOfUnity_congr_unit_at_place A₀ P hA₀ u hu
    rw [hNm] at hζ
    obtain ⟨σ, hσ, hσπ⟩ := GlobalTheory.T.inertia_acts_on_tame_root A₀ P hA₀ m hm0 hmP ϖ hϖ hϖ2 π hπ ζ hζ
    exact ⟨σ, hσ, ζ, hζ, hζu, hσπ⟩
  have hrep : ∀ σ ∈ Ine (F := E) A₀, ∀ u : 𝓞 E, A₀.valuation (σ π / π - algebraMap E Ω (u : E)) < 1 →
      NX.TameRep P 1 σ u := by
    intro σ hσ u h
    refine ⟨A₀, hA₀, hσ, ϖ, π, hϖ, hϖ2, by rw [hNm]; exact hπ, ?_⟩
    rw [zpow_one]; exact h
  have hkey : ∀ (σ : G E Ω) (u : 𝓞 E), NX.TameRep P 1 σ u → NX.tameVal χ P 1 u = χ σ := by
    intro σ u h
    rw [NX.tameVal, dif_pos ⟨σ, h⟩]
    exact GlobalTheory.T.tameChar_eq_of_tameRep_congr P hadic χ hχc (by rw [hNm]; exact hm0) (by rw [hNm]; exact hmP)
      (by intro A hA σ' hσ'; rw [hNm]; exact hχI A hA σ' hσ') _ σ u u (⟨σ, h⟩ : ∃ σ, NX.TameRep P 1 σ u).choose_spec h (by simp)
  have hlt : ∀ a b : Ω, A₀.valuation a ≤ 1 → A₀.valuation b < 1 → A₀.valuation (a * b) < 1 := by
    intro a b ha hb
    rw [map_mul]
    calc A₀.valuation a * A₀.valuation b ≤ 1 * A₀.valuation b := by gcongr
      _ = A₀.valuation b := one_mul _
      _ < 1 := hb
  have hle : ∀ a b : Ω, A₀.valuation a ≤ 1 → A₀.valuation (a - b) < 1 → A₀.valuation b ≤ 1 := by
    intro a b ha hab
    have e : b = a - (a - b) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le ha hab.le)
  have hP1 : ∀ w : 𝓞 E, w ∈ P.asIdeal → A₀.valuation (algebraMap E Ω (w : E)) < 1 := fun w hw => (hA₀ w).2 hw
  let U : (ZMod g)ˣ → 𝓞 E := fun x => (((x : ZMod g)).val : 𝓞 E)
  have hcong : ∀ x y : (ZMod g)ˣ, U x * U y - U (x * y) ∈ P.asIdeal := by
    intro x y
    simp only [U, Units.val_mul, ZMod.val_mul]
    have e : (((x : ZMod g).val * (y : ZMod g).val : ℕ) : 𝓞 E) =
        (g : 𝓞 E) * (((x : ZMod g).val * (y : ZMod g).val / g : ℕ) : 𝓞 E) +
          (((x : ZMod g).val * (y : ZMod g).val % g : ℕ) : 𝓞 E) := by
      exact_mod_cast (Nat.div_add_mod ((x : ZMod g).val * (y : ZMod g).val) g).symm
    rw [← Nat.cast_mul, e, add_sub_cancel_right]
    exact P.asIdeal.mul_mem_right _ hgP
  have hU1 : U 1 = 1 := by
    show (((1 : (ZMod g)ˣ) : ZMod g).val : 𝓞 E) = 1
    rw [Units.val_one, ZMod.val_one, Nat.cast_one]
  have hUP : ∀ x, U x ∉ P.asIdeal := by
    intro x hx
    have h := hcong x x⁻¹
    rw [mul_inv_cancel, hU1] at h
    apply hPtop
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 E) = U x * U x⁻¹ - (U x * U x⁻¹ - 1) := by ring
    rw [e]
    exact P.asIdeal.sub_mem (P.asIdeal.mul_mem_right _ hx) h
  choose σx hσx ζx hζx hζu hσπ using fun x => hex (U x) (hUP x)
  have hq : ∀ x, σx x π / π = ζx x := fun x => by rw [hσπ x, mul_div_cancel_right₀ _ hπ0]
  have hζ1 : ∀ x, A₀.valuation (ζx x) = 1 := fun x => valuation_eq_one_of_pow_eq_one A₀ hm0.ne' (hζx x)
  have hrepx : ∀ x, NX.TameRep P 1 (σx x) (U x) := fun x => hrep _ (hσx x) _ (by rw [hq]; exact hζu x)
  refine ⟨MonoidHom.mk' (fun x => χ (σx x)) ?_, ?_⟩
  · intro x y
    rw [← map_mul, ← hkey _ _ (hrepx (x * y))]
    refine hkey _ _ (hrep _ ((Ine (F := E) A₀).mul_mem (hσx x) (hσx y)) _ ?_)
    rw [GlobalTheory.TameTau.quot_mul (hσx x) m hvm hπ0 hπ, hq, hq]
    have e : ζx x * ζx y - algebraMap E Ω (U (x * y) : E) =
        ζx x * (ζx y - algebraMap E Ω (U y : E)) + algebraMap E Ω (U y : E) * (ζx x - algebraMap E Ω (U x : E)) +
          algebraMap E Ω ((U x * U y - U (x * y) : 𝓞 E) : E) := by
      push_cast; ring
    rw [e]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ (hlt _ _ (hζ1 x).le (hζu y))
      (hlt _ _ (hle _ _ (hζ1 y).le (hζu y)) (hζu x))) (hP1 _ (hcong x y))
  · intro x u hxu
    show χ (σx x) = _
    refine (hkey _ _ (hrep _ (hσx x) _ ?_)).symm
    rw [hq]
    have e : ζx x - algebraMap E Ω (u : E) = (ζx x - algebraMap E Ω (U x : E)) +
        algebraMap E Ω ((U x - u : 𝓞 E) : E) := by
      push_cast; ring
    rw [e]
    exact Valuation.map_add_lt _ (hζu x) (hP1 _ hxu)

end GlobalTheory.TameTau
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_char_of_tame_char_prime_residue_field : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (g - 1) = 1) → ∃ τ : (ZMod g)ˣ →* Oˣ, ∀ (x : (ZMod g)ˣ) (u : 𝓞 E), (((x : ZMod g).val : 𝓞 E) - u) ∈ P.asIdeal → τ x = NX.tameVal χ P 1 u := by
  atlas_forward_decl GlobalTheory.TameTau.tameChar_of_prime_residue
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.TameTau

theorem tauTame : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (j : ℕ) (b : Bool)
    (kv : Σ kk : Fin 2, D.nd.PlG kk), 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (T.l i) →
    TauTameT D T i j b kv := by
  intro _ D cf b0 b1 Sx T Sp i j b kv _ _ hl
  have hg := D.host.g_prime kv.1
  have hover := D.naut.plGw_over kv.1 kv.2
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_residue_char_of_tame_char_prime_residue_field (E := D.host.E) (Ω := D.nd.Om) (NX.pG D kv) (D.host.g kv.1) hg
    (GlobalTheory.Proof.EigenvalueCoprimeConjugation.normV_plGw D kv.1 kv.2) (by simpa [placesOver] using hover) (T.twistBaseCoefficientRing_isAdic i) (T.chi1 i j b)
    (T.twistCharacterFamily_continuous i j b) (fun A hA σ hσ => T.twistCharacterFamily_tame i j b kv.1 _ hover hl A hA σ hσ)
  refine ⟨(Units.map (baseCoeffToFractionRing D T i).toMonoidHom).comp τ, fun x u hu => ?_⟩
  rw [MonoidHom.comp_apply, Units.coe_map, hτ x u hu]
  rfl

end GlobalTheory.TameTau
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTameBlockCharacter_typePlace_not_over_l : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D)
    (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (i : T.Tw) (j : ℕ) (b : Bool)
    (kv : Σ kk : Fin 2, D.nd.PlG kk), 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (T.l i) →
    TauTameT D T i j b kv := by
  atlas_forward_decl GlobalTheory.TameTau.tauTame
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

attribute [local instance] algKkT

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem second_step : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (S : RatDat D.ntw) (In : RatIn D S) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (Q : D.what₂.places.Pl → Finset (PlE D.host)), MtInput D M tup Q → (∀ v, NG.OverPl (Pq v) v) → GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → ∃ c0 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T), (∀ (l : ℕ) [Fact l.Prime] j, (c0 l j).1 ≤ (b0 l j).1) → In.Sb ⊆ Sx → (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) → (∀ p ∈ low, placesOver D.host.E p ⊆ ↑Sx) → ∃ (F : TwF T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw A.bare F (TwL.empty T))) (h0 : _), (∀ i j b, (ex.Bsup i j b).FG ∧ Submodule.span (FractionRing ((T.ntw A.bare F (TwL.empty T)).O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) ∧ ∀ th, Nonempty (SideB (⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row A.row) low Pq ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) In.hL In.eig In.θ) := by
  intro hGAR D cf jE A S In low Pq M tup Q hM hPq hGal hRC hCh hstar hexp hsplit
  obtain ⟨c1, hc1⟩ := GlobalTheory.T.exists_galois_rep_family_bounded hGAR D cf jE A hGal hRC hCh hstar
  obtain ⟨c2, hc2⟩ := GlobalTheory.T.exists_weight_data_integral hGAR D cf jE A hstar hexp
  refine ⟨fun l _ j => ⟨(c1 l j).1 ⊔ (c2 l j).1, by haveI := (c1 l j).2; haveI := (c2 l j).2; infer_instance⟩,
    fun b0 b1 Sx T Sp hc0 hSb hconj hlow => ?_⟩
  have hb1 : ∀ (l : ℕ) [Fact l.Prime] j, (c1 l j).1 ≤ (b0 l j).1 := fun l _ j => le_trans le_sup_left (hc0 l j)
  have hb2 : ∀ (l : ℕ) [Fact l.Prime] j, (c2 l j).1 ≤ (b0 l j).1 := fun l _ j => le_trans le_sup_right (hc0 l j)
  obtain ⟨rho, hrho, hrhoS⟩ := hc1 b0 b1 Sx T Sp hb1
  obtain ⟨wt, hwt⟩ := hc2 b0 b1 Sx T Sp hb2
  have hfg := GlobalTheory.T.twisted_lattice_finitely_generated_spanning D S In T
  have hfg' : ∀ i j b, (BsupT D T S i j b).FG := fun i j b => (hfg i j b).1
  have hst := GlobalTheory.T.hecke_stable_rational_lattice D cf jE A S In b0 b1 Sx T Sp hSb hstar
  obtain ⟨sd, hsd1, hsd2, hsd3, hsd4, hsd5⟩ := GlobalTheory.T.exists_sigData_hecke_eigenvalue_formula D cf jE A S In b0 b1 Sx T Sp hst hSb hstar
  have he := GlobalTheory.T.isCentralGroupAlgebraIdempotent_universal D
  have hpsi := GlobalTheory.T.genericUnipotentCharacterAtSide_eq_thetaSide D S In T hstar
  refine ⟨mkF D T S In hfg' hst sd rho hrho, mkEx D T S In A.bare hfg' hst sd rho hrho he Pq wt, D.nStage_trivialCharacter_coeff_eq,
    fun i j b => hfg i j b, fun th => ⟨?_⟩⟩
  let N : TwNew D := ⟨T.ntw A.bare (mkF D T S In hfg' hst sd rho hrho) (TwL.empty T),
    mkEx D T S In A.bare hfg' hst sd rho hrho he Pq wt, D.nStage_trivialCharacter_coeff_eq, th, Sp.br, Sp.br_ind⟩
  have hU := tied_U_clauses N.toD7 (fun (i : T.Tw) k => (Units.map (readT D T i true).toMonoidHom).comp (In.θ k))
    (fun _ => xiRedNZ N.toD7) (fun h i k => hpsi.2 h i k) rfl (fun i b u => hpsi.1 i b u)
  have hLev : ∀ (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ), 1 ≤ j → j ≤ D.R.m → NX.AdmTw N.toD7 i k Q ψ →
      ∃ L : LevT D T i k, LevLawsT D T Pq In.θ i j b k Q ψ L ∧
        FiniteDimensional (FractionRing (T.Ok i k))
          ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ) :=
    fun i j b k Q ψ h1 h2 hadm => GlobalTheory.T.places_over_real_subfield_split hGAR D cf jE A S In Pq b0 b1 Sx T Sp hPq hsplit wt
      (fun i j b h1 h2 => ⟨(hwt i j b h1 h2).1, (hwt i j b h1 h2).2.1⟩) A.bare (mkF D T S In hfg' hst sd rho hrho)
      i j b k Q ψ h1 h2 hadm.1 hadm.2.1 hadm.2.2.1 hadm.2.2.2.1 hadm.2.2.2.2.1 hadm.2.2.2.2.2
  let E : NExpTied N.toD7 :=
    { U_eq := hU.1
      psiU_gen := hU.2.1
      psiU_side := hU.2.2.1
      psiU_xi := hU.2.2.2
      delU_cont := fun (i : T.Tw) Q M => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.2.2.1 Q M
      delU_ine := fun i Q M hQ P hP =>
        GlobalTheory.T.inertia_surjective_of_admQ hGAR D cf b0 b1 Sx T Sp A.bare (mkF D T S In hfg' hst sd rho hrho) i Q M hQ P hP
      thU_empty := fun i j b M d => PEmpty.elim d
      sgnT := 1
      sgnT_one := rfl
      Wt := wt.Wt
      acgWt := fun (i : T.Tw) j b => wt.acg i j b
      modWt := fun (i : T.Tw) j b => wt.mod i j b
      fdWt := fun (i : T.Tw) j b => wt.fd i j b
      rhoW := fun (i : T.Tw) j b => wt.rhoW i j b
      rhoW_irr := fun i j b h1 h2 => (hwt i j b h1 h2).1
      rhoW_alg := fun i j b h1 h2 => (hwt i j b h1 h2).2.1
      tauG := fun (i : T.Tw) j b kv => tauT D T i j b kv
      sgnG := 1
      sgnG_one := rfl
      tau_galois_first_character := fun (i : T.Tw) j b kv x u h1 h2 hl hu => by
        have h := GlobalTheory.T.hasTameBlockCharacter_typePlace_not_over_l hGAR D cf b0 b1 Sx T Sp i j b kv h1 h2 hl
        show ((tauT D T i j b kv x : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) =
          baseCoeffToFractionRing D T i (NX.tameVal (T.chi1 i j b) (NX.pG D kv) ((1 : ℤ) * 1) u).1
        rw [show ((1 : ℤ) * 1) = 1 from rfl]
        unfold tauT
        rw [dif_pos h]
        exact h.choose_spec x u hu
      mtV := fun (i : T.Tw) j b k Q ψ h1 h2 hadm =>
        @NX.MtVReal.mk N.toD7 i j b k Q ψ 1 (wt.Wt i j b) (wt.acg i j b) (wt.mod i j b) (wt.rhoW i j b) (tauT D T i j b)
          (WkT D T wt i j b k)
          (inferInstance : AddCommGroup (WkT D T wt i j b k))
          (inferInstance : Module (FractionRing (T.Ok i k)) (WkT D T wt i j b k))
          (inferInstance : FiniteDimensional (FractionRing (T.Ok i k)) (WkT D T wt i j b k))
          (rhoKT D T wt i j b k)
          ((hwt i j b h1 h2).2.2.1 k)
          (isAlgWeightF_bc (K' := FractionRing (T.Ok i k)) (wt.rhoW i j b) (hwt i j b h1 h2).2.1)
          ⟨_, inferInstance, inferInstance, Module.finBasis (FractionRing (T.O i)) (wt.Wt i j b),
            Algebra.TensorProduct.basis (FractionRing (T.Ok i k)) (Module.finBasis (FractionRing (T.O i)) (wt.Wt i j b)),
            fun γ => toMatrix_bcRep (K' := FractionRing (T.Ok i k)) _ (wt.rhoW i j b) γ⟩
          (hLev i j b k Q ψ h1 h2 hadm).choose.J
          (hLev i j b k Q ψ h1 h2 hadm).choose.χ
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.QP
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.DP
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.sp
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.redG
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.2.2.2
          (LinearEquiv.ofEq (MtSubT D T wt i j b k (LevLawsT D T Pq In.θ i j b k Q ψ))
            (NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k)
              (hLev i j b k Q ψ h1 h2 hadm).choose.J (hLev i j b k Q ψ h1 h2 hadm).choose.χ)
            (by rw [MtSubT, dif_pos (hLev i j b k Q ψ h1 h2 hadm)]))
      rhoW_hw := fun i j b t h1 h2 => (hwt i j b h1 h2).2.2.2.1 t
      rhoW_wt := fun i j b t hj hjm sh lam h1 h2 => (hwt i j b hj hjm).2.2.2.2 t sh lam h1 h2 }
  exact
    { twF := { K0 := Sp.K0, eO0 := Sp.eO0, j0 := Sp.j0, Lw := Sp.Lw, eO := Sp.eO, eOk := Sp.eOk, iCq := Sp.iCq,
               S0x := fun _ => Sx }
      tw := { pl_emb := fun i => ⟨Sp.eTw i, Sp.pl_emb i⟩
              ringSpec_baseIntegersEquiv_algebraMap := Sp.ringSpec_baseIntegersEquiv_algebraMap
              ringSpec_baseEmbedding_compatible := Sp.ringSpec_baseEmbedding_compatible
              eO_alg := Sp.eO_alg
              eOk_alg := Sp.eOk_alg
              mu_g := Sp.mu_g
              hk_split := fun i j b k P hP => GlobalTheory.T.lattice_basis_free_module_place D cf jE A S In b0 b1 Sx T Sp hSb hstar hst i j b k P
                (hfr := (mkF D T S In hfg' hst sd rho hrho).freeB i j b)
                (hfi := (mkF D T S In hfg' hst sd rho hrho).finB i j b) hP
              ringSpec_excludedPlaces_eq := Sp.ringSpec_excludedPlaces_eq
              concreteTwistFrame_extraExcludedPlaces_conj := fun i P P' h h' => hconj P P' h h'
              B_range := fun (i : T.Tw) j b => by
                show LinearMap.range (BI D T S In i j b).subtype = _
                rw [Submodule.range_subtype]
                rfl
              sig_inj := hsd2
              qs_pos := fun i lam => PEmpty.elim lam
              concreteTwistFrame_extraExcluded_over_smallPrimes := fun i => hlow }
      cover := fun w => GlobalTheory.T.exists_twistIndex_of_coefficientField_place D cf b0 b1 Sx T Sp w
      chiD := { mu0 := Sp.mu0H, etaT := Sp.etaH, del := Sp.delH, psi := fun a => A.bare.elim a,
                chiI := fun s lam => PEmpty.elim lam, embO := Sp.embO }
      chi := { psi := fun a => A.bare.elim a, del_fix := Sp.del_fix, delta := Sp.delta, chi1 := Sp.chi1,
               ringSpec_sidedEmbedding_fixedField := Sp.ringSpec_sidedEmbedding_fixedField, etaT_unr := Sp.etaT_unr, etaT_inf := Sp.etaT_inf,
               lamG := fun s lam => PEmpty.elim lam }
      eta_eq := Sp.eta_eq
      ringSpec_normalisedCharacter_eq := Sp.ringSpec_normalisedCharacter_eq
      del_eq := Sp.del_eq
      iCq_embO := Sp.iCq_embO
      embO_star := Sp.embO_star
      deltaRead := Sp.deltaRead
      exp := E
      pq := fun (i : T.Tw) j b k Q ψ h1 h2 hadm =>
        ⟨(hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.1, (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.1⟩
      psiU := fun i b u hu hu' => rfl
      rho := In.rho
      chiL := In.chi
      hs := In.hs
      eF := fun i j b h1 h2 => (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose
      bsup := fun i j b h1 h2 => (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose_spec.1
      act := fun i j b h1 h2 => (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose_spec.2.1
      cHk := fun (i : T.Tw) b P => cHkT D T i b P
      hkEq := fun i j b h1 h2 k P x _ _ _ =>
        (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose_spec.2.2 k P x
      cHk_del := fun i b P hP σ hσ => GlobalTheory.T.heckeComparisonUnitAtFrobenius_eq_delta D T i b P hP σ hσ
      hk_emb := fun (i : T.Tw) j b k P x h1 h2 hP hs hk => by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · show ((hkB D T S In hst i j b 0 P x : ↥(BI D T S In i j b)) : FmT D T S i j b) =
            hkT D T S In i j b 0 P (x : ↥(BI D T S In i j b)).1
          rw [show hkB D T S In hst i j b 0 P = 1 from hkB_zero D T S In hst i j b P,
            show hkT D T S In i j b 0 P = 1 from hkT_zero D T S In i j b P]
          rfl
        · show ((hkB D T S In hst i j b k P x : ↥(BI D T S In i j b)) : FmT D T S i j b) =
            hkT D T S In i j b k P (x : ↥(BI D T S In i j b)).1
          unfold hkB
          rw [dif_pos ⟨h1, h2, hk0, hk, hs, hP⟩]
          rfl
      sigSpan := fun i j b h1 h2 => hsd1 i j b h1 h2
      rowS := sd.rowS
      rowS_eig := hsd4
      hEig_zero := hsd5
      rhoS := fun i s => ⟨(hsd3 i s).1, (hsd3 i s).2, fun π hc hr hl φ ι hz hι =>
        hrhoS i (sd.rowS i s) (sd.side i s) ⟨sd.jS i s, (sd.jS_range i s).1, (sd.jS_range i s).2, (hsd3 i s).1⟩
          (hsd3 i s).2 π hc hr hl φ ι hz hι⟩ }

end GlobalTheory.HeightCounting.FormsStep
end
end
