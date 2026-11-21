import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistAllPowersOfGaloisCohomologyClassField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmbientBaseHeq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRationalRowsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivMapLattice
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ThetaSeriesDatumMemLevelTypeForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsSpannedByThetaSeriesOfClassSums
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodModelVectorEqClassSumBaseLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalDatumSmallFieldFormHeckeScalarUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem exists_basisOf_of_classSum :
    ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.admT4 D.nexp E → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∃ S, BasisOf D.nexp i j b (SgJ D.nexp E i j b) S :=
  fun D E h i hi j hj b =>
    GlobalTheory.TwistChoice.exists_basisOf D.nexp i j b _ (GlobalTheory.TwistChoice.th_fg D.nexp E h i hi j hj b)

end GlobalTheory.TwInputs
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_averaged_series_of_class_sums : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.admT4 D.nexp E → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∃ S, BasisOf D.nexp i j b (SgJ D.nexp E i j b) S := by
  atlas_forward_decl GlobalTheory.TwInputs.exists_basisOf_of_classSum
end

section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.ThetaRank

section Class

structure ClassDat (A K M W : Type) [CommRing A] [Field K] [Algebra A K] [AddCommGroup M] [Module A M]
    [AddCommGroup W] [Module A W] where
  Hf : Type
  [grp : Group Hf]
  HF : Subgroup Hf
  J : Subgroup Hf
  lam : J →* Aˣ
  PP : Type
  [acg : AddCommGroup PP]
  [modK : Module K PP]
  [modA : Module A PP]
  [tow : IsScalarTower A K PP]
  rho : HF →* (PP ≃ₗ[K] PP)
  LL : Hf → Submodule A PP
  reps : Finset Hf
  reps_cover : ∀ h, ∃ r ∈ reps, ∃ (γ : HF) (k : J), h = γ * r * k
  reps_sep : ∀ r ∈ reps, ∀ r' ∈ reps, ∀ (γ : HF) (k : J), r' = γ * r * k → r' = r
  ev : M →ₗ[A] (Hf → PP)
  ev_inj : Function.Injective ev
  ev_law : ∀ f (γ : HF) h (k : J), ev f (γ * h * k) = ((lam k : Aˣ) : A) • rho γ (ev f h)
  ser : Hf → PP →ₗ[A] W

attribute [instance] ClassDat.grp ClassDat.acg ClassDat.modK ClassDat.modA ClassDat.tow

namespace ClassDat

variable {A K M W : Type} [CommRing A] [Field K] [Algebra A K] [AddCommGroup M] [Module A M]
  [AddCommGroup W] [Module A W] (C : ClassDat A K M W)

def Gam (h : C.Hf) : Subgroup C.Hf := C.HF ⊓ C.J.map (MulAut.conj h).toMonoidHom

def thetaReps : Submodule A W := Submodule.span A {x | ∃ h ∈ C.reps, ∃ P ∈ C.LL h, x = C.ser h P}

def thetaAll : Submodule A W := Submodule.span A {x | ∃ h, ∃ P ∈ C.LL h, x = C.ser h P}

def ClassSum (Λ : Submodule A M) (θ : M →ₗ[A] W) : Prop :=
  (∀ h, Finite (C.Gam h)) ∧ (∀ f, f ∈ Λ ↔ ∀ h, C.ev f h ∈ C.LL h) ∧
    ∀ f, θ f = ∑ h ∈ C.reps, C.ser h (((Nat.card (C.Gam h) : ℕ) : K)⁻¹ • C.ev f h)

def SeriesLaw : Prop :=
  ∀ (γ : C.HF) h (k : C.J) P, C.ser (γ * h * k) (C.rho γ P) = (((C.lam k)⁻¹ : Aˣ) : A) • C.ser h P

def LatticeLaw : Prop :=
  ∀ (γ : C.HF) h (k : C.J), C.LL (γ * h * k) = (C.LL h).map ((C.rho γ).toLinearMap.restrictScalars A)


theorem exists_smul_mem [IsDomain A] [CharZero A] [CharZero K] {Λ : Submodule A M} {θ : M →ₗ[A] W}
    (h : C.ClassSum Λ θ) {f : M} (hf : f ∈ Λ) : ∃ c : A, c ≠ 0 ∧ c • θ f ∈ C.thetaReps := by
  classical
  obtain ⟨hfin, hlat, hsum⟩ := h
  have hpos : ∀ h, Nat.card (C.Gam h) ≠ 0 := fun h => by
    haveI := hfin h
    exact Nat.card_pos.ne'
  refine ⟨∏ h ∈ C.reps, ((Nat.card (C.Gam h) : ℕ) : A),
    Finset.prod_ne_zero_iff.2 fun h _ => Nat.cast_ne_zero.2 (hpos h), ?_⟩
  rw [hsum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun h hh => ?_
  rw [← Finset.prod_erase_mul _ _ hh, mul_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [← map_smul, ← algebraMap_smul K, map_natCast, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 (hpos h)), one_smul]
  exact Submodule.subset_span ⟨h, hh, _, (hlat f).1 hf h, rfl⟩

end ClassDat

end Class

section Cx

structure CxDat (A M W : Type) [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup W] [Module A W] where
  [alg : Algebra A ℂ]
  inj : Function.Injective (algebraMap A ℂ)
  MC : Type
  [nM : NormedAddCommGroup MC]
  [iM : InnerProductSpace ℂ MC]
  [fM : FiniteDimensional ℂ MC]
  cM : ℂ ⊗[A] M ≃ₗ[ℂ] MC
  WC : Type
  [nW : NormedAddCommGroup WC]
  [iW : InnerProductSpace ℂ WC]
  [fW : FiniteDimensional ℂ WC]
  cW : ℂ ⊗[A] W ≃ₗ[ℂ] WC
  Rep : Type
  part : Rep → Submodule ℂ WC
  good : Set Rep

attribute [instance] CxDat.nM CxDat.iM CxDat.fM CxDat.nW CxDat.iW CxDat.fW

theorem exists_smul_mem_of_tmul {A B W : Type} [CommRing A] [CommRing B] [Nontrivial B] [Algebra A B] [Module.Flat A B]
    [AddCommGroup W] [Module A W] (T : Submodule A W) (x : W) (h : (1 : B) ⊗ₜ[A] x ∈ T.baseChange B) :
    ∃ c : A, c ≠ 0 ∧ c • x ∈ T := by
  by_contra hne
  push_neg at hne
  let g : A →ₗ[A] W ⧸ T := LinearMap.toSpanSingleton A _ (T.mkQ x)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    by_contra hc0
    refine hne c hc0 ?_
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hc
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := B) g hg
  have h2 : T.baseChange B ≤ LinearMap.ker (T.mkQ.baseChange B) := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    show T.mkQ.baseChange B ((1 : B) ⊗ₜ[A] v) = 0
    rw [LinearMap.baseChange_tmul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero T).2 hv, TensorProduct.tmul_zero]
  have h3 : g.lTensor B ((1 : B) ⊗ₜ[A] (1 : A)) = 0 := by
    have := h2 h
    rw [LinearMap.mem_ker, LinearMap.baseChange_tmul] at this
    simpa [g] using this
  have h4 : (1 : B) ⊗ₜ[A] (1 : A) = 0 := h1 (by rw [h3, map_zero])
  have h5 := congrArg (TensorProduct.rid A B) h4
  simp at h5

namespace CxDat

variable {A M W : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup W] [Module A W] (Z : CxDat A M W)

def mapC (θ : M →ₗ[A] W) : Z.MC →ₗ[ℂ] Z.WC :=
  letI := Z.alg
  Z.cW.toLinearMap ∘ₗ θ.baseChange ℂ ∘ₗ Z.cM.symm.toLinearMap

def endC (e : W →ₗ[A] W) : Z.WC →ₗ[ℂ] Z.WC :=
  letI := Z.alg
  Z.cW.toLinearMap ∘ₗ e.baseChange ℂ ∘ₗ Z.cW.symm.toLinearMap

def subC (S : Submodule A W) : Submodule ℂ Z.WC :=
  letI := Z.alg
  (S.baseChange ℂ).map Z.cW.toLinearMap

def goodSum : Submodule ℂ Z.WC := ⨆ σ ∈ Z.good, Z.part σ

def OrthSum (S : Submodule A W) : Prop :=
  ⨆ σ, Z.part σ = Z.subC S ∧ Pairwise fun σ σ' => Z.part σ ⟂ Z.part σ'

def PosScalar (θ : M →ₗ[A] W) : Prop :=
  ∀ σ, Z.part σ ≠ ⊥ → ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Z.part σ, Z.mapC θ (LinearMap.adjoint (Z.mapC θ) x) = (c : ℂ) • x

def GoodProj (S : Submodule A W) (e : W →ₗ[A] W) : Prop :=
  ∀ x ∈ Z.subC S, Z.endC e x = Z.goodSum.starProjection x

theorem goodSum_le {S : Submodule A W} {θ : M →ₗ[A] W} {e : W →ₗ[A] W} (h1 : Z.OrthSum S) (h2 : Z.PosScalar θ)
    (h3 : Z.GoodProj S e) : Z.goodSum ≤ LinearMap.range (Z.endC e ∘ₗ Z.mapC θ) := by
  refine iSup₂_le fun σ hσ x hx => ?_
  by_cases h0 : Z.part σ = ⊥
  · rw [h0, Submodule.mem_bot] at hx
    exact hx ▸ Submodule.zero_mem _
  obtain ⟨c, hc, hcx⟩ := h2 σ h0
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hxS : x ∈ Z.subC S := h1.1 ▸ Submodule.mem_iSup_of_mem σ hx
  have hxG : x ∈ Z.goodSum := Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem hσ hx)
  refine ⟨(c : ℂ)⁻¹ • LinearMap.adjoint (Z.mapC θ) x, ?_⟩
  rw [LinearMap.comp_apply, map_smul, hcx x hx, smul_smul, inv_mul_cancel₀ hc', one_smul, h3 x hxS,
    Submodule.starProjection_eq_self_iff.2 hxG]

theorem exists_smul_mem_range [IsDomain A] [IsPrincipalIdealRing A] {S : Submodule A W} {θ : M →ₗ[A] W} {e : W →ₗ[A] W}
    (h1 : Z.OrthSum S) (h2 : Z.PosScalar θ) (h3 : Z.GoodProj S e) {y : W} (hy : y ∈ S) :
    ∃ c : A, c ≠ 0 ∧ c • e y ∈ LinearMap.range (e ∘ₗ θ) := by
  letI := Z.alg
  haveI : FaithfulSMul A ℂ := (faithfulSMul_iff_algebraMap_injective A ℂ).2 Z.inj
  haveI : Module.Flat A ℂ := inferInstance
  refine exists_smul_mem_of_tmul (B := ℂ) _ _ ?_
  have hS : Z.cW ((1 : ℂ) ⊗ₜ[A] y) ∈ Z.subC S := ⟨_, Submodule.tmul_mem_baseChange_of_mem 1 hy, rfl⟩
  have hG : Z.endC e (Z.cW ((1 : ℂ) ⊗ₜ[A] y)) ∈ Z.goodSum := by
    rw [h3 _ hS]
    exact Submodule.starProjection_apply_mem _ _
  obtain ⟨m, hm⟩ := Z.goodSum_le h1 h2 h3 hG
  have hm' : e.baseChange ℂ (θ.baseChange ℂ (Z.cM.symm m)) = (1 : ℂ) ⊗ₜ[A] e y := by
    apply Z.cW.injective
    simpa [endC, mapC] using hm
  rw [← hm']
  induction Z.cM.symm m using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  | tmul a v => exact Submodule.tmul_mem_baseChange_of_mem a ⟨v, rfl⟩

end CxDat

end Cx


namespace Model

theorem tmul_rat (z : ℂ) (q : ℚ) : z ⊗ₜ[ℤ] q = (z * q) ⊗ₜ[ℤ] (1 : ℚ) := by
  have hd : ((q.den : ℤ) : ℂ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have h1 : z = (q.den : ℤ) • (z / ((q.den : ℤ) : ℂ)) := by rw [zsmul_eq_mul]; field_simp
  have h2 : (q.den : ℤ) • q = q.num • (1 : ℚ) := by simp
  have h3 : z * q = q.num • (z / ((q.den : ℤ) : ℂ)) := by
    rw [zsmul_eq_mul, Rat.cast_def]; push_cast; ring
  rw [h3, TensorProduct.smul_tmul, ← h2, ← TensorProduct.smul_tmul, ← h1]

def cq : ℂ ⊗[ℤ] ℚ ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofLinear (((Algebra.linearMap ℚ ℂ).restrictScalars ℤ).liftBaseChange ℂ)
    (LinearMap.toSpanSingleton ℂ _ ((1 : ℂ) ⊗ₜ[ℤ] (1 : ℚ))) (by ext; simp) (by
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [map_add, map_add, ha, hb]
      | tmul z q =>
        rw [LinearMap.id_apply, tmul_rat z q]
        simp [TensorProduct.smul_tmul'])

def c2 : ℂ ⊗[ℤ] (Fin 2 → ℚ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (TensorProduct.piRight ℤ ℂ ℂ fun _ : Fin 2 => ℚ) ≪≫ₗ (LinearEquiv.piCongrRight fun _ => cq) ≪≫ₗ
    (WithLp.linearEquiv 2 ℂ (Fin 2 → ℂ)).symm


def lat : Submodule ℤ (Fin 2 → ℚ) := Submodule.pi Set.univ fun _ => (1 : Submodule ℤ ℚ)

def cls : ClassDat ℤ ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) where
  Hf := Multiplicative (ZMod 2)
  HF := ⊤
  J := ⊤
  lam := 1
  PP := Fin 2 → ℚ
  rho := 1
  LL _ := lat
  reps := {1}
  reps_cover h := ⟨1, Finset.mem_singleton_self _, ⟨h, trivial⟩, 1, by simp⟩
  reps_sep r hr r' hr' _ _ _ := by rw [Finset.mem_singleton.1 hr, Finset.mem_singleton.1 hr']
  ev := LinearMap.pi fun _ => LinearMap.id
  ev_inj _ _ h := congrFun h 1
  ev_law _ _ _ _ := by simp
  ser _ := (2 : ℤ) • LinearMap.id

abbrev cx : CxDat ℤ (Fin 2 → ℚ) (Fin 2 → ℚ) where
  inj := Int.cast_injective
  MC := EuclideanSpace ℂ (Fin 2)
  cM := c2
  WC := EuclideanSpace ℂ (Fin 2)
  cW := c2
  Rep := Fin 2
  part a := ℂ ∙ EuclideanSpace.single a (1 : ℂ)
  good := {0}

def pr : (Fin 2 → ℚ) →ₗ[ℤ] (Fin 2 → ℚ) := LinearMap.single ℤ (fun _ : Fin 2 => ℚ) 0 ∘ₗ LinearMap.proj 0

theorem gam_eq (h : cls.Hf) : cls.Gam h = ⊤ := by
  rw [eq_top_iff]
  exact fun x _ => ⟨trivial, h⁻¹ * x * h, trivial, by simp [mul_assoc]⟩

theorem card_gam (h : cls.Hf) : Nat.card (cls.Gam h) = 2 := by
  rw [gam_eq, Subgroup.card_top]
  show Nat.card (Multiplicative (ZMod 2)) = 2
  simp

theorem classSum : cls.ClassSum lat LinearMap.id := by
  refine ⟨fun h => Nat.finite_of_card_ne_zero (by rw [card_gam]; norm_num), fun f => ⟨fun hf _ => hf, fun hf => hf 1⟩,
    fun f => ?_⟩
  show f = ∑ h ∈ ({1} : Finset cls.Hf), _
  rw [Finset.sum_singleton, card_gam]
  show f = (2 : ℤ) • (((2 : ℕ) : ℚ)⁻¹ • f)
  funext a
  simp



theorem subC_top : cx.subC ⊤ = ⊤ := by
  show ((⊤ : Submodule ℤ (Fin 2 → ℚ)).baseChange ℂ).map c2.toLinearMap = ⊤
  rw [Submodule.baseChange_top, Submodule.map_top, LinearEquiv.range]

theorem orthSum : cx.OrthSum ⊤ := by
  refine ⟨?_, fun (a a' : Fin 2) h => ?_⟩
  · rw [subC_top]
    show ⨆ a : Fin 2, (ℂ ∙ EuclideanSpace.single a (1 : ℂ)) = (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2)))
    rw [← Submodule.span_range_eq_iSup, ← (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis.span_eq]
    congr 2
    funext a
    simp
  · show (ℂ ∙ EuclideanSpace.single a (1 : ℂ)) ⟂ (ℂ ∙ EuclideanSpace.single a' (1 : ℂ) :
      Submodule ℂ (EuclideanSpace ℂ (Fin 2)))
    rw [Submodule.isOrtho_span]
    rintro _ rfl _ rfl
    have h' : (a : Fin 2) ≠ a' := h
    simp [EuclideanSpace.inner_single_left, h']






end Model

section Record

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

abbrev ClassAt (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) : Type 1 :=
  ClassDat (X.Ok i k) (FractionRing (X.Ok i k)) (Y.MtV i j b k Q ψ) (X.Ok i k ⊗[X.O i] Y.Fm i j b)

abbrev CxAt (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) : Type 1 :=
  CxDat (X.Ok i k) (Y.MtV i j b k Q ψ) (X.Ok i k ⊗[X.O i] Y.Fm i j b)

def allK (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  ((Fm0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k)

def eK (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) : Module.End (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  (eO Y i j b).baseChange (X.Ok i k)

theorem map_baseChange {O O' V : Type} [CommRing O] [CommRing O'] [Algebra O O'] [AddCommGroup V] [Module O V]
    (T : Submodule O V) (e : V →ₗ[O] V) : (T.baseChange O').map (e.baseChange O') = (T.map e).baseChange O' := by
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩






def SeriesRational (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (C : ClassAt Y i j b k ∅ 1) : Prop :=
  ∀ h ∈ C.reps, ∀ P ∈ C.LL h, C.ser h P ∈ (ThJ Y E i j b).baseChange (X.Ok i k)



abbrev ClassFam (D : D7) (k : ℕ) : Type 1 :=
  ∀ i : D.ntw.Tw, D.ntw.NonzeroIndexPlace i → ∀ (j : ℕ) (b : Bool), ClassAt D.nexp i j b k ∅ 1

abbrev CxFam (D : D7) (k : ℕ) : Type 1 :=
  ∀ i : D.ntw.Tw, D.ntw.NonzeroIndexPlace i → ∀ (j : ℕ) (b : Bool), CxAt D.nexp i j b k ∅ 1

def ClassSumFormula (D : D7) (k : ℕ) (C : ClassFam D k) : Prop :=
  ∀ i hi, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, (C i hi j b).ClassSum (D.nexp.MtLat i j b k ∅ 1) (D.nexp.thP i j b k ∅ 1)

def Rationality (D : D7) (E : XD D) (k : ℕ) (C : ClassFam D k) : Prop :=
  ∀ i hi, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, SeriesRational D.nexp E i j b k (C i hi j b)

def PartsSum (D : D7) (k : ℕ) (Z : CxFam D k) : Prop :=
  ∀ i hi, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, (Z i hi j b).OrthSum (allK D.nexp i j b k)

def ThetaGramPos (D : D7) (k : ℕ) (Z : CxFam D k) : Prop :=
  ∀ i hi, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, (Z i hi j b).PosScalar (D.nexp.thP i j b k ∅ 1)

def GoodProjector (D : D7) (k : ℕ) (Z : CxFam D k) : Prop :=
  ∀ i hi, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, (Z i hi j b).GoodProj (allK D.nexp i j b k) (eK D.nexp i j b k)


end Record

end GlobalTheory.ThetaRank

end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.RankDescent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem charZero_frac (i : X.Tw) : CharZero (FractionRing (X.O i)) :=
  (RingHom.charZero_iff ((IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
      (L := FractionRing (X.O i)) (X.O_inj i)).comp (X.emb0 i)).injective).1 inferInstance

theorem eG_eG (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    Formalism.MainNotions.IntegralHeckeForms.eG Y i j b (Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x) = Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x := by
  have h := congrArg (MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b))) (Y.eAlg_idem i b)
  rw [map_mul] at h
  exact LinearMap.congr_fun h x

theorem good_idempotent_fixes_mem_good_type_space (i : X.Tw) (j : ℕ) (b : Bool) {x : Y.Fm i j b} (hx : x ∈ V0 Y i j b) :
    Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x = x := by
  obtain ⟨y, -, rfl⟩ := hx
  exact eG_eG Y i j b y

open Formalism.MainNotions.IntegralHeckeForms in

theorem AO_eq (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    AO Y i j b x = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • eG Y i j b x := by
  show ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eG Y i j b x = _
  rw [← map_natCast (algebraMap (X.O i) (FractionRing (X.O i))), algebraMap_smul]

open Formalism.MainNotions.IntegralHeckeForms in

theorem thetaSeries_mem_goodTypeForms (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) (a : Y.Dat i j b) (ha : a ∈ E.Dat0 i j b) :
    Y.th i j b a ∈ Fm0 Y i j b := by
  simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u
  have := E.theta_base_equivariant i j b a ha u
  simp [this]

open Formalism.MainNotions.IntegralHeckeForms in

theorem AO_Th_le (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) :
    ∀ x ∈ (Th Y i j b (SgJ Y E i j b)).map (AO Y i j b), x ∈ V0 Y i j b := by
  rintro _ ⟨y, hy, rfl⟩
  rw [AO_eq]
  refine Submodule.smul_mem _ _ ⟨y, ?_, rfl⟩
  refine (Submodule.span_le (p := (Fm0 Y i j b).restrictScalars (X.O i))).2 ?_ hy
  rintro _ ⟨a, ha, rfl⟩
  exact thetaSeries_mem_goodTypeForms Y E i j b a ha

open Formalism.MainNotions.IntegralHeckeForms in

theorem fullRk_of_le (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool)
    (h : V0 Y i j b ≤ Submodule.span (FractionRing (X.O i)) (eG Y i j b '' (Y.th i j b '' E.Dat0 i j b))) :
    FullRk Y E i j b (SgJ Y E i j b) := by
  haveI := charZero_frac (X := X) i
  have hc : ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) ≠ 0 := Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'
  refine ⟨subset_rfl, AO_Th_le Y E i j b, le_antisymm (Submodule.span_le.2 (AO_Th_le Y E i j b)) (h.trans ?_)⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  have e1 : eG Y i j b (Y.th i j b a) = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i))⁻¹ • AO Y i j b (Y.th i j b a) := by
    rw [AO_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.subset_span ⟨a, ha, rfl⟩, rfl⟩)

section Descent

variable {ρ : Setup X} {i : X.Tw} {j : Fin D.R.m} {b : Bool}

theorem rd_mem_span (rd : Rd ρ Y i j b) (S : Set (Y.Fm i ((j : ℕ) + 1) b)) {y : Y.Fm i ((j : ℕ) + 1) b}
    (hy : y ∈ Submodule.span (FractionRing (X.O i)) S) : rd y ∈ Submodule.span ℂ (rd '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

theorem mem_span_of_faithful {rd : Rd ρ Y i j b} (hf : Faithful rd) (S : Set (Y.Fm i ((j : ℕ) + 1) b))
    {x : Y.Fm i ((j : ℕ) + 1) b} (hx : rd x ∈ Submodule.span ℂ (rd '' S)) :
    x ∈ Submodule.span (FractionRing (X.O i)) S := by
  set W := Submodule.span (FractionRing (X.O i)) S
  by_contra hxW
  let bW := Module.finBasis (FractionRing (X.O i)) W
  let v : Fin (Module.finrank (FractionRing (X.O i)) W) → Y.Fm i ((j : ℕ) + 1) b := fun k => (bW k : Y.Fm i ((j : ℕ) + 1) b)
  have hv : LinearIndependent (FractionRing (X.O i)) v := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hspan : Submodule.span (FractionRing (X.O i)) (Set.range v) = W := by
    have := congrArg (Submodule.map W.subtype) bW.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  have hli : LinearIndependent (FractionRing (X.O i)) (Fin.cons x v : Fin _ → Y.Fm i ((j : ℕ) + 1) b) :=
    linearIndependent_fin_cons.2 ⟨hv, by rw [hspan]; exact hxW⟩
  have hC := hf _ _ hli
  have hC' : LinearIndependent ℂ (Fin.cons (rd x) (fun k => rd (v k)) : Fin _ → (GA D (Wc D j) → ℂ)) := by
    convert hC using 1
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  refine (linearIndependent_fin_cons.1 hC').2 ?_
  refine Submodule.span_le.2 ?_ hx
  rintro _ ⟨s, hs, rfl⟩
  have hsW : s ∈ Submodule.span (FractionRing (X.O i)) (Set.range v) := by
    rw [hspan]; exact Submodule.subset_span hs
  have := rd_mem_span Y rd _ hsW
  rw [← Set.range_comp] at this
  exact this

end Descent

theorem fullRk_of_spanGood : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), Comparison₂ hρ rd → (∀ i j b, Faithful (rd i j b)) → ∀ (E : IntegralHeckeForms.XD D) (i : D.ntw.Tw), (∀ j b, RatBase (rd i j b)) → (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b) → SpanGood rd i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  intro D ρ hρ rd T hF E i hR hall hS j hj b
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j' : Fin D.R.m, j = (j' : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine fullRk_of_le D.nexp E i _ b ?_
  intro x hx
  have h1 : rd i j' b x ∈ Submodule.span ℂ (rd i j' b '' (D.nexp.th i _ b '' E.Dat0 i _ b)) := by
    refine Submodule.span_mono ?_ (hS j' b x hx)
    rintro _ ⟨s, h, P, hd, rfl⟩
    obtain ⟨d, -, hc, hp⟩ := (T i j' b).dat_onto s h P hd (hR j' b s h P hd)
    refine ⟨D.nexp.th i _ b d, ⟨d, hall _ hj b d, rfl⟩, ?_⟩
    rw [(T i j' b).th_eq d, hc, hp]
  have h2 := mem_span_of_faithful D.nexp (hF i j' b) _ h1
  rw [← good_idempotent_fixes_mem_good_type_space D.nexp i _ b hx]
  have h3 := Submodule.mem_map_of_mem (f := Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i ((j' : ℕ) + 1) b) h2
  rwa [Submodule.map_span] at h3

end GlobalTheory.RankDescent

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.averaged_series_full_rank_of_complex_span_good : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), Comparison₂ hρ rd → (∀ i j b, Faithful (rd i j b)) → ∀ (E : IntegralHeckeForms.XD D) (i : D.ntw.Tw), (∀ j b, RatBase (rd i j b)) → (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b) → SpanGood rd i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  atlas_forward_decl GlobalTheory.RankDescent.fullRk_of_spanGood
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodForms_spanned_by_thetaSeries_of_classSums : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), ∀ i, SumOnto rd i → SpanGood rd i := by
  first | exact @GlobalTheory.TwInputs.spanGood_of_sumOnto | exact GlobalTheory.TwInputs.spanGood_of_sumOnto | (intros; apply GlobalTheory.TwInputs.spanGood_of_sumOnto <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SeriesTie.ModelGood

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)

def jH (j : Fin D.R.m) : S.WL ((j : ℕ) + 1) →+ (Rl.HW j (sg0 D A3.A)).H where
  toFun x := (Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e x)
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]

theorem jH_smul (j : Fin D.R.m) (c : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    jH YS j (c • x) = D.what₂.embLL c • jH YS j x := by
  change (Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (c • x)) = _
  rw [map_smul, map_smulₛₗ, show sg0 D A3.A c = D.what₂.embLL c from
    congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)]
  rfl

section Read

variable {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

def evH : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1) →+ (Rl.HW j (sg0 D A3.A)).H :=
  TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ρ.e i b a)).comp
        ((jH YS j).comp (S.A ((j : ℕ) + 1)).WK.subtype.toAddMonoidHom)
      map_zero' := by ext; simp [show ρ.e i b (0 : NX.KB S i b) = 0 from map_zero _]
      map_add' := fun x y => by
        ext; simp [show ρ.e i b (x + y : NX.KB S i b) = ρ.e i b x + ρ.e i b y from map_add _ _ _, add_smul] }
    fun c a f => by
      change ρ.e i b (sideEmb D.ntw i b (S.kKs c) * (show FractionRing (D.ntw.O i) from a)) • jH YS j (Subtype.val f) =
        ρ.e i b a • jH YS j (c • Subtype.val f)
      rw [← algebraMap_smul D.what₂.LL c, jH_smul, map_mul, hρ.e_LL0, smul_smul, mul_comm, ← S.kKs_spec]
      rfl

theorem evH_tmul (a : NX.KB S i b) (f : NX.FmK S ((j : ℕ) + 1)) :
    evH YS hρ i j b (a ⊗ₜ f) = ρ.e i b a • jH YS j (Subtype.val f) := rfl

theorem evK_eq (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b t = (Rl.HW j (sg0 D A3.A)).e (evH YS hρ i j b t) (v₀ j _) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; rfl
  | tmul a f => rw [evK_tmul, evH_tmul, map_smul]; rfl

theorem evH_smul (c : NX.KB S i b) (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evH YS hρ i j b (c • t) = ρ.e i b c • evH YS hρ i j b t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul a f =>
    rw [TensorProduct.smul_tmul', evH_tmul, evH_tmul, smul_smul]
    exact congrArg (· • _) (map_mul (ρ.e i b) c a)

def mv (y : D.nexp.Fm i ((j : ℕ) + 1) b) : (Rl.HW j (sg0 D A3.A)).H :=
  evH YS hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 y)

theorem mv_act (hU : Rl.toRealDat.LUnif) (g : G0g D.nd) (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    (Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b (D.nexp.actG i _ b g y)) =
      postOn _ (actL (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm g))
        ((Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b y)) := by
  unfold mv
  rw [YS.act]
  generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 y = t
  induction t using TensorProduct.induction_on with
  | zero =>
    erw [LinearEquiv.map_zero]
    simp only [map_zero]
    exact (congrArg (Rl.HW j (sg0 D A3.A)).e ((evH YS hρ i j b).map_zero)).trans (map_zero _)
  | add y z hy hz => erw [LinearEquiv.map_add, map_add, map_add, hy, hz, map_add, map_add, map_add]
  | tmul a f0 =>
    have e1 : (NX.actG S i ((j : ℕ) + 1) b (YS.rho _ (Nat.le_add_left _ _) j.2) (YS.chi _ (Nat.le_add_left _ _) j.2) g)
        (a ⊗ₜ f0) = ((NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g)))⁻¹ * a) ⊗ₜ
          (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0) := by
      change (NX.readLL0 S i b (NX.chiL S _ _ (S.eG.symm g)))⁻¹ •
        (a ⊗ₜ[S.Ks] (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    erw [e1]
    rw [evH_tmul, evH_tmul]
    have hgeq : Rl.eG ((YS.fi j).eG (S.eG.symm g)) = cG.symm g := by
      have h0 := YS.geq j (S.eG.symm g)
      rw [MulEquiv.apply_symm_apply] at h0
      exact ((MulEquiv.symm_apply_eq cG).2 h0.symm).symm
    have he : ρ.e i b (NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g))) =
        D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) :=
      hρ.e_LL0 i b _
    have hne : D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) ≠ 0 :=
      (map_ne_zero _).2 (Units.ne_zero _)
    have hs : sg0 D A3.A = D.what₂.embLL := GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL Rl
    change (Rl.HW j (sg0 D A3.A)).e (ρ.e i b _ • (Rl.FW j).j (sg0 D A3.A)
      ((YS.fi j).e ((S.A ((j : ℕ) + 1)).ρ (S.eG.symm g) (Subtype.val f0)))) = _
    rw [map_smul, map_smul, map_smul, (YS.fi j).rho, (hU j _).2.2, (YS.fi j).chi, hgeq, smul_smul]
    congr 1
    erw [map_mul, map_inv₀, he, hs]
    field_simp

theorem mv_smul (c : FractionRing (D.ntw.O i)) (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    mv YS hρ i j b (c • y) = ρ.e i b c • mv YS hρ i j b y := by
  unfold mv
  rw [map_smul]
  exact evH_smul YS hρ i j b c _

theorem mv_sum {ι : Type} (s : Finset ι) (y : ι → D.nexp.Fm i ((j : ℕ) + 1) b) :
    mv YS hρ i j b (∑ k ∈ s, y k) = ∑ k ∈ s, mv YS hρ i j b (y k) := by
  unfold mv
  rw [map_sum]
  exact map_sum (evH YS hρ i j b) _ _

theorem postOn_eWf_sum (σ : D.what₂.LL →+* ℂ) (M : MMap (Rl.MW j σ)) :
    postOn (Rl.MW j σ) (Rl.toRealDat.eWf j σ) M = ∑ γ : Γ, RealDat.eC (A := A3.A) σ γ •
      postOn (Rl.MW j σ) (actL (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG γ)) M := by
  refine MultilinearMap.ext fun v => ?_
  simp only [RealDat.eWf, gaL, postOn, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compMultilinearMap_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply, MultilinearMap.smul_apply]
  rfl

theorem mv_eG (hU : Rl.toRealDat.LUnif)
    (hid : ∀ γ : Γ, D.what₂.embLL ((idemOf A3.A.X).coeff γ) = D.ntypes.e0.coeff ((Rl.eG.trans cG) γ))
    (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    (Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b y)) =
      postOn _ (Rl.toRealDat.eWf j (sg0 D A3.A)) ((Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b y)) := by
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv Γ (Rl.eG.trans cG).toEquiv
  have h1 : Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b y = ∑ g, (D.nexp.eAlg i b).coeff g • D.nexp.actG i _ b g y := by
    unfold Formalism.MainNotions.IntegralHeckeForms.eG
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype]
    · rw [LinearMap.sum_apply]; rfl
    · intro; exact zero_smul _ _
  have hc : ∀ g, ρ.e i b ((D.nexp.eAlg i b).coeff g) = D.ntypes.e0.coeff g := fun g => by
    have h : (D.nexp.eAlg i b).coeff g = NX.readLL0 S i b (D.nexp.eLL0 g) := by rw [D.nexp.eAlg_def]; rfl
    rw [h]
    exact (hρ.e_LL0 i b _).trans (D.nStage_trivialCharacter_coeff_eq g)
  have hs : sg0 D A3.A = D.what₂.embLL := GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL Rl
  rw [h1, mv_sum, map_sum, postOn_eWf_sum]
  refine (Fintype.sum_equiv (Rl.eG.trans cG).toEquiv _ _ fun γ => ?_).symm
  rw [mv_smul, map_smul, mv_act YS hρ i j b hU, hc]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  congr 1
  exact (congrArg (fun f : D.what₂.LL →+* ℂ => f ((idemOf A3.A.X).coeff γ)) hs).trans (hid γ)

end Read
end GlobalTheory.SeriesTie.ModelGood

open GlobalTheory.SeriesTie.ModelGood in
theorem GlobalTheory.SeriesTie.rd_good_model : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∃ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      Y.Z.rd i j b x = (Y.Z.ν i j b)⁻¹ • (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) := by
  intro D X E Y i j b x hx
  obtain ⟨f, -, rfl⟩ := hx
  have hidem : ∀ z, Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b z) = Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i ((j : ℕ) + 1) b z :=
    fun z => by rw [← Module.End.mul_apply, Formalism.MainNotions.IntegralHeckeForms.eG, ← map_mul, D.nexp.eAlg_idem]
  refine ⟨mv Y.YS Y.Z.good i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b f), ⟨?_, ?_⟩, ?_⟩
  · have h := LinearMap.mem_range_self (X.R.HW j (sg0 D X.A3.A)).e
      (mv Y.YS Y.Z.good i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b f))
    rw [(X.char.models.HW j _).2.1] at h
    exact h
  · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply]
    rw [← mv_eG Y.YS Y.Z.good i j b X.unif X.idem, hidem]
  · change (Y.Z.ν i j b)⁻¹ • evK Y.YS X.geo.v₀ Y.Z.good i j b _ = _
    exact congrArg _ (evK_eq Y.YS Y.Z.good i j b X.geo.v₀ _)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_form_reading_eq_good_model_vector_evaluation : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∃ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      Y.Z.rd i j b x = (Y.Z.ν i j b)⁻¹ • (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) := by
  atlas_forward_decl GlobalTheory.SeriesTie.rd_good_model
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TypeRead

theorem actG_eG (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (u : G0g D.nd) (y : D.nexp.Fm i j b) :
    D.nexp.actG i j b u (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b y) = Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b (D.nexp.actG i j b u y) := by
  have h := congrArg (fun z => MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) z y)
    (D.nexp.eAlg_central i b (MonoidAlgebra.single u 1))
  simp only [map_mul, MonoidAlgebra.lift_single, one_smul, Module.End.mul_apply] at h
  exact h.symm

theorem finite_group_acts_on_good_type_form_by_character (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (x : D.nexp.Fm i j b) (hx : x ∈ V0 D.nexp i j b)
    (u : G0g D.nd) (hu : u ∈ D.nexp.U) :
    D.nexp.actG i j b u x = ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • x := by
  obtain ⟨f, hf, rfl⟩ := hx
  have hf' := (Submodule.mem_iInf _).1 hf ⟨u, hu⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hf'
  rw [actG_eG]
  change Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b ((D.nexp.actG i j b (⟨u, hu⟩ : D.nexp.U) : _ ≃ₗ[_] _) f) = _
  erw [hf']
  simp

end GlobalTheory.TypeRead

open GlobalTheory.TypeRead in

theorem GlobalTheory.TypeRead.rd_mul_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
      Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
      Y.Z.rd i j b x (g * κ) = Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
        Y.Z.rd i j b x g := by
  intro D X E Y i j b x hx u hu κ hκ g
  have hA : ActRead (Y.Z.rd i j b) :=
    actRead_realRd D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _ Y.Z.pin X.unif
      X.char.models.HW
  rw [← hA u κ hκ x g, finite_group_acts_on_good_type_form_by_character D i _ b x hx u hu, map_smulₛₗ]
  rfl
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_type_form_reading_right_translate_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
      Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
      Y.Z.rd i j b x (g * κ) = Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
        Y.Z.rd i j b x g := by
  atlas_forward_decl GlobalTheory.TypeRead.rd_mul_lift
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.RankOnto

theorem sumOnto_of_goodRange : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) → ∀ i, BaseTup Y i → SumOnto Y.Z.rd i := by
  intro D X E Y hG i hB j b x hx
  obtain ⟨w, hw, hrd⟩ := GlobalTheory.T.good_form_reading_eq_good_model_vector_evaluation D X E Y i j b x hx
  have hν : Y.Z.ν i j b ≠ 0 := (Y.Z.scalar i j b).ne
  have hT := GlobalTheory.T.good_type_form_reading_right_translate_lift D X E Y i j b x hx
  have hφ : (X.R.HW j (Formalism.IndefR.Links.sg0 D X.A3.A)).e w (X.geo.v₀ j _) = Y.Z.ν i j b • Y.Z.rd i j b x := by
    rw [hrd, smul_smul, mul_inv_cancel₀ hν, one_smul]
  obtain ⟨F, hF, hsum⟩ := GlobalTheory.T.goodModelVector_eq_classSum_baseLevel D X E Y hG i hB j b w hw (fun u hu κ hκ g => by
    rw [hφ, Pi.smul_apply, Pi.smul_apply, hT u hu κ hκ g, smul_eq_mul, smul_eq_mul]; ring)
  refine ⟨(Y.Z.ν i j b)⁻¹ • F, Submodule.smul_mem _ _ hF, ?_⟩
  rw [map_smul, ← hsum, hrd]

end GlobalTheory.RankOnto
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodForms_classSums_of_projectedLift_range : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) → ∀ i, BaseTup Y i → SumOnto Y.Z.rd i := by
  atlas_forward_decl GlobalTheory.RankOnto.sumOnto_of_goodRange
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.MainNotions.IntegralHeckeForms
open Formalism.IndefR.Links
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TieRank
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin
variable {O O' V : Type} [CommRing O] [IsDomain O] [CommRing O'] [Algebra O O'] [AddCommGroup V]
  [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]

variable (O') in

def scR (a : FractionRing O) : O' ⊗[O] V →ₗ[O'] O' ⊗[O] V :=
  ((a • LinearMap.id : Module.End (FractionRing O) V).restrictScalars O).baseChange O'

end Lin

section Onto
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

end Onto

section Comparison₂
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Comparison₂

section Tie2
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Tie2

section Main
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Main

section Target
open GlobalTheory.TwInputs GlobalTheory.SeriesTie Formalism.MainNotions

theorem faithful_serSide {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m)
    (b : Bool) : Faithful (Y.Z.rd i j b) :=
  realRd_faithful D X.Γ X.Pl0 X.I0 X.T X.A3 _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b (Y.Z.ν i j b)
    (Y.Z.scalar i j b).ne X.unif X.char.models.HW (Y.Z.vec j) ((GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)

theorem rank_of_ties : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ i,
    BaseTup Y i → (∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
    FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  intro hP D X E Y i hB hR
  have hG : ∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t :=
    GlobalTheory.AdSpan.goodRangeAt X.R.toRealDat hP X.size X.char.lev X.char.grp.record X.char.fam X.char.models X.char.thP
  exact GlobalTheory.T.averaged_series_full_rank_of_complex_span_good D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.tie (faithful_serSide X Y) E i (fun j b => (Y.Z.rat (hR j b)).1)
    (fun j hj b a => Y.all i j hj b a) (GlobalTheory.T.goodForms_spanned_by_thetaSeries_of_classSums D Y.Z.ρ Y.Z.good Y.Z.rd i (GlobalTheory.T.goodForms_classSums_of_projectedLift_range D X E Y hG i hB))

end Target

end GlobalTheory.TieRank

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullRank_thetaSeries_forms_of_rational_scalars : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ i, BaseTup Y i → (∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  atlas_forward_decl GlobalTheory.TieRank.rank_of_ties
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published

namespace GlobalTheory.ExportClose

open Classical in

theorem exportAt_of_bundles : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (X : RealSide D) (Y : SerSide X (twEOf xd)) (G : GalSide D), (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → GlobalTheory.TripleLocal.GalHodge D G.wd → LocalSituation.Conclusion5 D → IsGalois ℚ ↥D.LL0 → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) → NChTie D nch → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)) → GlobalTheory.Mem.Top.ExportAt D nch xd := by
  intro hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 hGW hRC hDec hCh1 hArt hTor D nch xd X Y G hRat hXi hHk hHodge h5 hGal hRoots hTie hBase
  obtain ⟨N0, hI⟩ := GlobalTheory.T.admT4_of_rational_rows hCh1 hArt hTor D X (twEOf xd) Y G hRat hXi hHk hHodge hRoots
  have hW : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → D.ntw.NonzeroIndexPlace (nch.twI w) :=
    GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice D nch hTie hGal
  let S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b) := fun i j b =>
    if h : D.ntw.NonzeroIndexPlace i ∧ j ∈ Finset.Icc 1 D.R.m then
      Classical.choose (GlobalTheory.T.exists_basis_averaged_series_of_class_sums D (twEOf xd) hI.t4 i h.1 j h.2 b) else ∅
  refine ⟨N0, S, fun i hi => ?_, fun w hw => ⟨hI.hyp _ (hW w hw), ?_, ?_⟩⟩
  · exact GlobalTheory.TwExportTop.twistAllPowers_of_galoisCohomology_classField hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 hGW hRC D (twEOf xd) N0 h5
      hI.a1 hI.a2 hI.a8 hI.good hI.sig hI.a9 hI.a10 hI.univChar hI.off hI.rel hI.l3 hI.t4 hI.type hI.univ hI.supG
      hI.supFull hI.supHk hI.commG hI.comm hI.ss i hi
  · intro j hj b
    exact GlobalTheory.T.fullRank_thetaSeries_forms_of_rational_scalars hDec D X (twEOf xd) Y (nch.twI w) (hBase w hw) (hRat _ (hW w hw)) j hj b
  · intro j hj b
    have h : D.ntw.NonzeroIndexPlace (nch.twI w) ∧ j ∈ Finset.Icc 1 D.R.m := ⟨hW w hw, hj⟩
    show IntegralHeckeForms.BasisOf D.nexp (nch.twI w) j b (IntegralHeckeForms.SgJ D.nexp (twEOf xd) (nch.twI w) j b) (S (nch.twI w) j b)
    simp only [S, dif_pos h]
    exact Classical.choose_spec (GlobalTheory.T.exists_basis_averaged_series_of_class_sums D (twEOf xd) hI.t4 _ h.1 j h.2 b)

end GlobalTheory.ExportClose
end
