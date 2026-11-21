import Mathlib
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ThetaSeriesDatumMemLevelTypeForms

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
