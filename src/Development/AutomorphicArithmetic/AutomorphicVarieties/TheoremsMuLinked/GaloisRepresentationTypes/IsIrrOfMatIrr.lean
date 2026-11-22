module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.RigPtOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CoefIs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CoefEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ValIntLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CRealEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.LocCFT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.SgnEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ProModularRingExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.PhiAll
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.ContinuousKap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.IsFrobSq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.TorsionOrderFrobenius.QuadMu
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ChebQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.AdDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep3
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.EqOneOfNear
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.MatrixIrreducibility.IrrOfMatIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LkMarks
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CplFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ContinuousHom
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StationaryPhaseModel

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th

namespace UpperTheory.V.Th.End3

open UpperTheory.V.U3 UpperTheory.V.Base

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing

attribute [local instance] tf

theorem algClo (L Ω : Type) [Field L] [CharZero L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩

theorem cyc_cont (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  (Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
    (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)

theorem isAut_iso {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {n : ℕ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.IsAut ι r) (e : Af.RepIso r r') (hi : Af.IsIrr r') :
    Af.IsAut ι r' := by
  obtain ⟨sat, inf, hc, hreg, hatt⟩ := h
  exact ⟨sat, inf, hc, hreg, (Af.Bc.irrBasic.1 _ Unit _ n _).2.1 hi,
    hatt.2.mono fun w ⟨B, hB, h⟩ => ⟨B, hB, h.of_iso e⟩⟩

theorem freeAt_iso {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : FreeAt l r) (e : Af.RepIso r r') : FreeAt l r' := by
  intro A hA
  obtain ⟨g, hg, h1, α, h2, h3⟩ := h A hA
  obtain ⟨a, ha⟩ := e
  refine ⟨g, hg, h1, α, h2, ?_⟩
  rw [← h3]
  show (r' g).val.charpoly = (r g).val.charpoly
  rw [ha, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem h1fZero_equiv {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {C V V' : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
    [AddCommGroup V'] [Module C V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] C V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul C V']
    (ρ : Representation C (G F Ω) V) (ρ' : Representation C (G F Ω) V') (f : V ≃ₗ[C] V') (hc : Continuous f)
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (h : Af.BlochKatoSelmerVanishes l ρ') : Af.BlochKatoSelmerVanishes l ρ := by
  intro c hz hbk
  obtain ⟨hcc, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 hz
  have hcont : Continuous (fun g => f (c g)) := hc.comp hcc
  have hz' : (fun g => f (c g)) ∈ Z1 ρ' := (mem_Z1_iff_cocycle _ _).2 ⟨hcont, fun g g' => by rw [hcoc, map_add (f := _), hf]⟩
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 (h _ hz'
    (X.Kato.bkMap l F Ω _ _ _ _ ρ ρ' (f.toLinearMap.restrictScalars ℚ_[l]) hf c hcont hbk))
  obtain ⟨m', rfl⟩ := f.surjective m
  refine (mem_coboundaries1 _ _).2 ⟨m', fun g => f.injective ?_⟩
  rw [map_sub, hf]
  exact hm g

theorem h1fZero_conjBy {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {m : ℕ}
    (r : G F Ω →* GG (m := m) (R := PadicAlgCl l)) (h : GL (Fin m) (PadicAlgCl l))
    (H : Af.BlochKatoSelmerVanishes l (adRep (conjBy h r))) :
    Af.BlochKatoSelmerVanishes l (adRep r) := by
  let f : Matrix (Fin m) (Fin m) (PadicAlgCl l) ≃ₗ[PadicAlgCl l] Matrix (Fin m) (Fin m) (PadicAlgCl l) :=
    LinearMap.GeneralLinearGroup.toLinearEquiv ((GG.ad m (PadicAlgCl l)).toHomUnits (GG.ofGL h))
  have hf : ∀ X, f X = GG.ad m (PadicAlgCl l) (GG.ofGL h) X := fun X => rfl
  refine h1fZero_equiv _ _ f ?_ (fun g X => ?_) H
  · have : (f : _ → _) = fun X => h.val * X * (h⁻¹).val := funext fun X => by
      rw [hf, GG.ad_apply, GG.adFun, if_pos (by rfl)]
      rfl
    rw [this]
    fun_prop
  · rw [hf, hf]
    show _ = GG.ad m (PadicAlgCl l) (GG.ofGL h * r g * (GG.ofGL h)⁻¹) _
    rw [GG.ad_apply, GG.ad_apply, GG.ad_apply, ← GG.adFun_mul, inv_mul_cancel_right, GG.adFun_mul]
    rfl

private theorem congOne_iff {C : Type} [CommRing C] (I : Ideal C) (h : GL (Fin 3) C) :
    CongOne I h ↔ Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) h = 1 := by
  constructor
  · intro e
    ext a b
    have := Ideal.Quotient.eq.2 (e a b)
    refine this.trans ?_
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · intro e a b
    refine Ideal.Quotient.eq.1 ?_
    refine (congrArg (fun x : GL (Fin 3) (C ⧸ I) => x.val a b) e).trans ?_
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem map_conjBy {G R S : Type} [Group G] [CommRing R] [CommRing S] {m : ℕ} (f : R →+* S) (h : GL (Fin m) R)
    (r : G →* GG (m := m) (R := R)) :
    (GG.map f).comp (conjBy h r) = conjBy (Matrix.GeneralLinearGroup.map f h) ((GG.map f).comp r) := by
  have e : GG.map f (GG.ofGL h) = GG.ofGL (Matrix.GeneralLinearGroup.map f h) := rfl
  refine MonoidHom.ext fun g => ?_
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e]

theorem conjBy_left {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG (m := m) (R := R)) (g : G) :
    (conjBy h r g).left = h * (r g).left * sgnAct m R (r g).right h⁻¹ := by
  simp [conjBy]

theorem conjBy_right {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG (m := m) (R := R)) (g : G) :
    (conjBy h r g).right = (r g).right := by
  simp [conjBy]

private theorem conjBy_conjBy {C D : Type} [CommRing C] [Group D] (h h' : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C)) :
    conjBy (h * h')⁻¹ (conjBy h r) = conjBy h'⁻¹ r := by
  refine MonoidHom.ext fun g => ?_
  show GG.ofGL _ * (GG.ofGL h * r g * (GG.ofGL h)⁻¹) * (GG.ofGL _)⁻¹ = GG.ofGL _ * r g * (GG.ofGL _)⁻¹
  simp only [map_inv, map_mul, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

theorem ordPt_conj {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ g₂ : G ℚ Ω} {B : ValuationSubring Ω} {A : Type} [CommRing A] [IsLocalRing A]
    [Algebra O A] {r : G ℚ Ω →* GG (m := 3) (R := A)} (hr : Pr.OrdPt l η Ψ σ g₁ B r)
    (hη : IsLocallyConstant η) (h : GL (Fin 3) A)
    (hh : CongOne (maximalIdeal A) h) (hN : Normalised σ g₂ (conjBy h r)) : Pr.OrdPt l η Ψ σ g₂ B (conjBy h r) := by
  refine ⟨⟨fun g => (conjBy_right h r g).trans (hr.red.mult g), fun g a b => ?_⟩, fun n => ?_, hN,
    fun B' h1 s h2 h3 h4 => ?_, ?_⟩
  · have e := DFunLike.congr_fun (map_conjBy (Ideal.Quotient.mk (maximalIdeal A)) h r) g
    rw [(congOne_iff _ _).1 hh] at e
    have e2 : (conjBy h r g).mat.map (Ideal.Quotient.mk (maximalIdeal A)) = (r g).mat.map (Ideal.Quotient.mk (maximalIdeal A)) := by
      refine (congrArg GG.mat e).trans ?_
      rw [GG.mat, conjBy_left, inv_one, map_one, one_mul, mul_one]
      rfl
    refine Ideal.Quotient.eq.1 ((congrFun (congrFun e2 a) b).trans ?_)
    exact Ideal.Quotient.eq.2 (hr.red.red g a b)
  · have := ((hr.cont n).prodMk hη).comp fun p : Matrix (Fin 3) (Fin 3) (A ⧸ maximalIdeal A ^ n) × ℤˣ =>
      h.val.map (Ideal.Quotient.mk (maximalIdeal A ^ n)) * p.1 *
        (sgnAct 3 A p.2 h⁻¹).val.map (Ideal.Quotient.mk (maximalIdeal A ^ n))
    convert this using 1
    funext g
    rw [GG.mat, conjBy_left, hr.red.mult g, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
    rfl
  · show GG.ofGL h * r s * (GG.ofGL h)⁻¹ = 1
    rw [hr.away B' h1 s h2 h3 h4, mul_one, mul_inv_cancel]
  · obtain ⟨h', h1, h2, h3⟩ := hr.ord
    have e : (conjBy h r).comp (Dec (F := ℚ) B).subtype = conjBy h (r.comp (Dec (F := ℚ) B).subtype) := rfl
    refine ⟨h * h', (congOne_iff _ _).2 ?_, ?_, ?_⟩
    · rw [map_mul, (congOne_iff _ _).1 hh, (congOne_iff _ _).1 h1, mul_one]
    · rw [e, conjBy_conjBy]; exact h2
    · rw [e, conjBy_conjBy]; exact h3

private theorem map_tor {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (t : Aˣ) :
    Matrix.GeneralLinearGroup.map f (tor A t) = tor B (Units.map f.toMonoidHom t) := by
  apply Units.ext
  show (tor A t : Matrix (Fin 3) (Fin 3) A).map f = _
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  rw [← map_zpow]
  rfl

theorem ordPt_renorm {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ g₂ : G ℚ Ω} {B : ValuationSubring Ω} {A : Type} [CommRing A] [IsLocalRing A]
    [Algebra O A] [IsAdicComplete (maximalIdeal A) A] {r : G ℚ Ω →* GG (m := 3) (R := A)}
    (hr : Pr.OrdPt l η Ψ σ g₁ B r) (hη : IsLocallyConstant η) (h2 : IsUnit (2 : O)) (hM : Marks η Ψ σ g₂) :
    ∃ h : GL (Fin 3) A, CongOne (maximalIdeal A) h ∧ Pr.OrdPt l η Ψ σ g₂ B (conjBy h r) := by
  obtain ⟨h, hh, hN⟩ := exists_normalised η ((Units.map ((residue A).comp (algebraMap O A)).toMonoidHom).comp Ψ) σ g₂ r
    (by simpa [map_ofNat] using h2.map (algebraMap O A))
    ⟨hM.csq, hM.ηc, by simp [hM.Ψc], hM.ηg, by simpa using hM.Ψg.map ((residue A).comp (algebraMap O A))⟩ (by
      refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) (hr.red.mult g)
      rw [unitaryThreeReflection_left, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_tor]
      ext a b
      exact Ideal.Quotient.eq.2 (hr.red.red g a b))
  exact ⟨h, hh, ordPt_conj hr hη h hh hN⟩

private theorem charpoly_pow {K : Type} [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ)
    (hM : M.charpoly = ∏ i, (X - C (a i : K))) (ha : Pr.FreeRatios a) (d : ℕ) (hd : 0 < d) :
    (M ^ d).charpoly = ∏ i, (X - C ((a i : K) ^ d)) := by
  have hinj : Function.Injective (fun i => (a i : K) ^ d) := by
    intro i j hij
    by_contra hne
    apply ha i j hne d hd
    apply Units.ext
    simpa using hij
  have hroot : ∀ i, (M ^ d).charpoly.IsRoot ((a i : K) ^ d) := by
    intro i
    rw [← Matrix.mem_spectrum_iff_isRoot_charpoly]
    apply spectrum.pow_mem_pow
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hM, Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hdvd : (∏ i, (X - C ((a i : K) ^ d))) ∣ (M ^ d).charpoly := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact Polynomial.pairwise_coprime_X_sub_C hinj hij
    · intro i _
      exact Polynomial.dvd_iff_isRoot.2 (hroot i)
  have hmon : (∏ i, (X - C ((a i : K) ^ d))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic _) hdvd
  rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]

theorem freeAt_res {F L Ω : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L] [Algebra F Ω]
    [Algebra L Ω] [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : G F Ω →* GL (Fin n) (Qbar l)} (h : FreeAt l r) : FreeAt l (r.comp (galEmb F L Ω)) := by
  intro A hA
  obtain ⟨g, hg, h1, α, h2, h3⟩ := h A hA
  obtain ⟨d, hd, -, hm⟩ := (galOf F L Ω).exists_pow_mem_of_index_ne_zero
    (by rw [(galEmbTop F L Ω).2.2]; exact Module.finrank_pos.ne') g
  rw [← range_galEmb] at hm
  obtain ⟨t, ht⟩ := hm
  refine ⟨t, ?_, ?_, fun i => α i ^ d, fun i j hij m hm => ?_, ?_⟩
  · have := pow_mem hg d
    rw [← ht] at this
    exact this
  · show cycZ F Ω l (galEmb F L Ω t) = 1
    rw [ht, map_pow, h1, one_pow]
  · rw [← pow_mul, ← pow_mul]
    exact h2 i j hij _ (Nat.mul_pos hd hm)
  · show (r (galEmb F L Ω t)).val.charpoly = _
    rw [ht, map_pow, Units.val_pow_eq_pow_val]
    simp only [Units.val_pow_eq_pow_val]
    exact charpoly_pow _ α h3 h2 d hd

theorem sub_facts {l : ℕ} [Fact l.Prime] (c : Coef l) (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A]
    [Module.Finite c.O A] : IsAdicComplete (maximalIdeal A) A ∧ IsLocalHom (algebraMap c.O A) ∧
      ∀ (Γ : Type) [TopologicalSpace Γ] (f : Γ → A), Alg.AdicCont (maximalIdeal A) f →
        Continuous fun g => (f g : PadicAlgCl l) := by
  let c' : Coef l := ⟨A.restrictScalars ℤ_[l], ‹IsDiscreteValuationRing A›,
    (Module.Finite.trans (R := ℤ_[l]) c.O A :)⟩
  haveI := (abelian₂.dvr_finite l c.O).1
  refine ⟨AlgebraTools.Conn.cplFinite (A := c.O) _ (maximalIdeal.isMaximal A).ne_top, Db.locHom c A, fun Γ _ f hf => ((UpperTheory.integrality_of_norm_coefficients l).2 c' Γ f).1 hf⟩

theorem matIrr_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {U : Subgroup Γ} {a a' : Γ → Matrix (Fin n) (Fin n) k}
    (H : MatIrr U a) (h : GL (Fin n) k) (e : ∀ g ∈ U, a' g = h.val * a g * (h⁻¹).val) : MatIrr U a' :=
  _root_.UpperTheory.Reformulated.B.StationaryPhaseModel.matIrr_conj H h e

section Abs

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {K L : Type} [Field K] [NumberField K]
  [IsCMField K] [Algebra K Ω] [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {σ : G ℚ Ω} {R : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)} {ρ : G K Ω →* GL (Fin 3) (Qbar l)}

end Abs

end UpperTheory.V.Th.End3

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
attribute [local instance 10000] IsDiscreteValuationRing.toIsLocalRing

