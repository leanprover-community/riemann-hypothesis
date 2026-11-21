import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEQuotientMapSpanSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDepthTwoHullOfEtalePuncturedSpectrum
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomOfEtalePunctured
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEThreeOfFreeRegularLocal

section
section
open IsLocalRing

namespace GlobalTheory

theorem isSMulRegular_of_etale_punctured_of_depth_pos :
    ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [Algebra R A]
      [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 1 →
      (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      ∀ f : R, f ≠ 0 → IsSMulRegular A f := by
  intro R A _ _ _ _ _ hdepth het f hf

  obtain ⟨rs, hlen, hmem, hreg⟩ := hdepth
  obtain ⟨w, hw⟩ : ∃ w, rs = [w] := List.length_eq_one_iff.mp hlen
  subst hw
  have hwm : w ∈ maximalIdeal R := hmem w (by simp)
  have hwr : IsSMulRegular A w := ((RingTheory.Sequence.isRegular_cons_iff A w []).mp hreg).1
  have hmax : maximalIdeal R ∉ associatedPrimes R A := ReciprocityTheory.CA.max_not_mem_ass_of_reg hwm hwr

  refine IsSMulRegular.of_right_eq_zero_of_smul fun a ha => ?_
  by_contra ha0
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R a ha0
  have hfP : f ∈ P := hle (Submodule.mem_colon_singleton.mpr (by simpa using ha))
  obtain ⟨hPprime, b, hb⟩ := Submodule.isAssociatedPrime_iff.mp hP
  haveI := hPprime
  have hPm : P ≠ maximalIdeal R := fun h => hmax (h ▸ hP)
  haveI := het P hPm
  set L := Localization.AtPrime P
  haveI : Module.Free L (TensorProduct R L A) := Module.free_of_flat_of_isLocalRing
  have hfb : f • b = 0 := by
    have : f ∈ (⊥ : Submodule R A).colon {b} := hb ▸ hfP
    simpa using Submodule.mem_colon_singleton.mp this
  have hloc : IsLocalizedModule P.primeCompl (TensorProduct.mk R L A 1) :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl L _).mpr (TensorProduct.isBaseChange R A L)
  have hfL : algebraMap R L f ≠ 0 := by
    intro h0
    apply hf
    exact (IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors P)) (by simpa using h0)
  have h1 : (1 : L) ⊗ₜ[R] b = 0 := by
    have : algebraMap R L f • ((1 : L) ⊗ₜ[R] b) = 0 := by
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, hfb, TensorProduct.tmul_zero]
    exact (smul_eq_zero.mp this).resolve_left hfL
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff P.primeCompl (TensorProduct.mk R L A 1)).mp h1
  have htP : (t : R) ∈ P := by
    have : (t : R) ∈ (⊥ : Submodule R A).colon {b} :=
      Submodule.mem_colon_singleton.mpr (by simpa [Submonoid.smul_def] using ht)
    exact hb ▸ this
  exact t.2 htP

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' : ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 1 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ f : R, f ≠ 0 → IsSMulRegular A f := by
  atlas_forward_decl GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos
end

section
section
open IsLocalRing

namespace GlobalTheory

theorem etale_quotient_of_etale_punctured :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] (f : R)
      [IsLocalRing (R ⧸ Ideal.span {f})],
      (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      ∀ (P : Ideal (R ⧸ Ideal.span {f})) [P.IsPrime], P ≠ maximalIdeal (R ⧸ Ideal.span {f}) →
        Algebra.Etale (Localization.AtPrime P)
          (TensorProduct (R ⧸ Ideal.span {f}) (Localization.AtPrime P)
            (A ⧸ (Ideal.span {f}).map (algebraMap R A))) := by
  intro R A _ _ _ _ f _ H P _ hP
  set S := R ⧸ Ideal.span {f}
  set T := Localization.AtPrime P
  set p : Ideal R := P.comap (algebraMap R S) with hpdef
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  have hp : p ≠ maximalIdeal R := by
    intro h
    apply hP
    refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : r ∈ maximalIdeal R := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_maximalIdeal _).1 hx (hu.map _)
    rw [← h] at hr
    exact hr
  haveI := H p hp
  let φ : Localization.AtPrime p →+* T := Localization.localRingHom p P (algebraMap R S) rfl
  letI : Algebra (Localization.AtPrime p) T := φ.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime p) T :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      show algebraMap R T r = φ (algebraMap R _ r)
      rw [Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R S T])
  haveI : Algebra.Etale T (TensorProduct (Localization.AtPrime p) T
      (TensorProduct R (Localization.AtPrime p) A)) :=
    Algebra.Etale.baseChange _ _ _
  let e1 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p) T T A
  let e2 := Algebra.TensorProduct.cancelBaseChange R S T T A
  let e3 : (A ⧸ (Ideal.span {f}).map (algebraMap R A)) ≃ₐ[S] TensorProduct R S A :=
    AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (Ideal.span {f})).restrictScalars R).trans
        (Algebra.TensorProduct.comm R A S))
  let e4 : TensorProduct S T (A ⧸ (Ideal.span {f}).map (algebraMap R A)) ≃ₐ[T]
      TensorProduct S T (TensorProduct R S A) :=
    Algebra.TensorProduct.congr AlgEquiv.refl e3
  exact Algebra.Etale.of_equiv (e1.trans (e4.trans e2).symm)

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_quotient_of_etale_punctured' : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] (f : R) [IsLocalRing (R ⧸ Ideal.span {f})], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ (P : Ideal (R ⧸ Ideal.span {f})) [P.IsPrime], P ≠ maximalIdeal (R ⧸ Ideal.span {f}) → Algebra.Etale (Localization.AtPrime P) (TensorProduct (R ⧸ Ideal.span {f}) (Localization.AtPrime P) (A ⧸ (Ideal.span {f}).map (algebraMap R A))) := by
  atlas_forward_decl GlobalTheory.etale_quotient_of_etale_punctured
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_etale_at_height_one_primes : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A], ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  first | exact @GlobalTheory.PurityDisc.etale_of_etale_height_one | exact GlobalTheory.PurityDisc.etale_of_etale_height_one | (intros; apply GlobalTheory.PurityDisc.etale_of_etale_height_one <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaleLiftQuot

open IsLocalRing TensorProduct

theorem ker_le_jacobson_of_factor {S T F : Type} [CommRing S] [CommRing T] [FunLike F S T]
    [RingHomClass F S T] (g : F)
    (h : ∀ n : Ideal S, n.IsMaximal → ∃ τ : T →+* S ⧸ n, ∀ x, τ (g x) = Ideal.Quotient.mk n x) :
    RingHom.ker g ≤ (⊥ : Ideal S).jacobson := by
  intro x hx
  refine GlobalTheory.mem_jacobson_bot_of_forall_isMaximal fun n hn ↦ ?_
  obtain ⟨τ, hτ⟩ := h n hn
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hτ, RingHom.mem_ker.1 hx, map_zero]

def residueToQuot (R : Type) [CommRing R] [IsLocalRing R] {S : Type} [CommRing S] [Algebra R S]
    [Module.Finite R S] (n : Ideal S) [n.IsMaximal] : ResidueField R →ₐ[R] S ⧸ n :=
  Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R _) fun a ha ↦ by
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite n] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha

variable {R : Type} [CommRing R] [HenselianLocalRing R] (I : Ideal R)

abbrev algQuotResidue (hI : I ≤ maximalIdeal R) : Algebra (R ⧸ I) (ResidueField R) :=
  (Ideal.Quotient.factor hI : R ⧸ I →+* R ⧸ maximalIdeal R).toAlgebra

theorem exists_lift (hI : I ≤ maximalIdeal R) (E : Type) [CommRing E] [Algebra (R ⧸ I) E] [Module.Finite (R ⧸ I) E]
    [Algebra.Etale (R ⧸ I) E] :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Module.Finite R B ∧ Algebra.Etale R B ∧
      Nonempty ((B ⧸ I.map (algebraMap R B)) ≃ₐ[R ⧸ I] E) := by
  letI := algQuotResidue I hI
  have : IsScalarTower R (R ⧸ I) (ResidueField R) := .of_algebraMap_eq fun _ ↦ rfl
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  have hk : Function.Surjective (algebraMap (R ⧸ I) (ResidueField R)) := fun y ↦ by
    obtain ⟨x, rfl⟩ := residue_surjective y
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  letI : Algebra R E := ((algebraMap (R ⧸ I) E).comp (algebraMap R (R ⧸ I))).toAlgebra
  have : IsScalarTower R (R ⧸ I) E := .of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite R E := .trans (R ⧸ I) E
  obtain ⟨B, _, _, hBfin, hBet, ⟨e⟩⟩ :=
    GlobalTheory.exists_etale_lift_of_etale.{0, 0} R (ResidueField R ⊗[R ⧸ I] E)
  refine ⟨B, inferInstance, inferInstance, hBfin, hBet, ?_⟩
  have : IsScalarTower R (R ⧸ I) (ResidueField R ⊗[R ⧸ I] E) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R (R ⧸ I) (ResidueField R ⊗[R] B) := .of_algebraMap_eq fun _ ↦ rfl

  let πE : E →ₐ[R ⧸ I] ResidueField R ⊗[R ⧸ I] E := Algebra.TensorProduct.includeRight
  have hπE : Function.Surjective πE := Algebra.TensorProduct.includeRight_surjective _ hk
  have hkerE : RingHom.ker πE ≤ (⊥ : Ideal E).jacobson := by
    refine ker_le_jacobson_of_factor πE fun n hn ↦ ?_
    let σ := (residueToQuot R n).extendScalarsOfSurjective hsurj
    let τ := Algebra.TensorProduct.lift σ (Ideal.Quotient.mkₐ (R ⧸ I) n) fun _ _ ↦ .all _ _
    exact ⟨τ.toRingHom, fun x ↦ by simp [τ, πE]⟩

  let J := I.map (algebraMap R B)
  have hJ : ∀ (T : Type) [CommRing T] [Algebra R T] (g : B →ₐ[R] T),
      (∀ r ∈ I, algebraMap R T r = 0) → ∀ a ∈ J, g a = 0 := fun T _ _ g hT a ha ↦ by
    have : J ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
      exact hT r hr
    exact this ha
  have hres : ∀ r ∈ I, algebraMap R (ResidueField R ⊗[R] B) r = 0 := fun r hr ↦ by
    have h0 : algebraMap R (ResidueField R) r = 0 := (residue_eq_zero_iff r).2 (hI hr)
    rw [IsScalarTower.algebraMap_apply R (ResidueField R), h0, map_zero]
  let πB₀ : B ⧸ J →ₐ[R] ResidueField R ⊗[R] B :=
    Ideal.Quotient.liftₐ J Algebra.TensorProduct.includeRight (hJ _ _ hres)
  let πB : B ⧸ J →ₐ[R ⧸ I] ResidueField R ⊗[R] B := πB₀.extendScalarsOfSurjective hsurj
  have hπB_mk : ∀ b : B, πB (Ideal.Quotient.mk J b) = 1 ⊗ₜ b := fun b ↦ rfl
  have hπB : Function.Surjective πB := fun y ↦ by
    obtain ⟨b, rfl⟩ := Algebra.TensorProduct.includeRight_surjective B residue_surjective y
    exact ⟨Ideal.Quotient.mk J b, rfl⟩
  have hkerB : RingHom.ker πB ≤ (⊥ : Ideal (B ⧸ J)).jacobson := by
    refine ker_le_jacobson_of_factor πB fun n hn ↦ ?_
    let τ := Algebra.TensorProduct.lift (residueToQuot R n)
      ((Ideal.Quotient.mkₐ R n).comp (Ideal.Quotient.mkₐ R J)) fun _ _ ↦ .all _ _
    refine ⟨τ.toRingHom, fun x ↦ ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hπB_mk]
    simp [τ]

  obtain ⟨φ, hφ⟩ := (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R) (A := B)
    (πE.restrictScalars R) hπE hkerE).2
    ((e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight)
  have hφb : ∀ b, πE (φ b) = e (1 ⊗ₜ b) := fun b ↦ congr($hφ b)

  obtain ⟨ψ, hψ⟩ := (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R ⧸ I) (A := E)
    πB hπB hkerB).2 ((e.symm.toAlgHom.restrictScalars (R ⧸ I)).comp πE)
  have hψx : ∀ x, πB (ψ x) = e.symm (πE x) := fun x ↦ congr($hψ x)
  have hEI : ∀ r ∈ I, algebraMap R E r = 0 := fun r hr ↦ by
    rw [IsScalarTower.algebraMap_apply R (R ⧸ I), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  let φ' : B ⧸ J →ₐ[R ⧸ I] E := (Ideal.Quotient.liftₐ J φ (hJ _ _ hEI)).extendScalarsOfSurjective hsurj
  have hφ'_mk : ∀ b, φ' (Ideal.Quotient.mk J b) = φ b := fun b ↦ rfl
  have key : ∀ y, πE (φ' y) = e (πB y) := fun y ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hφ'_mk, hφb, hπB_mk]
  have h1 : φ'.comp ψ = AlgHom.id (R ⧸ I) E := by
    refine (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R ⧸ I) (A := E)
      πE hπE hkerE).1 (AlgHom.ext fun x ↦ ?_)
    simp only [AlgHom.comp_apply, AlgHom.id_apply, key, hψx, AlgEquiv.apply_symm_apply]
  have h2 : ψ.comp φ' = AlgHom.id (R ⧸ I) (B ⧸ J) := by
    have H := (GlobalTheory.bijective_algHom_comp_of_etale_of_henselian R (k := R) (A := B)
      (πB.restrictScalars R) hπB hkerB).1
      (a₁ := (ψ.restrictScalars R).comp φ) (a₂ := Ideal.Quotient.mkₐ R J) (AlgHom.ext fun b ↦ by
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [hψx, hφb, AlgEquiv.symm_apply_apply, hπB_mk])
    refine AlgHom.ext fun y ↦ ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [AlgHom.comp_apply, AlgHom.id_apply, hφ'_mk]
    simpa using congr($H b)
  exact ⟨AlgEquiv.ofAlgHom φ' ψ h1 h2⟩

end GlobalTheory.EtaleLiftQuot

namespace GlobalTheory.EtaleLiftQuot

open IsLocalRing TensorProduct

theorem exists_finite_free_etale_lift : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    IsAdicComplete (maximalIdeal R) R → ∀ f ∈ maximalIdeal R, ∀ (E : Type) [CommRing E]
    [Algebra (R ⧸ Ideal.span {f}) E] [Module.Finite (R ⧸ Ideal.span {f}) E]
    [Algebra.Etale (R ⧸ Ideal.span {f}) E], ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B),
      Module.Finite R B ∧ Module.Free R B ∧ Algebra.Etale R B ∧
        Nonempty ((B ⧸ (Ideal.span {f}).map (algebraMap R B)) ≃ₐ[R ⧸ Ideal.span {f}] E) := by
  intro R _ _ _ hc f hf E _ _ _ _
  have : HenselianRing R (maximalIdeal R) := @IsAdicComplete.henselianRing R _ _ hc
  have : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  obtain ⟨B, _, _, h₁, h₂, h₃⟩ :=
    exists_lift (Ideal.span {f}) ((Ideal.span_singleton_le_iff_mem _).2 hf) E
  exact ⟨B, inferInstance, inferInstance, h₁, Module.free_of_flat_of_isLocalRing, h₂, h₃⟩

end GlobalTheory.EtaleLiftQuot
end
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_free_etale_lift_of_quotient_etale : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ f ∈ maximalIdeal R, ∀ (E : Type) [CommRing E] [Algebra (R ⧸ Ideal.span {f}) E] [Module.Finite (R ⧸ Ideal.span {f}) E] [Algebra.Etale (R ⧸ Ideal.span {f}) E], ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Module.Finite R B ∧ Module.Free R B ∧ Algebra.Etale R B ∧ Nonempty ((B ⧸ (Ideal.span {f}).map (algebraMap R B)) ≃ₐ[R ⧸ Ideal.span {f}] E) := by
  atlas_forward_decl GlobalTheory.EtaleLiftQuot.exists_finite_free_etale_lift
end

section
section
open IsLocalRing

namespace GlobalTheory

theorem injective_and_saturated_of_injective_mod_regular :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A B : Type) [CommRing A]
      [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] (f : R),
      f ∈ maximalIdeal R → IsSMulRegular B f → ∀ ψ : A →ₐ[R] B,
      (∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) →
        a ∈ (Ideal.span {f}).map (algebraMap R A)) →
      Function.Injective ψ ∧ ∀ b : B, f • b ∈ ψ.range → b ∈ ψ.range := by
  intro R _ _ _ A B _ _ _ _ _ f hf hreg ψ hψ

  have memA : ∀ a : A, a ∈ (Ideal.span {f}).map (algebraMap R A) → ∃ c : A, a = f • c := by
    intro a ha
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, hc⟩ := ha
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_comm]⟩
  have memB : ∀ b : B, f • b ∈ (Ideal.span {f}).map (algebraMap R B) := by
    intro b
    rw [Ideal.map_span, Set.image_singleton, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have key : ∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) → ∃ c : A, a = f • c :=
    fun a h => memA a (hψ a h)
  refine ⟨?_, ?_⟩
  ·
    set K : Submodule R A := LinearMap.ker ψ.toLinearMap with hK
    have hFG : K.FG := IsNoetherian.noetherian K
    have hle : K ≤ Ideal.span {f} • K := by
      intro a ha
      have ha0 : ψ a = 0 := ha
      obtain ⟨c, rfl⟩ := key a (by rw [ha0]; exact Submodule.zero_mem _)
      have hc : ψ c = 0 := by
        apply hreg
        change f • ψ c = f • (0 : B)
        rw [smul_zero, ← map_smul]
        exact ha0
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) hc
    have hjac : Ideal.span {f} ≤ Ideal.jacobson (⊥ : Ideal R) := by
      refine le_trans ?_ (maximalIdeal_le_jacobson _)
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hf
    have hK0 : K = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ K hFG hle hjac
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ K := ha
    rw [hK0] at this
    exact (Submodule.mem_bot R).1 this
  · intro b ⟨a, ha'⟩
    have ha : ψ a = f • b := ha'
    obtain ⟨c, rfl⟩ := key a (by rw [ha]; exact memB b)
    refine ⟨c, ?_⟩
    apply hreg
    change f • ψ c = f • b
    rw [← map_smul, ha]

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_and_saturated_of_injective_mod_regular' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A B : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] (f : R), f ∈ maximalIdeal R → IsSMulRegular B f → ∀ ψ : A →ₐ[R] B, (∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) → a ∈ (Ideal.span {f}).map (algebraMap R A)) → Function.Injective ψ ∧ ∀ b : B, f • b ∈ ψ.range → b ∈ ψ.range := by
  atlas_forward_decl GlobalTheory.injective_and_saturated_of_injective_mod_regular
end

section
section
open IsLocalRing

namespace GlobalTheory

theorem exists_prime_ne_maximalIdeal_of_one_le_ringKrullDim_quot
    (R : Type) [CommRing R] [IsLocalRing R] (f : R)
    (hdim : 1 ≤ ringKrullDim (R ⧸ Ideal.span {f})) :
    ∃ P : Ideal R, P.IsPrime ∧ f ∈ P ∧ P ≠ maximalIdeal R := by
  by_contra! hne
  have h0 : Ring.KrullDimLE 0 (R ⧸ Ideal.span {f}) := by
    refine Ring.krullDimLE_zero_iff.mpr fun Q hQ => ?_
    have hc : Q.comap (Ideal.Quotient.mk (Ideal.span {f})) = maximalIdeal R := by
      refine hne _ (Ideal.comap_isPrime _ _) ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
      exact Q.zero_mem
    have hmax := (maximalIdeal.isMaximal R).map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
      (by rw [← hc]; exact Ideal.comap_mono bot_le)
    rwa [← hc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hmax
  have := (Ring.krullDimLE_iff (n := 0)).mp h0
  have h10 := hdim.trans this
  norm_num at h10

theorem cokernel_torsion_of_finiteLength_mod : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (f : R), 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) → ∀ (A B : Type) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Module.Finite R B] (ψ : A →ₐ[R] B), (∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c) → ∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range := by
  intro R _ _ _ f hdim A B _ _ _ _ _ ψ ⟨k, hk⟩
  obtain ⟨P, hP, hfP, hPm⟩ := exists_prime_ne_maximalIdeal_of_one_le_ringKrullDim_quot R f hdim

  obtain ⟨x, hxk, hxP⟩ : ∃ x ∈ maximalIdeal R ^ k, x ∉ P := by
    by_contra! h
    have hle : maximalIdeal R ≤ P := hP.le_of_pow_le h
    exact hPm (le_antisymm (le_maximalIdeal hP.ne_top) hle)
  set N : Submodule R B := LinearMap.range ψ.toLinearMap
  set I : Ideal R := Ideal.span {f}
  let φ : Module.End R (B ⧸ N) := algebraMap R (Module.End R (B ⧸ N)) x
  have hφ : LinearMap.range φ ≤ I • ⊤ := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective N c
    obtain ⟨a, c', hac⟩ := hk x hxk b
    have : φ (Submodule.Quotient.mk b) = f • Submodule.Quotient.mk c' := by
      simp only [φ, Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, hac]
      have ha0 : Submodule.Quotient.mk (p := N) (ψ a) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨a, rfl⟩
      rw [Submodule.Quotient.mk_add, ha0, zero_add]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) Submodule.mem_top
  obtain ⟨p, hmon, -, hcoeff, hzero⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R φ I hφ
  refine ⟨p.eval x, ?_, ?_⟩
  · intro h0
    apply hxP
    apply hP.mem_of_pow_mem p.natDegree
    have hs : p.eval x ∈ P := h0 ▸ P.zero_mem
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_mul] at hs
    refine (P.add_mem_iff_right ?_).mp hs
    refine P.sum_mem fun i hi => P.mul_mem_right _ ?_
    have hi' : 0 < p.natDegree - i := Nat.sub_pos_of_lt (Finset.mem_range.mp hi)
    have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hfP
    exact hIP (Ideal.pow_le_self hi'.ne' (hcoeff i))
  · intro b
    have h1 : (Polynomial.aeval φ p) (Submodule.Quotient.mk b) = 0 := by rw [hzero]; rfl
    rw [show φ = algebraMap R _ x from rfl, Polynomial.aeval_algebraMap_apply,
      Module.algebraMap_end_apply, Polynomial.aeval_def] at h1
    change Polynomial.eval x p • Submodule.Quotient.mk (p := N) b = 0 at h1
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, ha⟩

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_torsion_of_finiteLength_mod_element : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (f : R), 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) → ∀ (A B : Type) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Module.Finite R B] (ψ : A →ₐ[R] B), (∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c) → ∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range := by
  atlas_forward_decl GlobalTheory.cokernel_torsion_of_finiteLength_mod
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem algebraTrace_map_of_cokernel_killed (S A B : Type) [CommRing S] [IsDomain S] [CommRing A]
    [Algebra S A] [Module.Free S A] [Module.Finite S A] [CommRing B] [Algebra S B]
    [Module.Free S B] [Module.Finite S B] (φ : A →ₐ[S] B) (hφ : Function.Injective φ)
    (s : S) (hs : s ≠ 0) (hr : ∀ b : B, s • b ∈ φ.range) (x : A) :
    Algebra.trace S B (φ x) = Algebra.trace S A x := by
  classical
  choose g hg using fun b => (AlgHom.mem_range φ).1 (hr b)
  let gl : B →ₗ[S] A :=
    { toFun := g
      map_add' := by
        intro b c
        apply hφ
        rw [map_add, hg, hg, hg, smul_add]
      map_smul' := by
        intro r b
        apply hφ
        rw [hg, RingHom.id_apply, map_smul, hg, smul_comm] }
  have h1 : φ.toLinearMap ∘ₗ gl = s • LinearMap.id := by
    ext b
    simp [gl, hg]
  have h2 : gl ∘ₗ φ.toLinearMap = s • LinearMap.id := by
    ext a
    apply hφ
    simp [gl, hg]
  have h3 : Algebra.lmul S B (φ x) ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ Algebra.lmul S A x := by
    ext a
    simp
  have key : s * Algebra.trace S B (φ x) = s * Algebra.trace S A x := by
    rw [Algebra.trace_apply, Algebra.trace_apply]
    calc s * LinearMap.trace S B (Algebra.lmul S B (φ x))
        = LinearMap.trace S B (Algebra.lmul S B (φ x) ∘ₗ (φ.toLinearMap ∘ₗ gl)) := by
          rw [h1, LinearMap.comp_smul, LinearMap.comp_id, map_smul, smul_eq_mul]
      _ = LinearMap.trace S B (φ.toLinearMap ∘ₗ (Algebra.lmul S A x ∘ₗ gl)) := by
          rw [← LinearMap.comp_assoc, h3, LinearMap.comp_assoc]
      _ = LinearMap.trace S A ((Algebra.lmul S A x ∘ₗ gl) ∘ₗ φ.toLinearMap) := by
          rw [LinearMap.trace_comp_comm']
      _ = s * LinearMap.trace S A (Algebra.lmul S A x) := by
          rw [LinearMap.comp_assoc, h2, LinearMap.comp_smul, LinearMap.comp_id, map_smul,
            smul_eq_mul]
  exact mul_left_cancel₀ hs key

example : ∀ (S A B : Type) [CommRing S] [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B] (φ : A →ₐ[S] B), Function.Injective φ → ∀ s : S, s ≠ 0 → (∀ b : B, s • b ∈ φ.range) → ∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x :=
  algebraTrace_map_of_cokernel_killed

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebra_trace_map_of_cokernel_killed_by_scalar : ∀ (S A B : Type) [CommRing S] [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B] (φ : A →ₐ[S] B), Function.Injective φ → ∀ s : S, s ≠ 0 → (∀ b : B, s • b ∈ φ.range) → ∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x := by
  atlas_forward_decl GlobalTheory.algebraTrace_map_of_cokernel_killed
end

section
open IsLocalRing

open TensorProduct

namespace GlobalTheory.EtaleCoker

theorem discr_isUnit (S A : Type) [CommRing S] [IsLocalRing S] [CommRing A] [Algebra S A]
    [Algebra.Etale S A] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι S A) :
    IsUnit (Algebra.discr S b) := by
  have h := GlobalTheory.PurityDisc.discr_ne_zero_of_etale (ResidueField S) (ResidueField S ⊗[S] A)
    (Algebra.TensorProduct.basis (ResidueField S) b)
  rw [GlobalTheory.PurityDisc.discr_baseChange] at h
  by_contra hn
  exact h ((residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn))

end GlobalTheory.EtaleCoker
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleCoker

theorem surjective_of_trace_of_smul_mem_range (S A B : Type) [CommRing S] [IsLocalRing S]
    [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A]
    [Algebra.Etale S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B]
    [Algebra.Etale S B] (φ : A →ₐ[S] B) (hφ : Function.Injective φ) (s : S) (hs : s ≠ 0)
    (hcok : ∀ b : B, s • b ∈ φ.range)
    (htr : ∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x) : Function.Surjective φ := by
  classical
  have htf : ∀ b : B, s • b = 0 → b = 0 := by
    intro b hb
    let e := Module.Free.chooseBasis S B
    apply e.repr.injective
    ext i
    have := congrArg (fun x => e.repr x i) hb
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
    simpa using (mul_eq_zero.mp this).resolve_left hs
  let L : A →ₗ[S] B := φ.toLinearMap
  have hL : Function.Injective L := hφ
  let E : A ≃ₗ[S] LinearMap.range L := LinearEquiv.ofInjective L hL
  let g : B →ₗ[S] LinearMap.range L :=
    { toFun := fun b => ⟨s • b, by obtain ⟨a, ha⟩ := hcok b; exact ⟨a, ha⟩⟩
      map_add' := fun x y => by ext; simp [smul_add]
      map_smul' := fun c x => by ext; simp [smul_comm s c] }
  have hg : Function.Injective g := by
    intro x y hxy
    have : s • x = s • y := congrArg Subtype.val hxy
    have h0 : s • (x - y) = 0 := by rw [smul_sub, this, sub_self]
    exact sub_eq_zero.mp (htf _ h0)
  have h1 : Module.finrank S A ≤ Module.finrank S B :=
    LinearMap.finrank_le_finrank_of_injective hL
  have h2 : Module.finrank S B ≤ Module.finrank S A :=
    LinearMap.finrank_le_finrank_of_injective (f := E.symm.toLinearMap ∘ₗ g)
      (E.symm.injective.comp hg)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex S A) =
      Fintype.card (Module.Free.ChooseBasisIndex S B) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex]
    omega
  let eι := Fintype.equivOfCardEq hcard
  let a := (Module.Free.chooseBasis S A).reindex eι
  let bB := Module.Free.chooseBasis S B
  let v : Module.Free.ChooseBasisIndex S B → B := fun i => φ (a i)
  have htm : Algebra.traceMatrix S v = Algebra.traceMatrix S a := by
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, v, ← map_mul, htr]
  have hdv : Algebra.discr S v = Algebra.discr S a := by
    rw [Algebra.discr_def, Algebra.discr_def, htm]
  let P := bB.toMatrix v
  have hv : Matrix.vecMul (⇑bB) (P.map (algebraMap S B)) = v := by
    funext j
    rw [← bB.sum_toMatrix_smul_self v j]
    simp [Matrix.vecMul, dotProduct, P, Algebra.smul_def, mul_comm]
  have hdisc : Algebra.discr S v = P.det ^ 2 * Algebra.discr S bB := by
    rw [← hv, Algebra.discr_of_matrix_vecMul]
  have hu : IsUnit (P.det ^ 2 * Algebra.discr S bB) := by
    rw [← hdisc, hdv]; exact discr_isUnit S A a
  have hPu : IsUnit P.det := (isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_left hu)
  have hbd : IsUnit (bB.det v) := by rw [Module.Basis.det_apply]; exact hPu
  have hspan := ((Module.Basis.is_basis_iff_det bB).mpr hbd).2
  intro y
  have hy : y ∈ Submodule.span S (Set.range v) := by rw [hspan]; trivial
  have hle : Submodule.span S (Set.range v) ≤ LinearMap.range L := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact ⟨a i, rfl⟩
  obtain ⟨x, hx⟩ := hle hy
  exact ⟨x, hx⟩

end GlobalTheory.EtaleCoker
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_injective_of_trace_eq_of_smul_mem_range : ∀ (S A B : Type) [CommRing S] [IsLocalRing S] [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A] [Algebra.Etale S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B] [Algebra.Etale S B] (φ : A →ₐ[S] B), Function.Injective φ → ∀ s : S, s ≠ 0 → (∀ b : B, s • b ∈ φ.range) → (∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x) → Function.Surjective φ := by
  atlas_forward_decl GlobalTheory.EtaleCoker.surjective_of_trace_of_smul_mem_range
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem localization_map_injective_coker_killed (R A B : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B) :
    Function.Injective ψ → ∀ s : R, s ≠ 0 → (∀ b : B, s • b ∈ ψ.range) →
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) ∧
      algebraMap R (Localization.AtPrime p) s ≠ 0 ∧
      ∀ y : Localization.AtPrime p ⊗[R] B, algebraMap R (Localization.AtPrime p) s • y ∈
        (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ).range := by
  intro hψ s hs hrange
  set L := Localization.AtPrime p
  refine ⟨?_, ?_, ?_⟩
  · have heq : ((Algebra.TensorProduct.map (AlgHom.id L L) ψ).toLinearMap.restrictScalars R) =
        LinearMap.lTensor L ψ.toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      simp
    have : Function.Injective (LinearMap.lTensor L ψ.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hψ
    rw [← heq] at this
    exact this
  · intro h0
    apply hs
    have hinj : Function.Injective (algebraMap R L) :=
      IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors p)
    exact hinj (by rw [h0, map_zero])
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      obtain ⟨a, ha⟩ := hrange b
      refine ⟨t ⊗ₜ a, ?_⟩
      have ha' : ψ a = s • b := ha
      change Algebra.TensorProduct.map (AlgHom.id L L) ψ (t ⊗ₜ a) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ha', TensorProduct.smul_tmul', algebraMap_smul,
        TensorProduct.smul_tmul]
    | add x y hx hy =>
      rw [smul_add]
      exact Subalgebra.add_mem _ hx hy

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_tensor_map_injective_coker_killed : ∀ (R A B : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B), Function.Injective ψ → ∀ s : R, s ≠ 0 → (∀ b : B, s • b ∈ ψ.range) → Function.Injective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) ∧ algebraMap R (Localization.AtPrime p) s ≠ 0 ∧ ∀ y : Localization.AtPrime p ⊗[R] B, algebraMap R (Localization.AtPrime p) s • y ∈ (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ).range := by
  atlas_forward_decl GlobalTheory.localization_map_injective_coker_killed
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_smul_mem_range_of_surjective_localization_map
    (R A B : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B)
    (hs : Function.Surjective (Algebra.TensorProduct.map
      (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ)) :
    ∀ b : B, ∃ t ∉ p, t • b ∈ ψ.range := by
  intro b
  classical
  set L := Localization.AtPrime p
  set N : Submodule R B := LinearMap.range ψ.toLinearMap
  let π := N.mkQ
  let g : L ⊗[R] B →ₗ[R] L ⊗[R] (B ⧸ N) := LinearMap.lTensor L π
  obtain ⟨z, hz⟩ := hs ((1 : L) ⊗ₜ[R] b)
  have key : ∀ w : L ⊗[R] A, g (Algebra.TensorProduct.map
      (AlgHom.id L L) ψ w) = 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul]
      simp only [g, LinearMap.lTensor_tmul]
      have : π (ψ y) = 0 := by
        simp only [π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨y, rfl⟩
      rw [this, TensorProduct.tmul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have h0 : (TensorProduct.mk R L (B ⧸ N) 1) (π b) = 0 := by
    have := key z
    rw [hz] at this
    simpa [g] using this
  have hloc : IsLocalizedModule p.primeCompl (TensorProduct.mk R L (B ⧸ N) 1) :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl L _).mpr (TensorProduct.isBaseChange R _ L)
  obtain ⟨s, hs'⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl _).mp h0
  refine ⟨s, s.2, ?_⟩
  have : π ((s : R) • b) = 0 := by
    rw [map_smul]; exact hs'
  simp only [π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N] at this
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha⟩

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_mem_range_of_surjective_localized_map : ∀ (R A B : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B), Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) → ∀ b : B, ∃ t ∉ p, t • b ∈ ψ.range := by
  atlas_forward_decl GlobalTheory.exists_smul_mem_range_of_surjective_localization_map
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem smul_mem_of_maximalIdeal_pow_of_locally_eq :
    ∀ (R B : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup B] [Module R B]
      [Module.Finite R B] (N : Submodule R B),
      (∀ (p : Ideal R), p.IsPrime → p ≠ maximalIdeal R → ∀ b : B, ∃ t ∉ p, t • b ∈ N) →
      ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ N := by
  intro R B _ _ _ _ _ _ N h
  classical
  set J : Ideal R := N.colon (Set.univ : Set B) with hJ
  have hmem : ∀ r : R, r ∈ J ↔ ∀ b : B, r • b ∈ N := by
    intro r
    rw [hJ, Submodule.mem_colon]
    simp
  have hrad : maximalIdeal R ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro p ⟨hJp, hp⟩
    by_cases hpm : p = maximalIdeal R
    · exact hpm.ge
    exfalso
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R B).FG)
    have hg : ∀ g : B, ∃ t ∉ p, t • g ∈ N := h p hp hpm
    choose t ht1 ht2 using hg
    set u : R := ∏ g ∈ s, t g with hu
    have hu_notin : u ∉ p := by
      rw [hu, Ideal.IsPrime.prod_mem_iff]
      rintro ⟨i, -, hi⟩
      exact ht1 i hi
    apply hu_notin
    apply hJp
    rw [hmem]
    intro b
    have hb : b ∈ Submodule.span R (s : Set B) := by rw [hs]; trivial
    have hle : Submodule.span R (s : Set B) ≤ N.comap (u • LinearMap.id) := by
      rw [Submodule.span_le]
      intro g hgs
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hu, ← Finset.prod_erase_mul s t hgs, mul_smul]
      exact N.smul_mem _ (ht2 g)
    have := hle hb
    simpa using this
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian (maximalIdeal R))
  exact ⟨k, fun x hx b => (hmem x).1 (hk hx) b⟩

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smul_mem_of_maximalIdeal_pow_of_locally_surjective : ∀ (R B : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup B] [Module R B] [Module.Finite R B] (N : Submodule R B), (∀ (p : Ideal R), p.IsPrime → p ≠ maximalIdeal R → ∀ b : B, ∃ t ∉ p, t • b ∈ N) → ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ N := by
  atlas_forward_decl GlobalTheory.smul_mem_of_maximalIdeal_pow_of_locally_eq
end

section
open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleCoker

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] (A B : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] [Module.Finite R B], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B)) → ∀ ψ : A →ₐ[R] B, Function.Injective ψ → (∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range) → ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ ψ.range := by
  intro R _ _ _ _ A B _ _ _ _ _ _ hA hB ψ hψ ⟨s, hs, hsb⟩
  obtain ⟨k, hk⟩ := GlobalTheory.T.smul_mem_of_maximalIdeal_pow_of_locally_surjective R B (ψ.range.toSubmodule.restrictScalars R) (fun p hp hpm => by
    haveI := hp
    haveI := hA p hpm
    haveI := hB p hpm
    let S := Localization.AtPrime p
    haveI : Module.Free S (S ⊗[R] A) := Module.free_of_flat_of_isLocalRing
    haveI : Module.Free S (S ⊗[R] B) := Module.free_of_flat_of_isLocalRing
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.localization_tensor_map_injective_coker_killed R A B p ψ hψ s hs hsb
    have htr := GlobalTheory.T.algebra_trace_map_of_cokernel_killed_by_scalar S _ _ _ h1 _ h2 h3
    exact GlobalTheory.T.exists_smul_mem_range_of_surjective_localized_map R A B p ψ (GlobalTheory.T.surjective_of_injective_of_trace_eq_of_smul_mem_range S _ _ _ h1 _ h2 h3 htr))
  exact ⟨k, fun x hx b => hk x hx b⟩

end GlobalTheory.EtaleCoker
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteLength_coker_of_etale_punctured_spectrum : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] (A B : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] [Module.Finite R B], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B)) → ∀ ψ : A →ₐ[R] B, Function.Injective ψ → (∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range) → ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ ψ.range := by
  first | (exact @GlobalTheory.EtaleCoker.main) | (exact GlobalTheory.EtaleCoker.main) | (intros; apply GlobalTheory.EtaleCoker.main  <;> assumption)
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modDepthGE_three_of_free_regularLocal : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M] [Nontrivial M], ReciprocityTheory.CA.ModDepthGE R M 3 := by
  first | exact @GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing | exact GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing | (intros; apply GlobalTheory.modDepthGE_three_of_free_of_isRegularLocalRing <;> assumption)
end

section
section
open IsLocalRing

namespace GlobalTheory.LocalLefschetz

lemma two_le_of_add_one {x y : WithBot ℕ∞} (h : x + 1 = y) (hy : 3 ≤ y) : 2 ≤ x := by
  subst h
  induction x using WithBot.recBotCoe with
  | bot => simp at hy
  | coe n =>
    have h3 : (3 : ℕ∞) ≤ n + 1 := WithBot.coe_le_coe.mp hy
    have : (2 : ℕ∞) ≤ n := by
      induction n using ENat.recTopCoe with
      | top => simp
      | coe m =>
        have : (3 : ℕ) ≤ m + 1 := by exact_mod_cast h3
        exact_mod_cast (by omega : 2 ≤ m)
    exact WithBot.coe_le_coe.mpr this

theorem depth_three : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ∉ maximalIdeal R ^ 2 → ∀ [IsLocalRing (R ⧸ Ideal.span {f})], GlobalTheory.PurityFree (R ⧸ Ideal.span {f}) → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 2 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ReciprocityTheory.CA.ModDepthGE R A 3 := by
  intro R _ _ hcomp hdim f hf hf2 _ hpur A _ _ _ hdep hEt
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf2 (Ideal.zero_mem _)
  haveI : IsDomain R := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain R
  have hreg : IsSMulRegular A f :=
    GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' R A (ReciprocityTheory.CA.ModDepthGE.mono (by norm_num) hdep) hEt f hf0
  haveI hRb : IsRegularLocalRing (R ⧸ Ideal.span {f}) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hf hf2
  have hdimb : 2 ≤ ringKrullDim (R ⧸ Ideal.span {f}) :=
    two_le_of_add_one
      (ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.ringKrullDim_quotient_span_singleton_add_one hf hf2) hdim
  haveI : Module.Finite R (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R ((Ideal.span {f}).map (algebraMap R A))).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hdepb := GlobalTheory.modDepthGE_quotient_map_span_singleton R A f hf hreg 1 hdep
  have hEtb := GlobalTheory.T.etale_quotient_of_etale_punctured' R A f hEt
  obtain ⟨A', _, _, hA'fin, ι, hι, hdep', hEt', k, hk⟩ := GlobalTheory.T.exists_finite_depth_two_hull_of_etale_punctured_spectrum _ hdimb _ hdepb hEtb
  have hfree : Module.Free (R ⧸ Ideal.span {f}) A' := hpur A' hdep' hEt'
  obtain ⟨_, _⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (R ⧸ Ideal.span {f})
  have hnf : ¬ IsField (R ⧸ Ideal.span {f}) := by
    intro hF
    have := ringKrullDim_eq_zero_of_isField hF
    rw [this] at hdimb
    exact absurd hdimb (by decide)
  have hEtA' : Algebra.Etale (R ⧸ Ideal.span {f}) A' := by
    refine GlobalTheory.T.etale_of_etale_at_height_one_primes _ A' hnf fun p _ hp => hEt' p ?_
    rintro rfl
    have h1 := maximalIdeal_height_eq_ringKrullDim (R := R ⧸ Ideal.span {f})
    rw [hp] at h1
    rw [← h1] at hdimb
    exact absurd hdimb (by decide)
  obtain ⟨B, _, _, hBfin, hBfree, hBet, ⟨e⟩⟩ := GlobalTheory.T.exists_finite_free_etale_lift_of_quotient_etale R hcomp f hf A'
  let φ : A →ₐ[R] B ⧸ (Ideal.span {f}).map (algebraMap R B) :=
    { toRingHom := e.symm.toRingHom.comp (ι.toRingHom.comp (Ideal.Quotient.mk _))
      commutes' := fun r => by
        have h1 : (Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R A)) (algebraMap R A r)) =
            algebraMap (R ⧸ Ideal.span {f}) _ (algebraMap R (R ⧸ Ideal.span {f}) r) := by
          rw [← IsScalarTower.algebraMap_apply]; rfl
        show e.symm (ι (Ideal.Quotient.mk _ (algebraMap R A r))) = _
        rw [h1, ι.commutes, e.symm.commutes, ← IsScalarTower.algebraMap_apply] }
  have hφ : ∀ a, φ a = e.symm (ι (Ideal.Quotient.mk _ a)) := fun a => rfl
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_lift_algHom_of_etale_punctured R hcomp hdim f hf hf0 A hEt B φ
  have hψa : ∀ a, Ideal.Quotient.mk _ (ψ a) = φ a := fun a => by
    rw [← hψ]; rfl
  have hBreg : IsSMulRegular B f := fun x y h => smul_right_injective B hf0 h
  have hsat : ∀ a : A, ψ a ∈ (Ideal.span {f}).map (algebraMap R B) →
      a ∈ (Ideal.span {f}).map (algebraMap R A) := by
    intro a ha
    have h1 : φ a = 0 := by
      rw [← hψa]; exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [hφ] at h1
    have h2 : ι (Ideal.Quotient.mk _ a) = 0 := by
      simpa using h1
    have h3 : Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R A)) a = 0 :=
      hι (by rw [h2, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  obtain ⟨hinj, hfsat⟩ := GlobalTheory.T.injective_and_saturated_of_injective_mod_regular' R A B f hf hBreg ψ hsat
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {f})) ≤ maximalIdeal (R ⧸ Ideal.span {f}) := by
    rw [Ideal.map_le_iff_le_comap]
    have : (maximalIdeal (R ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})) = maximalIdeal R := by
      haveI := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (Ideal.span {f}))
        Ideal.Quotient.mk_surjective (K := maximalIdeal (R ⧸ Ideal.span {f}))
      exact IsLocalRing.eq_maximalIdeal this
    rw [this]
  have hspan : ∀ z : B, z ∈ (Ideal.span {f}).map (algebraMap R B) → ∃ c : B, z = f • c := by
    intro z hz
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hz
    obtain ⟨c, hc⟩ := hz
    exact ⟨c, by rw [Algebra.smul_def, ← hc, mul_comm]⟩
  have hcok : ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c := by
    refine ⟨k, fun x hx b => ?_⟩
    have hx' : Ideal.Quotient.mk (Ideal.span {f}) x ∈ maximalIdeal (R ⧸ Ideal.span {f}) ^ k := by
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {f})) hx
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono hmap k this
    obtain ⟨abar, habar⟩ := hk _ hx' (e (Ideal.Quotient.mk _ b))
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective abar
    refine ⟨a, ?_⟩
    have h1 : Ideal.Quotient.mk ((Ideal.span {f}).map (algebraMap R B)) (x • b - ψ a) = 0 := by
      rw [map_sub, hψa, hφ]
      change Ideal.Quotient.mk _ (x • b) - e.symm (ι (Ideal.Quotient.mk _ a)) = 0
      have habar' : ι (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk (Ideal.span {f}) x • e (Ideal.Quotient.mk _ b) := habar
      have h2 : ∀ z, e.symm (Ideal.Quotient.mk (Ideal.span {f}) x • e z) =
          Ideal.Quotient.mk (Ideal.span {f}) x • z := fun z => by
        rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, AlgEquiv.symm_apply_apply, ← Algebra.smul_def]
      rw [habar', h2]
      change Ideal.Quotient.mkₐ R _ (x • b) - _ = 0
      rw [map_smul, ← algebraMap_smul (R ⧸ Ideal.span {f}) x, Ideal.Quotient.algebraMap_eq]
      exact sub_eq_zero.mpr rfl
    obtain ⟨c, hc⟩ := hspan _ (Ideal.Quotient.eq_zero_iff_mem.mp h1)
    exact ⟨c, by rw [← hc]; abel⟩
  have hdim1 : 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) := le_trans (by decide) hdimb
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.cokernel_torsion_of_finiteLength_mod_element R f hdim1 A B ψ hcok
  have hEtB : ∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R →
      Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B) :=
    fun p _ _ => inferInstance
  obtain ⟨k2, hk2⟩ := GlobalTheory.T.finiteLength_coker_of_etale_punctured_spectrum R A B hEt hEtB ψ hinj ⟨s, hs0, hs⟩
  have hdesc : ∀ (n : ℕ) (b : B), f ^ n • b ∈ ψ.range → b ∈ ψ.range := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih =>
      intro b hb
      apply ih
      apply hfsat
      rwa [← mul_smul, ← pow_succ']
  have hsurj : Function.Surjective ψ := fun b => by
    obtain ⟨a, ha⟩ := hdesc k2 b (hk2 _ (Ideal.pow_mem_pow hf k2) b)
    exact ⟨a, ha⟩
  let eqv : A ≃ₐ[R] B := AlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  haveI : Module.Free R A := Module.Free.of_equiv eqv.symm.toLinearEquiv
  haveI : Nontrivial A := by
    obtain ⟨rs, -, -, hr⟩ := hdep
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hr.top_ne_smul (Subsingleton.elim _ _)
  exact GlobalTheory.T.modDepthGE_three_of_free_regularLocal R hdim A

end GlobalTheory.LocalLefschetz
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_ge_three_finite_etale_punctured_regular : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ∉ maximalIdeal R ^ 2 → ∀ [IsLocalRing (R ⧸ Ideal.span {f})], GlobalTheory.PurityFree (R ⧸ Ideal.span {f}) → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 2 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ReciprocityTheory.CA.ModDepthGE R A 3 := by
  atlas_forward_decl GlobalTheory.LocalLefschetz.depth_three
end
