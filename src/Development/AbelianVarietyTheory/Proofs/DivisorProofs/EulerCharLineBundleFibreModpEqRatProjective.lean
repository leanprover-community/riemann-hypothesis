import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv

section
section
open CategoryTheory Limits

namespace GlobalTheory

theorem index_range_eq_card_ker_of_finite {D : Type} [AddCommGroup D] [Finite D] (f : D →+ D) :
    f.range.index = Nat.card f.ker := by
  have h1 := f.range.card_mul_index
  have h2 := f.ker.card_mul_index
  rw [AddSubgroup.index_ker] at h2
  have h3 : 0 < Nat.card f.range := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left h3
  rw [h1, mul_comm, h2]

theorem card_quot_smul_eq_of_equiv_prod {M D : Type} [AddCommGroup M] [AddCommGroup D] [Finite D]
    {n : ℕ} (e : M ≃+ (Fin n → ℤ) × D) (p : ℕ) (hp : p ≠ 0) :
    Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) *
        p ^ Module.finrank ℤ M := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  let f : D →+ D := zsmulAddGroupHom (p : ℤ)
  have hf : ∀ d, f d = (p : ℤ) • d := fun d => rfl
  have hrank : Module.finrank ℤ M = n := by
    rw [e.toIntLinearEquiv.finrank_eq]
    have hD : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ (Fin n → ℤ) D)) = 0 := by
      rw [Module.rank_eq_zero_iff_isTorsion]
      intro x
      refine ⟨⟨(Nat.card D : ℤ), mem_nonZeroDivisors_of_ne_zero ?_⟩, ?_⟩
      · exact_mod_cast (Nat.card_pos (α := D)).ne'
      · have hx : x.1.1 = 0 := x.2
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · simp [Submonoid.smul_def, hx]
        · simp [Submonoid.smul_def]
    have : Module.rank ℤ ((Fin n → ℤ) × D) = n := by
      rw [← (LinearMap.fst ℤ (Fin n → ℤ) D).rank_range_add_rank_ker, hD,
        LinearMap.range_eq_top.2 LinearMap.fst_surjective]
      simp
    simp [Module.finrank, this]
  have hker : Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card f.ker := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(e x.1).2, ?_⟩
        invFun := fun d => ⟨e.symm (0, d.1), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hx : (p : ℤ) • x.1 = 0 := x.2
      have := congrArg (fun y => (e y).2) hx
      simpa [hf] using this
    · have hd : (p : ℤ) • d.1 = 0 := d.2
      change (p : ℤ) • e.symm (0, d.1) = 0
      rw [← map_zsmul, Prod.smul_mk, hd, smul_zero]
      exact map_zero _
    · intro x
      have hx : (p : ℤ) • x.1 = 0 := x.2
      have h1 : (p : ℤ) • (e x.1).1 = 0 := by
        have := congrArg (fun y => (e y).1) hx
        simpa only [map_zsmul, map_zero, Prod.smul_fst, Prod.fst_zero] using this
      have h2 : (e x.1).1 = 0 := (smul_eq_zero.1 h1).resolve_left hp'
      apply Subtype.ext
      change e.symm (0, (e x.1).2) = x.1
      rw [← h2]
      exact e.symm_apply_apply _
    · intro d
      apply Subtype.ext
      simp
  have hrange : (LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).toAddSubgroup =
      ((AddSubgroup.pi Set.univ fun _ : Fin n => AddSubgroup.zmultiples (p : ℤ)).prod
        f.range).comap e.toAddMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [AddSubgroup.mem_comap]
      change e ((p : ℤ) • y) ∈ _
      rw [map_zsmul]
      refine ⟨fun i _ => ⟨(e y).1 i, ?_⟩, ⟨(e y).2, rfl⟩⟩
      simp [mul_comm]
    · rintro ⟨h1, d, hd⟩
      have h1' : ∀ i, ∃ k : ℤ, k • (p : ℤ) = (e x).1 i := fun i => h1 i (Set.mem_univ i)
      choose k hk using h1'
      refine ⟨e.symm (k, d), ?_⟩
      change (p : ℤ) • e.symm (k, d) = x
      rw [← map_zsmul, AddEquiv.symm_apply_eq]
      refine Prod.ext (funext fun i => ?_) hd
      rw [← hk i]
      simp [mul_comm]
  have hq : Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      (LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))).toAddSubgroup.index := rfl
  rw [hq, hrange, AddSubgroup.index_comap_of_surjective _ e.surjective, AddSubgroup.index_prod,
    AddSubgroup.index_pi, index_range_eq_card_ker_of_finite, hker, hrank, mul_comm]
  simp [Int.index_zmultiples]

theorem card_quot_prime_smul_eq_card_ker_mul_pow_finrank (M : Type) [AddCommGroup M]
    [inst : Module ℤ M] [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime] :
    Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) =
      Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) *
        p ^ Module.finrank ℤ M := by
  obtain rfl : inst = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  haveI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  obtain ⟨n, ι, _, q, hq, k, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  haveI : ∀ i, NeZero (q i ^ k i) := fun i => ⟨pow_ne_zero _ (hq i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (q i ^ k i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  exact card_quot_smul_eq_of_equiv_prod
    (e.trans ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddEquiv.prodCongr (AddEquiv.refl _)))
    p (Fact.out : p.Prime).ne_zero

end GlobalTheory
end

open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime], Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) = Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) * p ^ Module.finrank ℤ M := by
  atlas_forward_decl GlobalTheory.card_quot_prime_smul_eq_card_ker_mul_pow_finrank
end

section
section
open CategoryTheory Limits

namespace GlobalTheory

theorem natCard_eq_coker_mul_ker_of_exact {R : Type} [Ring R] {A A' B D D' : Type}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup D] [AddCommGroup D']
    [Module R A] [Module R A'] [Module R B] [Module R D] [Module R D']
    (f : A →ₗ[R] A') (g : A' →ₗ[R] B) (d : B →ₗ[R] D) (h : D →ₗ[R] D')
    (e₁ : LinearMap.range f = LinearMap.ker g) (e₂ : LinearMap.range g = LinearMap.ker d)
    (e₃ : LinearMap.range d = LinearMap.ker h) :
    Nat.card B = Nat.card (A' ⧸ LinearMap.range f) * Nat.card (LinearMap.ker h) := by
  have h1 : Nat.card B = Nat.card (B ⧸ LinearMap.ker d) * Nat.card (LinearMap.ker d) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker d).toAddSubgroup
  rw [h1, Nat.card_congr d.quotKerEquivRange.toEquiv, e₃, e₁,
    Nat.card_congr g.quotKerEquivRange.toEquiv, e₂, mul_comm]

theorem natCard_homology_of_shortExact_mul : ∀ (p : ℕ) (C G : CochainComplex (ModuleCat.{0} ℤ) ℕ) (π : C ⟶ G) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact → ∀ n : ℕ, Nat.card (G.homology n) = Nat.card ((C.homology n) ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : C.homology n →ₗ[ℤ] C.homology n))) * Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1)))) := by
  intro p C G π hz hS n
  have hmul0 : ∀ k, HomologicalComplex.homologyMap ((p : ℤ) • 𝟙 C) k = (p : ℤ) • 𝟙 _ := by
    intro k
    have := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) k).map_zsmul
      (f := 𝟙 C) (r := (p : ℤ))
    rw [CategoryTheory.Functor.map_id] at this
    exact this
  have hmul : ∀ k, (HomologicalComplex.homologyMap ((p : ℤ) • 𝟙 C) k).hom
      = (p : ℤ) • (LinearMap.id : C.homology k →ₗ[ℤ] C.homology k) := by
    intro k
    rw [hmul0]
    ext x
    simp
  have e2 := (hS.homology_exact₂ n).moduleCat_range_eq_ker
  have e3 := (hS.homology_exact₃ n (n+1) rfl).moduleCat_range_eq_ker
  have e1 := (hS.homology_exact₁ n (n+1) rfl).moduleCat_range_eq_ker
  dsimp only at e1 e2 e3
  rw [hmul] at e1 e2
  exact natCard_eq_coker_mul_ker_of_exact _ _ _ _ e2 e3 e1

end GlobalTheory
end

open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_homology_of_shortExact_mul' : ∀ (p : ℕ) (C G : CochainComplex (ModuleCat.{0} ℤ) ℕ) (π : C ⟶ G) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact → ∀ n : ℕ, Nat.card (G.homology n) = Nat.card ((C.homology n) ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : C.homology n →ₗ[ℤ] C.homology n))) * Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1)))) := by
  atlas_forward_decl GlobalTheory.natCard_homology_of_shortExact_mul
end

section
section
open CategoryTheory Limits

namespace GlobalTheory

theorem ideal_span_natCast_smul_top_eq_range (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ) :
    (Ideal.span {(p : ℤ)}) • (⊤ : Submodule ℤ M) =
      LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M)) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  simp [Submodule.mem_smul_pointwise_iff_exists, Nat.cast_smul_eq_nsmul]

noncomputable def intQuotSpanNatLinearEquivZMod (p : ℕ) :
    (ℤ ⧸ Ideal.span {(p : ℤ)}) ≃ₗ[ℤ] ZMod p :=
  LinearEquiv.ofBijective (Int.quotientSpanNatEquivZMod p).toRingHom.toIntAlgHom.toLinearMap
    (Int.quotientSpanNatEquivZMod p).bijective

theorem card_zmod_tensor_eq_card_quot (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ) :
    Nat.card (TensorProduct ℤ (ZMod p) M) =
      Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by
  rw [← Nat.card_congr ((intQuotSpanNatLinearEquivZMod p).rTensor M).toEquiv,
    Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {(p : ℤ)})).toEquiv,
    ideal_span_natCast_smul_top_eq_range]

theorem card_zmod_tensor_eq_card_quot' : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ),
    Nat.card (TensorProduct ℤ (ZMod p) M) =
      Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) :=
  fun M _ _ p => card_zmod_tensor_eq_card_quot M p

end GlobalTheory
end

open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples : ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ), Nat.card (TensorProduct ℤ (ZMod p) M) = Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by
  atlas_forward_decl GlobalTheory.card_zmod_tensor_eq_card_quot'
end

section
section
open CategoryTheory Limits

namespace GlobalTheory

theorem natCard_homology_restrictScalars {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ) :
    Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by
  have e : (((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n ≅
      (ModuleCat.restrictScalars.{0} f).obj (D.homology n) :=
    (D.sc n).mapHomologyIso (ModuleCat.restrictScalars.{0} f)
  exact Nat.card_congr e.toLinearEquiv.toEquiv

end GlobalTheory
end

open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_homology_restrictScalars_alt : ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (D : CochainComplex (ModuleCat.{0} S) ℕ) (n : ℕ), Nat.card ((((ModuleCat.restrictScalars.{0} f).mapHomologicalComplex (ComplexShape.up ℕ)).obj D).homology n) = Nat.card (D.homology n) := by
  atlas_forward_decl GlobalTheory.natCard_homology_restrictScalars
end

section
section
open CategoryTheory Limits

noncomputable section

namespace GlobalTheory

abbrev pMultiples (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] : Submodule ℤ M :=
  LinearMap.range ((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M)

lemma zmultiples_mkQ_p (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] :
    zmultiplesHom (M →+ M ⧸ pMultiples p M) (pMultiples p M).mkQ.toAddMonoidHom (p : ℤ) = 0 := by
  ext m
  simp only [zmultiplesHom_apply, AddMonoidHom.coe_smul, Pi.smul_apply, AddMonoidHom.zero_apply]
  show (p : ℤ) • Submodule.Quotient.mk m = (0 : M ⧸ pMultiples p M)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨m, by simp⟩

def modPPairing (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] :
    ZMod p →+ M →+ (M ⧸ pMultiples p M) :=
  ZMod.lift p ⟨zmultiplesHom _ (pMultiples p M).mkQ.toAddMonoidHom, zmultiples_mkQ_p p M⟩

lemma modPPairing_one (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] (m : M) :
    modPPairing p M 1 m = Submodule.Quotient.mk m := by
  have h := ZMod.lift_coe p (A := M →+ (M ⧸ pMultiples p M))
    ⟨zmultiplesHom _ (pMultiples p M).mkQ.toAddMonoidHom, zmultiples_mkQ_p p M⟩ 1
  simp only [Int.cast_one] at h
  unfold modPPairing
  rw [h]
  simp

abbrev zmodOverInt (p : ℕ) : ModuleCat.{0} ℤ :=
  (ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of (ZMod p) (ZMod p))

def tensorToModP (p : ℕ) (M : ModuleCat.{0} ℤ) :
    TensorProduct ℤ (zmodOverInt p) M →+ (M ⧸ pMultiples p M) :=
  TensorProduct.liftAddHom (modPPairing p M) (fun r a m => by
    have key : ∀ b : ZMod p, modPPairing p M ((r : ZMod p) * b) m = r • modPPairing p M b m := by
      intro b
      rw [← zsmul_eq_mul, map_zsmul]
      rfl
    refine (key a).trans ?_
    rw [← map_zsmul]
    congr 1
    exact (int_smul_eq_zsmul _ r m).symm)

lemma tensorToModP_unit (p : ℕ) (M : ModuleCat.{0} ℤ) (m : M) :
    tensorToModP p M
      (((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom m) =
      Submodule.Quotient.mk m := by
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  unfold tensorToModP
  exact (TensorProduct.liftAddHom_tmul _ _ _ _).trans (modPPairing_one p M m)

end GlobalTheory

end

noncomputable section

namespace GlobalTheory

def oneZ (p : ℕ) : zmodOverInt p := (1 : ZMod p)

lemma oneZ_tmul_surjective (p : ℕ) (M : ModuleCat.{0} ℤ) :
    ∀ t : TensorProduct ℤ (zmodOverInt p) M, ∃ m : M, oneZ p ⊗ₜ[ℤ] m = t := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul a m =>
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := p) a
    have h1 := map_zsmul (AddMonoidHom.mk' (fun x : M => oneZ p ⊗ₜ[ℤ] x) (TensorProduct.tmul_add _)) k m
    have h2 := map_zsmul (AddMonoidHom.mk' (fun b : zmodOverInt p => b ⊗ₜ[ℤ] m)
      (fun b c => TensorProduct.add_tmul b c m)) k (oneZ p)
    refine ⟨_, (h1.trans h2.symm).trans (congrArg (fun x => x ⊗ₜ[ℤ] m) ?_)⟩
    show (k • (1 : ZMod p) : ZMod p) = a
    rw [zsmul_one]
    exact hk
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, (TensorProduct.tmul_add _ u v).trans (by rw [hu, hv])⟩

lemma unit_surjective_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom := by
  intro t
  obtain ⟨m, hm⟩ := oneZ_tmul_surjective p M t
  exact ⟨m, (ModuleCat.extendRestrictScalarsAdj_unit_app_apply _ _ _).trans hm⟩

lemma unit_kernel_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) (y : M)
    (hy : ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom y = 0) :
    ∃ x : M, ((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M) x = y := by
  have h := tensorToModP_unit p M y
  rw [hy] at h
  exact (Submodule.Quotient.mk_eq_zero _).mp (h.symm.trans (map_zero (tensorToModP p M)))

lemma oneZ_tmul_p (p : ℕ) (M : ModuleCat.{0} ℤ) (x : M) :
    oneZ p ⊗ₜ[ℤ] ((p : ℤ) • x) = 0 := by
  have h1 := map_zsmul (AddMonoidHom.mk' (fun y : M => oneZ p ⊗ₜ[ℤ] y) (TensorProduct.tmul_add _)) (p : ℤ) x
  have h2 := map_zsmul (AddMonoidHom.mk' (fun b : zmodOverInt p => b ⊗ₜ[ℤ] x)
      (fun b c => TensorProduct.add_tmul b c x)) (p : ℤ) (oneZ p)
  refine (h1.trans h2.symm).trans ((congrArg (fun b => b ⊗ₜ[ℤ] x) ?_).trans (TensorProduct.zero_tmul _ _))
  show ((p : ℤ) • (1 : ZMod p) : ZMod p) = 0
  simp

lemma unit_pmul_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) (x : M) :
    ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom
      (((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M) x) = 0 :=
  (ModuleCat.extendRestrictScalarsAdj_unit_app_apply _ _ _).trans (oneZ_tmul_p p M x)

lemma pmul_injective (p : ℕ) (M : ModuleCat.{0} ℤ) (h : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Function.Injective (ConcreteCategory.hom ((p : ℤ) • 𝟙 M)) := by
  intro a b hab
  have hab' : (p : ℤ) • a = (p : ℤ) • b := hab
  apply sub_eq_zero.mp
  apply h
  rw [zsmul_sub, hab', sub_self]

theorem shortExact_mul_p_modP :
    ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime],
      (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) →
      ∃ (π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C)) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0),
        (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact := by
  intro C p _ hinj
  let π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C) :=
    { f := fun n => (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app (C.X n)
      comm' := fun i j _ =>
        ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.naturality (C.d i j)) }
  have hz : ((p : ℤ) • 𝟙 C) ≫ π = 0 := by
    ext n x
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f,
      ModuleCat.hom_comp, ModuleCat.hom_zsmul, ModuleCat.hom_id, LinearMap.comp_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact unit_pmul_zmod p (C.X n) x
  refine ⟨π, hz, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    simp only [ShortComplex.map_f, ShortComplex.map_g, HomologicalComplex.eval_map,
      HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f, ModuleCat.hom_zsmul,
      ModuleCat.hom_id] at hy ⊢
    exact unit_kernel_zmod p (C.X n) y hy
  · rw [ModuleCat.mono_iff_injective]
    exact pmul_injective p (C.X n) (hinj n)
  · rw [ModuleCat.epi_iff_surjective]
    exact unit_surjective_zmod p (C.X n)

end GlobalTheory

end
end

open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_mul_prime_zmod_tensor_complex : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → ∃ (π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C)) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact := by
  atlas_forward_decl GlobalTheory.shortExact_mul_p_modP
end

section
section
open CategoryTheory Limits

namespace GlobalTheory

theorem uct_mod_p : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → (∀ n, Module.Finite ℤ (C.homology n)) → ∀ n : ℕ, (Module.finrank (ZMod p) ((((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1))) - Module.finrank ℤ (C.homology (n + 1)) := by
  intro C p _ hinj hfin n
  obtain ⟨π, hz, hS⟩ := GlobalTheory.T.shortExact_mul_prime_zmod_tensor_complex C p hinj
  have e := GlobalTheory.T.natCard_homology_of_shortExact_mul' p C _ π hz hS n
  rw [GlobalTheory.T.natCard_homology_restrictScalars_alt] at e
  haveI := hfin n
  haveI := hfin (n + 1)
  have a1 := GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank (C.homology n) p
  have a2 := GlobalTheory.T.card_quot_range_prime_smul_eq_card_ker_mul_pow_finrank (C.homology (n + 1)) p
  rw [← GlobalTheory.T.card_zmod_tensor_eq_card_quot_prime_multiples] at a1 a2 e
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hcp : Nat.card (ZMod p) = p := by simp
  have c1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) (C.homology n))
  have c2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) (C.homology (n + 1)))
  rw [hcp] at c1 c2
  set D := (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n
  have hk : Nat.card (LinearMap.ker ((p : ℤ) • LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1))) ≠ 0 := by
    intro h0; rw [h0, zero_mul, c2] at a2; exact absurd a2 (pow_ne_zero _ (by omega))
  have hD : Nat.card D ≠ 0 := by
    rw [e, c1]; exact mul_ne_zero (pow_ne_zero _ (by omega)) hk
  haveI : Finite D := Nat.finite_of_card_ne_zero hD
  haveI : Module.Finite (ZMod p) D := Module.Finite.of_finite
  have c0 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := D)
  rw [hcp] at c0
  have key : p ^ (Module.finrank (ZMod p) D + Module.finrank ℤ (C.homology (n + 1))) = p ^ (Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1)))) := by
    rw [pow_add, pow_add, ← c0, e, ← c1, ← c2, a2]; ring
  have := Nat.pow_right_injective hp key
  push_cast; omega

end GlobalTheory
end

open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_homology_mod_prime_universal_coefficients : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) → (∀ n, Module.Finite ℤ (C.homology n)) → ∀ n : ℕ, (Module.finrank (ZMod p) ((((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n)) + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology (n + 1))) - Module.finrank ℤ (C.homology (n + 1)) := by
  atlas_forward_decl GlobalTheory.uct_mod_p
end

section
section
open CategoryTheory Limits

namespace GlobalTheory

theorem exists_torsion_eq_prime_smul_of_noPTorsion {M : Type*} [AddCommGroup M] (p : ℕ)
    [hp : Fact p.Prime] (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) (t : M)
    (ht : t ∈ Submodule.torsion ℤ M) :
    ∃ s ∈ Submodule.torsion ℤ M, t = (p : ℤ) • s := by
  obtain ⟨⟨a, ha⟩, hat⟩ := (Submodule.mem_torsion_iff t).1 ht
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  change a • t = 0 at hat
  set n := a.natAbs with hn
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.2 ha0
  have hnt : (n : ℤ) • t = 0 := by
    rcases Int.natAbs_eq a with h | h
    · rw [← h]; exact hat
    · have : a = -(n : ℤ) := h
      rw [this, neg_smul, neg_eq_zero] at hat; exact hat
  have hpow : ∀ k : ℕ, ∀ y : M, ((p : ℤ) ^ k) • y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      rw [pow_succ, mul_smul] at hy
      exact hM y (ih _ hy)
  set k := n.factorization p
  set m := n / p ^ k
  have hnm : p ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hmt : (m : ℤ) • t = 0 := by
    apply hpow k
    rw [← mul_smul]
    have : ((p : ℤ) ^ k * (m : ℤ)) = (n : ℤ) := by exact_mod_cast hnm
    rw [this, hnt]
  have hndvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp.out hn0
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hndvd
  have hic : IsCoprime (p : ℤ) (m : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd_natCast_natCast] using hcop
  obtain ⟨u, v, huv⟩ := hic
  refine ⟨u • t, Submodule.smul_mem _ _ ht, ?_⟩
  calc t = ((u * p + v * m : ℤ)) • t := by rw [huv, one_smul]
    _ = (p : ℤ) • (u • t) := by
      rw [add_smul, mul_smul, mul_smul, hmt, smul_zero, add_zero, smul_comm]

theorem subsingleton_zmod_tensor_torsion {M : Type*} [AddCommGroup M] (p : ℕ) [Fact p.Prime]
    (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Subsingleton (TensorProduct ℤ (ZMod p) (Submodule.torsion ℤ M)) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul c t =>
    obtain ⟨s, hs, hts⟩ := exists_torsion_eq_prime_smul_of_noPTorsion p hM t.1 t.2
    have : t = (p : ℤ) • (⟨s, hs⟩ : Submodule.torsion ℤ M) := Subtype.ext hts
    rw [this, ← TensorProduct.smul_tmul]
    have hc : (p : ℤ) • c = 0 := by
      rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
    rw [hc, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem finrank_zmod_tensor_eq_finrank_of_noPTorsion (M : Type*) [AddCommGroup M] [inst : Module ℤ M]
    [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime] (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) M) = Module.finrank ℤ M := by
  obtain rfl : inst = AddCommGroup.toIntModule M := Subsingleton.elim _ _
  set T := Submodule.torsion ℤ M
  haveI : Module.Free ℤ (M ⧸ T) := Module.free_of_finite_type_torsion_free'
  haveI := subsingleton_zmod_tensor_torsion p hM
  let g := LinearMap.baseChange (ZMod p) T.mkQ
  have hg : ⇑g = ⇑(LinearMap.lTensor (ZMod p) T.mkQ) := LinearMap.baseChange_eq_ltensor _
  have hex := lTensor_exact (ZMod p) (LinearMap.exact_subtype_mkQ T) (Submodule.mkQ_surjective T)
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : LinearMap.lTensor (ZMod p) T.mkQ y = 0 := by rw [← hg]; exact hy
    obtain ⟨z, rfl⟩ := (hex y).1 hy'
    rw [Subsingleton.elim z 0, map_zero]
  have hsurj : Function.Surjective g := by
    rw [hg]; exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective T)
  rw [(LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_baseChange,
    finrank_quotient_eq_of_le_torsion le_rfl]

theorem finrank_zmod_tensor_homology_zero :
    ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime],
      (∀ (x : C.X 0), (p : ℤ) • x = 0 → x = 0) → Module.Finite ℤ (C.homology 0) →
      Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology 0)) =
        Module.finrank ℤ (C.homology 0) := by
  intro C p _ hC _
  let f : C.homology 0 ⟶ C.X 0 := C.isoHomologyπ₀.inv ≫ C.iCycles 0
  have hinj : Function.Injective (ConcreteCategory.hom f) :=
    (ModuleCat.mono_iff_injective f).1 inferInstance
  apply finrank_zmod_tensor_eq_finrank_of_noPTorsion
  intro x hx
  apply hinj
  rw [map_zero]
  apply hC
  rw [← map_zsmul, hx, map_zero]

end GlobalTheory
end

open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_zmod_tensor_homology_zero_of_noPTorsion : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (x : C.X 0), (p : ℤ) • x = 0 → x = 0) → Module.Finite ℤ (C.homology 0) → Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology 0)) = Module.finrank ℤ (C.homology 0) := by
  atlas_forward_decl GlobalTheory.finrank_zmod_tensor_homology_zero
end

section
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.RatHomology

theorem finrank_rat_tensor (M : Type) [AddCommGroup M] [Module ℤ M] :
    Module.finrank ℚ (ℚ ⊗[ℤ] M) = Module.finrank ℤ M := by
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) le_rfl,
    ← IsFractionRing.finrank_right_eq ℤ ℚ]

theorem finrank_rat_homology (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (_ : Module.Finite ℤ (C.homology n)) :
    Module.finrank ℚ ((((ModuleCat.extendScalars (Int.castRingHom ℚ)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj C).homology n) = Module.finrank ℤ (C.homology n) := by
  obtain ⟨e⟩ := GlobalTheory.FieldChangeInter.nonempty_homology_equiv ℚ C n
  have h := e.finrank_eq
  have hφ : algebraMap ℤ ℚ = Int.castRingHom ℚ := rfl
  rw [hφ] at h
  rw [h]
  exact finrank_rat_tensor (C.homology n)

end GlobalTheory.RatHomology
end

open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_rat_homology_eq_finrank_int : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ), Module.Finite ℤ (C.homology n) → Module.finrank ℚ ((((ModuleCat.extendScalars (Int.castRingHom ℚ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) = Module.finrank ℤ (C.homology n) := by
  atlas_forward_decl GlobalTheory.RatHomology.finrank_rat_homology
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open GlobalTheory.LB (toMod)

namespace GlobalTheory.CechPic

theorem intCast_mul_eq_zero_of_isIntegral {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X]
    (hc : CharZero Γ(X, ⊤)) (W : X.Opens) {m : ℤ} (hm : m ≠ 0) {c : Γ(X, W)}
    (h : (m : Γ(X, W)) * c = 0) : c = 0 := by
  by_cases hW : Nonempty W
  · have hinj := AlgebraicGeometry.map_injective_of_isIntegral X (homOfLE (le_top : W ≤ ⊤))
    have hm' : (m : Γ(X, W)) ≠ 0 := by
      intro h0
      apply hm
      have : (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (m : Γ(X, ⊤)) =
          (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom 0 := by
        rw [map_intCast, map_zero, h0]
      exact_mod_cast hinj this
    exact (mul_eq_zero.1 h).resolve_left hm'
  · have hb : W = ⊥ := eq_bot_iff.2 fun x hx => (hW ⟨⟨x, hx⟩⟩).elim
    subst hb
    have := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEmpty)
    exact Subsingleton.elim _ _

theorem cechLB_X_noZSMulDivisors : ∀ {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X], CharZero Γ(X, ⊤) →
    ∀ (f : X ⟶ Sp ℤ) (M : LB X) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (n : ℕ) (m : ℤ), m ≠ 0 →
    ∀ x : (GlobalTheory.AbLaw.cechLB f M D).X n, m • x = 0 → x = 0 := by
  intro X _ hc f M κ _ D n m hm x hx
  have key : ∀ (V : X.Opens) (y : GlobalTheory.AbLaw.SecOnR (R := ℤ) f M V), m • y = 0 → y = 0 := by
    intro V y hy
    refine GlobalTheory.AbLaw.SecOnR.ext (R := ℤ) (f := f) fun i => ?_
    let c : GlobalTheory.AbLaw.SecOnR (R := ℤ) f M V →+ Γ(X, V ⊓ M.U i) :=
      { toFun := fun z => GlobalTheory.AbLaw.SecOnR.coord z i
        map_zero' := GlobalTheory.AbLaw.SecOnR.coord_zero i
        map_add' := fun z w => GlobalTheory.AbLaw.SecOnR.coord_add z w i }
    have hi : c (m • y) = c 0 := congrArg c hy
    rw [map_zsmul, map_zero, zsmul_eq_mul] at hi
    exact intCast_mul_eq_zero_of_isIntegral hc _ hm hi
  funext s
  refine key _ (x s) ?_
  exact congrFun hx s

end GlobalTheory.CechPic
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open GlobalTheory.LB (toMod)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechComplexLineBundle_term_torsionFree_charZero : ∀ {X : Scheme.{0}} [AlgebraicGeometry.IsIntegral X], CharZero Γ(X, ⊤) → ∀ (f : X ⟶ Sp ℤ) (M : LB X) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (n : ℕ) (m : ℤ), m ≠ 0 → ∀ x : (GlobalTheory.AbLaw.cechLB f M D).X n, m • x = 0 → x = 0 := by
  atlas_forward_decl GlobalTheory.CechPic.cechLB_X_noZSMulDivisors
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

noncomputable section

namespace GlobalTheory.ChiFibre

open GlobalTheory.AbLaw GlobalTheory.Adelic GlobalTheory.FieldChangeInter

theorem alternating_sum_range_telescoping_identity (a r : ℕ → ℤ) (m : ℕ) :
    ∑ n ∈ Finset.range m, (-1 : ℤ) ^ n * (a n + a (n + 1) - r (n + 1)) =
      ∑ n ∈ Finset.range m, (-1 : ℤ) ^ n * r n + (a 0 - r 0) + (-1) ^ m * (r m - a m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ]
    ring

theorem homology_subsingleton {R : Type} [Ring R] (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (h : IsZero (K.X n)) : Subsingleton (K.homology n) :=
  ModuleCat.subsingleton_of_isZero (ShortComplex.isZero_homology_of_isZero_X₂ (K.sc n) h)

theorem finite_int_congr {M : Type*} [AddCommGroup M] {i₁ i₂ : Module ℤ M}
    (h : @Module.Finite ℤ M _ _ i₁) : @Module.Finite ℤ M _ _ i₂ := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  exact h

theorem altSum (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime]
    (hinj : ∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0)
    (hfin : ∀ n, Module.Finite ℤ (C.homology n)) (m : ℕ) (hz : ∀ n, m ≤ n → IsZero (C.X n)) :
    ∑ᶠ n, (-1 : ℤ) ^ n * (Module.finrank (ZMod p) ((((ModuleCat.extendScalars
      (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) =
    ∑ᶠ n, (-1 : ℤ) ^ n * (Module.finrank ℚ ((((ModuleCat.extendScalars
      (Int.castRingHom ℚ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) := by
  set a : ℕ → ℤ := fun n => Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n))
  set r : ℕ → ℤ := fun n => Module.finrank ℤ (C.homology n)
  have hsub : ∀ n, m ≤ n → Subsingleton (C.homology n) :=
    fun n hn => homology_subsingleton C n (hz n hn)
  have hr0 : ∀ n, m ≤ n → r n = 0 := fun n hn => by
    haveI := hsub n hn
    simp only [r]
    rw [Module.finrank_zero_of_subsingleton]
    rfl
  have ha0 : ∀ n, m ≤ n → a n = 0 := fun n hn => by
    haveI := hsub n hn
    have : Subsingleton (TensorProduct ℤ (ZMod p) (C.homology n)) := inferInstance
    simp only [a]
    rw [Module.finrank_zero_of_subsingleton]
    rfl
  have hext : ∀ (F : Type) [Field F] (g : ℤ →+* F) (n : ℕ), m ≤ n →
      Module.finrank F ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj C).homology n) = 0 := by
    intro F _ g n hn
    have hZ : IsZero ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj C).X n) :=
      (ModuleCat.extendScalars g).map_isZero (hz n hn)
    haveI := homology_subsingleton _ n hZ
    exact Module.finrank_zero_of_subsingleton
  have hsupp : ∀ (F : Type) [Field F] (g : ℤ →+* F),
      (Function.support fun n => (-1 : ℤ) ^ n * (Module.finrank F ((((ModuleCat.extendScalars
        g).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ)) ⊆
        ↑(Finset.range m) := by
    intro F _ g n hn
    by_contra h
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
    exact hn (by simp [hext F g n h])
  rw [finsum_eq_sum_of_support_subset _ (hsupp (ZMod p) _),
    finsum_eq_sum_of_support_subset _ (hsupp ℚ _)]
  have h1 : ∀ n ∈ Finset.range m, (-1 : ℤ) ^ n * (Module.finrank (ZMod p) ((((ModuleCat.extendScalars
      (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) =
      (-1 : ℤ) ^ n * (a n + a (n + 1) - r (n + 1)) := fun n _ => by
    rw [GlobalTheory.T.finrank_homology_mod_prime_universal_coefficients C p hinj hfin n]
  have h2 : ∀ n ∈ Finset.range m, (-1 : ℤ) ^ n * (Module.finrank ℚ ((((ModuleCat.extendScalars
      (Int.castRingHom ℚ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) =
      (-1 : ℤ) ^ n * r n := fun n _ => by
    rw [GlobalTheory.T.finrank_rat_homology_eq_finrank_int C n (hfin n)]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, alternating_sum_range_telescoping_identity]
  have h0 : a 0 = r 0 := by
    simp only [a, r]
    exact_mod_cast GlobalTheory.T.finrank_zmod_tensor_homology_zero_of_noPTorsion C p (hinj 0) (hfin 0)
  rw [h0, hr0 m le_rfl, ha0 m le_rfl]
  ring

theorem hdim_fibre {X X' : Scheme.{0}} {F : Type} [Field F] (g : ℤ →+* F) (f : X ⟶ Sp ℤ)
    (f' : X' ⟶ Sp F) (π : X' ⟶ X) (H : IsPullback π f' f (spMap g)) {κ : Type} [LinearOrder κ]
    [Finite κ] (D : κ → X.Opens) (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) (M : LB X) (hM : M.IsLB)
    (n : ℕ) :
    (letI := GlobalTheory.algebraΓOfHom f'; hdim F (toMod (M.pull π)) n) =
      Module.finrank F ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (cechLB f M D)).homology n) := by
  letI := GlobalTheory.algebraΓOfHom f'
  have hM' := LB.isLB_pull hM π
  haveI := LB.isQuasicoherent_toMod hM'
  have hc' : ⨆ i, π ⁻¹ᵁ D i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hc]; rfl
  have hD' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, π ⁻¹ᵁ D i) :=
    fun s hs => isAffineOpen_biInf_preimage H (hD s hs)
  have e₁ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (cechIso f' (M.pull π) (fun i => π ⁻¹ᵁ D i))).toLinearEquiv ≪≫ₗ
    cechHEquivCoh F hc' hD' (toMod (M.pull π)) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (cechLBBaseChangeIso hM H hD)).toLinearEquiv
  rw [hdim_def, ← e₁.finrank_eq, ← e₄.finrank_eq]
  rfl

theorem chi_fibres_LB {X Xp Xq : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : CharZero Γ(X, ⊤))
    (f : X ⟶ Sp ℤ) (p : ℕ) [Fact p.Prime]
    (fp : Xp ⟶ Sp (ZMod p)) (πp : Xp ⟶ X) (Hp : IsPullback πp fp f (spMap (Int.castRingHom (ZMod p))))
    (fq : Xq ⟶ Sp ℚ) (πq : Xq ⟶ X) (Hq : IsPullback πq fq f (spMap (Int.castRingHom ℚ)))
    (M : LB X) (hM : M.IsLB)
    (hfin : ∀ n, letI := GlobalTheory.algebraΓOfHom f; Module.Finite ℤ (coh (twist (structureModule X) M) n)) :
    (letI := GlobalTheory.algebraΓOfHom fp; chi (ZMod p) (toMod (M.pull πp))) =
      (letI := GlobalTheory.algebraΓOfHom fq; chi ℚ (toMod (M.pull πq))) := by
  obtain ⟨m, Dc, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have hinj : ∀ (n : ℕ) (x : (cechLB f M Dc).X n), (p : ℤ) • x = 0 → x = 0 :=
    fun n x => GlobalTheory.T.cechComplexLineBundle_term_torsionFree_charZero hX f M Dc n (p : ℤ) (by exact_mod_cast (Fact.out : p.Prime).ne_zero) x
  have hz : ∀ n, m ≤ n → IsZero ((cechLB f M Dc).X n) :=
    fun n hn => isZero_cechLB_X f M Dc (by simpa using hn)
  have hfin' : ∀ n, Module.Finite ℤ ((cechLB f M Dc).homology n) := by
    intro n
    letI := GlobalTheory.algebraΓOfHom f
    obtain ⟨e⟩ := nonempty_coh_equiv f hM hc hD' n
    letI : Module ℤ (coh (twist (structureModule X) M) n) := cohOn.instModule ℤ _ ⊤ n
    haveI hf1 : Module.Finite ℤ (coh (twist (structureModule X) M) n) := finite_int_congr (hfin n)
    exact finite_int_congr (Module.Finite.equiv e.symm)
  letI := GlobalTheory.algebraΓOfHom fp
  letI := GlobalTheory.algebraΓOfHom fq
  rw [chi_def, chi_def]
  have hp := fun n => hdim_fibre (Int.castRingHom (ZMod p)) f fp πp Hp Dc hc hD' M hM n
  have hq := fun n => hdim_fibre (Int.castRingHom ℚ) f fq πq Hq Dc hc hD' M hM n
  simp only [hp, hq]
  exact altSum (cechLB f M Dc) p hinj hfin' m hz

theorem chi_structureModule_eq {X X' : Scheme.{0}} (F : Type) [Field F] [Algebra F Γ(X', ⊤)]
    (π : X' ⟶ X) : chi F (structureModule X') = chi F (toMod ((LB.triv X).pull π)) := by
  have h₀ := LB.isLB_triv X
  have h₁ := Semi.LB.isLB_pull h₀ π
  obtain ⟨e'⟩ := nonempty_twist_iso_of_cls_eq_zero (structureModule X') h₁
    ((CechPic.cls_pull h₀ π h₁).trans (map_zero _))
  rw [← chi_congr F e', chi_congr F (Twist.unitTwistIso _)]

theorem chi_fibre_eq : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (D : ℕ), IsArithVar q D → ∀ (p : ℕ) [Fact p.Prime] (N : LB W), N.IsLB → (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); chi (ZMod p) (toMod (N.pull (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) = chi ℚ (toMod (N.pull (ratFibre.fst q))) ∧ chi (ZMod p) (structureModule (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))) = chi ℚ (structureModule (ratFibre q))) := by
  intro k _ W q D hq p _ N hN
  haveI := hq.isDomain
  haveI := hq.finite
  haveI := hq.isIntegral
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  have hproj := hq.isProjOver
  haveI : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace q
  haveI := isAffineHom_diagonal_of_isSeparated q
  have hX : CharZero Γ(W, ⊤) := (flat_int_iff_charZero _).1 hq.flat
  have hfin : ∀ M : LB W, M.IsLB → ∀ n,
      letI := GlobalTheory.algebraΓOfHom (q ≫ spMap (Int.castRingHom k))
      Module.Finite ℤ (coh (twist (structureModule W) M) n) := by
    intro M hM n
    letI := GlobalTheory.algebraΓOfHom q
    have h1 : Module.Finite k (coh (twist (structureModule W) M) n) :=
      (((serre_finiteness_vanishing k W (structureModule W)).2 q (fun _ => rfl)).2
        (Or.inl hproj)).2.1 M hM n
    have h2 : Module.Finite ℤ (coh (twist (structureModule W) M) n) := Module.Finite.trans k _
    exact finite_int_congr h2
  refine ⟨chi_fibres_LB hX _ p _ _ (IsPullback.of_hasPullback _ _) _ _ (ratFibre.isPullback q) N hN
    (hfin N hN), ?_⟩
  letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k))
    (spMap (Int.castRingHom (ZMod p))))
  rw [chi_structureModule_eq (ZMod p) (pullback.fst _ _), chi_structureModule_eq ℚ (ratFibre.fst q)]
  exact chi_fibres_LB hX _ p _ _ (IsPullback.of_hasPullback _ _) _ _ (ratFibre.isPullback q) _
    (LB.isLB_triv W) (hfin _ (LB.isLB_triv W))

end GlobalTheory.ChiFibre
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerChar_lineBundle_fibre_modp_eq_rat_projective : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (D : ℕ), IsArithVar q D → ∀ (p : ℕ) [Fact p.Prime] (N : LB W), N.IsLB → (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); chi (ZMod p) (toMod (N.pull (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) = chi ℚ (toMod (N.pull (ratFibre.fst q))) ∧ chi (ZMod p) (structureModule (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))) = chi ℚ (structureModule (ratFibre q))) := by
  atlas_forward_decl GlobalTheory.ChiFibre.chi_fibre_eq
end
