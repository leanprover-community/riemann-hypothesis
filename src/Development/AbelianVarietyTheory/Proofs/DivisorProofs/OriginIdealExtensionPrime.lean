import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOrigin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalRingOfIsIntegralOfHenselian

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_isLocalRing_of_unique_prime_over : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [IsLocalRing L] [Algebra.IsIntegral P T] (𝔐 : Ideal T) [𝔐.IsPrime],
    𝔐.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) →
    (∀ 𝔔 : Ideal T, 𝔔.IsPrime → 𝔔.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) → 𝔔 = 𝔐) →
    (∀ y : L, ∃ a : P, y - algebraMap P L a ∈ maximalIdeal L) →
    IsLocalRing (TensorProduct P T L) := by
  intro P T L _ _ _ _ _ _ _ 𝔐 _ hM huniq hres

  let fκ : P →ₐ[P] L ⧸ maximalIdeal L := Algebra.ofId P _
  have hfκ : ∀ a, fκ a = Ideal.Quotient.mk (maximalIdeal L) (algebraMap P L a) := fun a => rfl
  have hsurj : Function.Surjective fκ := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hres y
    exact ⟨a, by rw [hfκ]; exact (Ideal.Quotient.eq.mpr ha).symm⟩
  have hker : RingHom.ker fκ = (maximalIdeal L).comap (algebraMap P L) := by
    ext a
    rw [RingHom.mem_ker, hfκ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
  let e : (P ⧸ RingHom.ker fκ) ≃ₐ[P] L ⧸ maximalIdeal L := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let q : (P ⧸ RingHom.ker fκ) →ₐ[P] T ⧸ 𝔐 :=
    Ideal.quotientMapₐ 𝔐 (Algebra.ofId P T) (le_of_eq (by rw [hker, ← hM]; rfl))
  let g : L →ₐ[P] T ⧸ 𝔐 := (q.comp e.symm.toAlgHom).comp (Ideal.Quotient.mkₐ P (maximalIdeal L))
  have hg : ∀ a : P, ∀ y : L, y - algebraMap P L a ∈ maximalIdeal L →
      g y = Ideal.Quotient.mk 𝔐 (algebraMap P T a) := by
    intro a y hy
    have h1 : Ideal.Quotient.mkₐ P (maximalIdeal L) y = Ideal.Quotient.mkₐ P (maximalIdeal L) (algebraMap P L a) := by
      rw [Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq.mpr hy
    have h2 : g y = g (algebraMap P L a) := by
      simp only [g, AlgHom.comp_apply]; rw [h1]
    rw [h2, AlgHom.commutes]; rfl
  let ψ : TensorProduct P T L →ₐ[P] T ⧸ 𝔐 :=
    Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ P 𝔐) g (fun _ _ => Commute.all _ _)
  have hψ : ∀ t y, ψ (t ⊗ₜ[P] y) = Ideal.Quotient.mk 𝔐 t * g y := by
    intro t y; simp [ψ, Algebra.TensorProduct.lift_tmul]
  haveI : Nontrivial (T ⧸ 𝔐) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨t ⊗ₜ[P] 1, by rw [hψ, map_one, mul_one]⟩
  haveI : Nontrivial (TensorProduct P T L) := hψs.nontrivial

  letI : Algebra L (TensorProduct P T L) := Algebra.TensorProduct.rightAlgebra
  have hmap : ∀ x, algebraMap L (TensorProduct P T L) x = (1 : T) ⊗ₜ[P] x := fun _ => rfl
  have hint : Algebra.IsIntegral L (TensorProduct P T L) := by
    constructor
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | add a b ha hb => exact ha.add hb
    | tmul a b =>
      have h1 : a ⊗ₜ[P] b = (a ⊗ₜ[P] (1 : L)) * algebraMap L (TensorProduct P T L) b := by
        rw [hmap]; simp
      rw [h1]
      refine IsIntegral.mul ?_ isIntegral_algebraMap
      have ha : IsIntegral P a := Algebra.IsIntegral.isIntegral a
      have h2 : IsIntegral P (a ⊗ₜ[P] (1 : L)) :=
        ha.map (Algebra.TensorProduct.includeLeft : T →ₐ[P] TensorProduct P T L)
      obtain ⟨p, hp, hp0⟩ := h2
      refine ⟨p.map (algebraMap P L), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap L (TensorProduct P T L)).comp (algebraMap P L) = algebraMap P _ := by
        ext x
        exact (Algebra.TensorProduct.includeRight : L →ₐ[P] TensorProduct P T L).commutes x
      rw [this]; exact hp0
  have hPB : ∀ a : P, (algebraMap P T a) ⊗ₜ[P] (1 : L) = (1 : T) ⊗ₜ[P] (algebraMap P L a) := by
    intro a
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have key : ∀ 𝔫 : Ideal (TensorProduct P T L), 𝔫.IsMaximal → 𝔫 = RingHom.ker ψ := by
    intro 𝔫 h𝔫
    have hLmax : (𝔫.comap (algebraMap L (TensorProduct P T L))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := L) 𝔫
    have hL : 𝔫.comap (algebraMap L (TensorProduct P T L)) = maximalIdeal L :=
      IsLocalRing.eq_maximalIdeal hLmax
    let iT : T →+* TensorProduct P T L := Algebra.TensorProduct.includeLeftRingHom
    have hiT : ∀ t, iT t = t ⊗ₜ[P] (1 : L) := fun _ => rfl
    have hcomp : iT.comp (algebraMap P T) = (algebraMap L (TensorProduct P T L)).comp (algebraMap P L) := by
      ext a; simp only [RingHom.comp_apply, hiT, hmap]; exact hPB a
    have hT : 𝔫.comap iT = 𝔐 := by
      apply huniq
      · exact Ideal.comap_isPrime iT 𝔫
      · rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hL]
    let j : T ⧸ 𝔐 →+* TensorProduct P T L ⧸ 𝔫 := Ideal.quotientMap 𝔫 iT hT.ge
    have hj : Function.Injective j := Ideal.quotientMap_injective' hT.le
    have hφ : ∀ b, Ideal.Quotient.mk 𝔫 b = j (ψ b) := by
      intro b
      induction b using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
      | tmul t y =>
        obtain ⟨a, ha⟩ := hres y
        have hy1 : (1 : T) ⊗ₜ[P] (y - algebraMap P L a) ∈ 𝔫 := by
          rw [← hmap, ← Ideal.mem_comap, hL]; exact ha
        have hsplit : t ⊗ₜ[P] y - (t * algebraMap P T a) ⊗ₜ[P] (1 : L) = (t ⊗ₜ[P] (1 : L)) * ((1 : T) ⊗ₜ[P] (y - algebraMap P L a)) := by
          rw [TensorProduct.tmul_sub, mul_sub, ← hPB]
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [hψ, hg a y ha, ← map_mul]
        show _ = Ideal.quotientMap 𝔫 iT hT.ge (Ideal.Quotient.mk 𝔐 (t * algebraMap P T a))
        rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, hiT, hsplit]
        exact 𝔫.mul_mem_left _ hy1
    ext b
    rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, RingHom.mem_ker, map_eq_zero_iff j hj]
  obtain ⟨𝔫₀, h0⟩ := Ideal.exists_maximal (TensorProduct P T L)
  exact IsLocalRing.of_unique_max_ideal ⟨𝔫₀, h0, fun 𝔫 h => (key 𝔫 h).trans (key 𝔫₀ h0).symm⟩

end GlobalTheory
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalRing_tensor_of_unique_prime_over : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [IsLocalRing L] [Algebra.IsIntegral P T] (𝔐 : Ideal T) [𝔐.IsPrime],
    𝔐.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) →
    (∀ 𝔔 : Ideal T, 𝔔.IsPrime → 𝔔.comap (algebraMap P T) = (maximalIdeal L).comap (algebraMap P L) → 𝔔 = 𝔐) →
    (∀ y : L, ∃ a : P, y - algebraMap P L a ∈ maximalIdeal L) →
    IsLocalRing (TensorProduct P T L) := by
  first | (exact @GlobalTheory.tensor_isLocalRing_of_unique_prime_over) | (exact GlobalTheory.tensor_isLocalRing_of_unique_prime_over) | (intros; apply GlobalTheory.tensor_isLocalRing_of_unique_prime_over  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_localization_atPrime_isDomain_of_isLocalRing_etale :
    ∀ (P R E : Type) [CommRing P] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra P R]
      [CommRing E] [Algebra P E] [Algebra.Etale P E] (Q : Ideal E) [Q.IsPrime],
      IsLocalRing (TensorProduct P R (Localization.AtPrime Q)) →
        IsDomain (TensorProduct P R (Localization.AtPrime Q)) := by
  intro P R E _ _ _ _ _ _ _ _ Q _ hloc
  letI : Algebra (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    (Algebra.TensorProduct.map (AlgHom.id P R)
      (IsScalarTower.toAlgHom P E (Localization.AtPrime Q))).toAlgebra
  haveI : IsScalarTower R (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI hl := IsLocalization.tensorProduct_tensorProduct_right P R Q.primeCompl
    (Localization.AtPrime Q) (by ext; simp [RingHom.algebraMap_toAlgebra])
  let 𝔭 : Ideal (R ⊗[P] E) :=
    (maximalIdeal (R ⊗[P] Localization.AtPrime Q)).comap
      (algebraMap (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q))
  haveI : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hle : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)) ≤
      𝔭.primeCompl := by
    intro x hx
    have hu := IsLocalization.map_units (R ⊗[P] Localization.AtPrime Q)
      (⟨x, hx⟩ : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)))
    intro h
    exact ((mem_maximalIdeal _).mp (Ideal.mem_comap.mp h)) hu
  haveI : IsLocalization 𝔭.primeCompl (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.of_le _ _ hle (fun r hr => by
      by_contra hu
      exact hr (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr hu)))
  obtain ⟨hd, -⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R (R ⊗[P] E) 𝔭
  let e : Localization.AtPrime 𝔭 ≃ₐ[R ⊗[P] E] (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.algEquiv 𝔭.primeCompl _ _
  exact e.symm.injective.isDomain _

end GlobalTheory
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_tensor_atPrime_of_isLocalRing_of_etale : ∀ (P R E : Type) [CommRing P] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra P R] [CommRing E] [Algebra P E] [Algebra.Etale P E] (Q : Ideal E) [Q.IsPrime],
    IsLocalRing (TensorProduct P R (Localization.AtPrime Q)) → IsDomain (TensorProduct P R (Localization.AtPrime Q)) := by
  first | (exact @GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale) | (exact GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale) | (intros; apply GlobalTheory.tensor_localization_atPrime_isDomain_of_isLocalRing_etale <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.OriginResidue

theorem isSepClosed_of_ringEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) [IsSepClosed K] :
    IsSepClosed L := by
  refine ⟨fun p hp => ?_⟩
  have h := IsSepClosed.splits_domain (f := e.toRingHom) (p.map e.symm.toRingHom) hp.map
  rwa [Polynomial.map_map, show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from by
    ext; simp, Polynomial.map_id] at h

variable {A : Type} [CommRing A] [IsLocalRing A]

def constToResidue [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] :
    A →+* (GlobalTheory.KeyOriginCut.originIdeal A).ResidueField :=
  (algebraMap (Polynomial A) (GlobalTheory.KeyOriginCut.originIdeal A).ResidueField).comp Polynomial.C

theorem constToResidue_eq_zero [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] {a : A}
    (ha : a ∈ maximalIdeal A) : constToResidue a = 0 := by
  simp only [constToResidue, RingHom.comp_apply]
  rw [Ideal.algebraMap_residueField_eq_zero, GlobalTheory.LocalStage.mem_originIdeal_iff]
  simpa using ha

instance [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] : IsLocalHom (constToResidue (A := A)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have := constToResidue_eq_zero ((mem_maximalIdeal a).2 h)
  rw [this] at ha
  exact not_isUnit_zero ha

theorem algebraMap_eq_constToResidue [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] (f : Polynomial A) :
    algebraMap (Polynomial A) (GlobalTheory.KeyOriginCut.originIdeal A).ResidueField f =
      constToResidue (f.coeff 0) := by
  simp only [constToResidue, RingHom.comp_apply]
  rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero,
    GlobalTheory.LocalStage.mem_originIdeal_iff]
  simp

theorem lift_surjective [(GlobalTheory.KeyOriginCut.originIdeal A).IsPrime] :
    Function.Surjective (ResidueField.lift (constToResidue (A := A))) := by
  set p := GlobalTheory.KeyOriginCut.originIdeal A
  intro x
  obtain ⟨z, rfl⟩ := residue_surjective x
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  have hs : algebraMap (Polynomial A) p.ResidueField s ≠ 0 := by
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact s.2
  have key : residue _ (IsLocalization.mk' (Localization.AtPrime p) f s) *
      algebraMap (Polynomial A) p.ResidueField s = algebraMap (Polynomial A) p.ResidueField f := by
    rw [IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime p) p.ResidueField,
      IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime p) p.ResidueField f,
      ResidueField.algebraMap_eq, ← map_mul, IsLocalization.mk'_spec]
  refine ⟨residue A (f.coeff 0) / residue A ((s : Polynomial A).coeff 0), ?_⟩
  rw [map_div₀, ResidueField.lift_residue_apply, ResidueField.lift_residue_apply,
    ← algebraMap_eq_constToResidue, ← algebraMap_eq_constToResidue, ← key, mul_div_cancel_right₀ _ hs]

theorem residue_origin : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsSepClosed (ResidueField A)] (E : Type) [CommRing E] [Algebra (Polynomial A) E] [Algebra.Etale (Polynomial A) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A) E) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ y : Localization.AtPrime Q, ∃ a : Polynomial A, y - algebraMap (Polynomial A) (Localization.AtPrime Q) a ∈ maximalIdeal (Localization.AtPrime Q) := by
  intro A _ _ _ E _ _ _ Q _ hQ y
  set p := GlobalTheory.KeyOriginCut.originIdeal A with hp
  haveI : p.IsPrime := hQ ▸ Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨hQ.symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p Q
  haveI : IsSepClosed p.ResidueField := isSepClosed_of_ringEquiv
    (RingEquiv.ofBijective _ ⟨(ResidueField.lift (constToResidue (A := A))).injective, lift_surjective⟩)
  obtain ⟨x, hx⟩ := IsSepClosed.algebraMap_surjective p.ResidueField Q.ResidueField
    (residue (Localization.AtPrime Q) y)
  obtain ⟨c, rfl⟩ := lift_surjective x
  obtain ⟨c, rfl⟩ := residue_surjective c
  refine ⟨Polynomial.C c, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← hx, ResidueField.lift_residue_apply]
  simp only [constToResidue, RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime Q) Q.ResidueField, ResidueField.algebraMap_eq, sub_self]

end GlobalTheory.OriginResidue
end
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sub_mem_maximalIdeal_etale_over_origin : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsSepClosed (ResidueField A)] (E : Type) [CommRing E] [Algebra (Polynomial A) E] [Algebra.Etale (Polynomial A) E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A) E) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ y : Localization.AtPrime Q, ∃ a : Polynomial A, y - algebraMap (Polynomial A) (Localization.AtPrime Q) a ∈ maximalIdeal (Localization.AtPrime Q) := by
  first | (exact @GlobalTheory.OriginResidue.residue_origin) | (exact GlobalTheory.OriginResidue.residue_origin) | (intros; apply GlobalTheory.OriginResidue.residue_origin <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.NormalLocal

theorem exists_normal_local (A : Type) [CommRing A] [HenselianLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S) (_ : IsLocalRing S) (f : A →+* S),
      f.IsIntegral ∧ RingHom.ker f = 𝔭 := by
  let B := A ⧸ 𝔭
  let K := FractionRing B
  let S := integralClosure B K
  have : IsFractionRing S K := inferInstance
  have hic : IsIntegrallyClosed S := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance
  letI : Algebra A S := ((algebraMap B S).comp (Ideal.Quotient.mk 𝔭)).toAlgebra
  have h1 : (Ideal.Quotient.mk 𝔭).IsIntegral := RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
  have h2 : (algebraMap B S).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := B) x
  have hint : (algebraMap A S).IsIntegral := RingHom.IsIntegral.trans _ _ h1 h2
  haveI : Algebra.IsIntegral A S := ⟨fun x => hint x⟩
  have hloc : IsLocalRing S := GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A S
  have hinjK : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have hinj : Function.Injective (algebraMap B S) := by
    intro x y h
    exact hinjK (congrArg Subtype.val h)
  refine ⟨S, inferInstance, inferInstance, hic, hloc, algebraMap A S, hint, ?_⟩
  ext a
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  change (algebraMap B S) (Ideal.Quotient.mk 𝔭 a) = 0 ↔ _
  rw [← map_zero (algebraMap B S), hinj.eq_iff]

end GlobalTheory.NormalLocal
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_local_domain_over_henselian_prime : ∀ (A : Type) [CommRing A] [HenselianLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S) (_ : IsLocalRing S) (f : A →+* S), f.IsIntegral ∧ RingHom.ker f = 𝔭 := by
  first | (exact @GlobalTheory.NormalLocal.exists_normal_local) | (exact GlobalTheory.NormalLocal.exists_normal_local) | (intros; apply GlobalTheory.NormalLocal.exists_normal_local  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolyOrigin

theorem originIdeal_eq_comap (T : Type) [CommRing T] [IsLocalRing T] :
    GlobalTheory.KeyOriginCut.originIdeal T = (maximalIdeal T).comap (Polynomial.constantCoeff : Polynomial T →+* T) := by
  ext g
  rw [GlobalTheory.LocalStage.mem_originIdeal_iff, Ideal.mem_comap, Polynomial.constantCoeff_apply]

theorem originIdeal_isMaximal (T : Type) [CommRing T] [IsLocalRing T] :
    (GlobalTheory.KeyOriginCut.originIdeal T).IsMaximal := by
  rw [originIdeal_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective _ (fun a => ⟨Polynomial.C a, by simp⟩)

theorem mapRingHom_isIntegral {A S : Type} [CommRing A] [CommRing S] (f : A →+* S) (hf : f.IsIntegral) :
    (Polynomial.mapRingHom f).IsIntegral := by
  letI : Algebra (Polynomial A) (Polynomial S) := (Polynomial.mapRingHom f).toAlgebra
  have hC : ∀ s : S, IsIntegral (Polynomial A) (Polynomial.C s) := by
    intro s
    obtain ⟨P, hPm, hP⟩ := hf s
    refine ⟨P.map Polynomial.C, hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (Polynomial A) (Polynomial S)).comp Polynomial.C = Polynomial.C.comp f := by
      refine RingHom.ext fun a => ?_
      change Polynomial.map f (Polynomial.C a) = _
      simp
    rw [hcomp, ← Polynomial.hom_eval₂, hP, map_zero]
  have hX : IsIntegral (Polynomial A) (Polynomial.X : Polynomial S) := by
    have : algebraMap (Polynomial A) (Polynomial S) Polynomial.X = Polynomial.X := Polynomial.map_X f
    rw [← this]
    exact isIntegral_algebraMap
  intro p
  change IsIntegral (Polynomial A) p
  induction p using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => exact hp.add hq
  | monomial n a _ => exact (hC a).mul (hX.pow _)

theorem polyOrigin : ∀ (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S] (f : A →+* S), f.IsIntegral →
    (Polynomial.mapRingHom f).IsIntegral ∧ (GlobalTheory.KeyOriginCut.originIdeal S).IsPrime ∧
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    ∀ 𝔔 : Ideal (Polynomial S), 𝔔.IsPrime → 𝔔.comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A → 𝔔 = GlobalTheory.KeyOriginCut.originIdeal S := by
  intro A S _ _ _ _ f hf

  have hmA : (maximalIdeal S).comap f = maximalIdeal A := by
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf (maximalIdeal S)
    exact IsLocalRing.eq_maximalIdeal this
  haveI hloc : IsLocalHom f := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ (maximalIdeal S).comap f := by
      rw [hmA]; exact (mem_maximalIdeal a).mpr hna
    exact (mem_maximalIdeal _).mp this ha
  refine ⟨mapRingHom_isIntegral f hf, (originIdeal_isMaximal S).isPrime,
    GlobalTheory.LocalStage.comap_originIdeal f, ?_⟩
  intro 𝔔 h𝔔 hc
  have hXmem : (Polynomial.X : Polynomial S) ∈ 𝔔 := by
    have : (Polynomial.X : Polynomial A) ∈ 𝔔.comap (Polynomial.mapRingHom f) := by
      rw [hc, GlobalTheory.LocalStage.mem_originIdeal_iff]; simp
    simpa using this

  haveI : (𝔔.comap (Polynomial.C : S →+* Polynomial S)).IsPrime := Ideal.comap_isPrime _ _
  have hcC : (𝔔.comap (Polynomial.C : S →+* Polynomial S)).comap f = maximalIdeal A := by
    ext a
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have h1 : Polynomial.C (f a) = Polynomial.mapRingHom f (Polynomial.C a) := by simp
    rw [h1, ← Ideal.mem_comap, hc, GlobalTheory.LocalStage.mem_originIdeal_iff, Polynomial.coeff_C_zero]
  have hmax : (𝔔.comap (Polynomial.C : S →+* Polynomial S)).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hf _ (by rw [hcC]; infer_instance)
  have hP : 𝔔.comap (Polynomial.C : S →+* Polynomial S) = maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal hmax
  have hle : GlobalTheory.KeyOriginCut.originIdeal S ≤ 𝔔 := by
    intro g hg
    rw [GlobalTheory.LocalStage.mem_originIdeal_iff] at hg
    rw [← Polynomial.X_mul_divX_add g]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hXmem) ?_
    have : g.coeff 0 ∈ 𝔔.comap (Polynomial.C : S →+* Polynomial S) := by rw [hP]; exact hg
    exact this
  exact ((originIdeal_isMaximal S).eq_of_le h𝔔.ne_top hle).symm

end GlobalTheory.PolyOrigin
end
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.origin_ideal_unique_prime_over : ∀ (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S] (f : A →+* S), f.IsIntegral →
    (Polynomial.mapRingHom f).IsIntegral ∧ (GlobalTheory.KeyOriginCut.originIdeal S).IsPrime ∧
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    ∀ 𝔔 : Ideal (Polynomial S), 𝔔.IsPrime → 𝔔.comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A → 𝔔 = GlobalTheory.KeyOriginCut.originIdeal S := by
  first | (exact @GlobalTheory.PolyOrigin.polyOrigin) | (exact GlobalTheory.PolyOrigin.polyOrigin) | (intros; apply GlobalTheory.PolyOrigin.polyOrigin  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem flat_one_tmul_eq_zero_mem_map (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [Module.Flat P L] (I : Ideal P) :
    RingHom.ker (algebraMap P T) = I → ∀ y : L, (1 : T) ⊗ₜ[P] y = 0 → y ∈ I.map (algebraMap P L) := by
  intro hI y hy
  subst hI
  set K := RingHom.ker (algebraMap P T)
  let f : (P ⧸ K) →ₗ[P] T := (Ideal.Quotient.liftₐ K (Algebra.ofId P T) (fun a ha => RingHom.mem_ker.mp ha)).toLinearMap
  have hf : Function.Injective f := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    simpa [f] using hab
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := L) f hf
  have h0 : (1 : P ⧸ K) ⊗ₜ[P] y = 0 := by
    apply hinj
    rw [LinearMap.rTensor_tmul, map_zero]
    simpa [f] using hy
  have h1 := congrArg (TensorProduct.quotTensorEquivQuotSMul L K) h0
  rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h1
  rw [Ideal.smul_top_eq_map] at h1
  exact h1

end GlobalTheory
end

section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_tensor_kernel_mem_map_ideal : ∀ (P T L : Type) [CommRing P] [CommRing T] [CommRing L] [Algebra P T] [Algebra P L] [Module.Flat P L] (I : Ideal P),
    RingHom.ker (algebraMap P T) = I → ∀ y : L, (1 : T) ⊗ₜ[P] y = 0 → y ∈ I.map (algebraMap P L) := by
  first | (exact @GlobalTheory.flat_one_tmul_eq_zero_mem_map) | (exact GlobalTheory.flat_one_tmul_eq_zero_mem_map) | (intros; apply GlobalTheory.flat_one_tmul_eq_zero_mem_map  <;> assumption)
end

section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.OriginPrimes

theorem origin_primes : ∀ (A' : Type) [CommRing A'] [HenselianLocalRing A'] [IsSepClosed (ResidueField A')]
    (𝔭 : Ideal A') [𝔭.IsPrime] (E : Type) [CommRing E] [Algebra (Polynomial A') E]
    [Algebra.Etale (Polynomial A') E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A') E) = GlobalTheory.KeyOriginCut.originIdeal A' →
    (𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C)).IsPrime := by
  intro A' _ _ _ 𝔭 _ E _ _ _ Q _ hQ
  obtain ⟨S, _, _, _, _, f, hfi, hker⟩ := GlobalTheory.T.exists_normal_local_domain_over_henselian_prime A' 𝔭
  obtain ⟨hXi, hOp, hOc, hOu⟩ := GlobalTheory.T.origin_ideal_unique_prime_over A' S f hfi
  letI : Algebra (Polynomial A') (Polynomial S) := (Polynomial.mapRingHom f).toAlgebra
  haveI : Algebra.IsIntegral (Polynomial A') (Polynomial S) := ⟨hXi⟩
  have hmax : (maximalIdeal (Localization.AtPrime Q)).comap
      (algebraMap (Polynomial A') (Localization.AtPrime Q)) = GlobalTheory.KeyOriginCut.originIdeal A' := by
    have h0 : (maximalIdeal (Localization.AtPrime Q)).comap (algebraMap E (Localization.AtPrime Q)) = Q :=
      Localization.AtPrime.comap_maximalIdeal (I := Q)
    rw [IsScalarTower.algebraMap_eq (Polynomial A') E (Localization.AtPrime Q), ← Ideal.comap_comap,
      h0, hQ]
  haveI hloc : IsLocalRing (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) :=
    GlobalTheory.T.isLocalRing_tensor_of_unique_prime_over (Polynomial A') (Polynomial S) (Localization.AtPrime Q) (GlobalTheory.KeyOriginCut.originIdeal S)
      (by rw [hmax]; exact hOc) (by intro 𝔔 h1 h2; rw [hmax] at h2; exact hOu 𝔔 h1 h2)
      (GlobalTheory.T.exists_sub_mem_maximalIdeal_etale_over_origin A' E Q hQ)
  haveI hdom : IsDomain (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) :=
    GlobalTheory.T.isDomain_tensor_atPrime_of_isLocalRing_of_etale (Polynomial A') (Polynomial S) E Q hloc
  haveI : Module.Flat (Polynomial A') (Localization.AtPrime Q) :=
    Module.Flat.trans (Polynomial A') E (Localization.AtPrime Q)
  have hkerX : RingHom.ker (algebraMap (Polynomial A') (Polynomial S)) = 𝔭.map Polynomial.C := by
    change RingHom.ker (Polynomial.mapRingHom f) = _
    rw [Polynomial.ker_mapRingHom, hker]
  have hJ : 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) =
      (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) := by
    rw [Ideal.map_map]
  let g : Localization.AtPrime Q →+* TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q) :=
    (Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _).toRingHom
  have hg0 : ∀ y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C), g y = 0 := by
    rw [hJ]
    have hle : (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _)
        (algebraMap (Polynomial A') (Localization.AtPrime Q) m) = 0
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
      have : algebraMap (Polynomial A') (Polynomial S) m = 0 := by
        rw [← RingHom.mem_ker, hkerX]; exact hm
      rw [this, TensorProduct.zero_tmul]
    exact fun y hy => hle hy
  have hg1 : ∀ y, g y = 0 → y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) := by
    intro y hy
    rw [hJ]
    exact GlobalTheory.T.flat_tensor_kernel_mem_map_ideal (Polynomial A') (Polynomial S) (Localization.AtPrime Q) _ hkerX y hy
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 := hg0 1 (by rw [htop]; exact Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  · intro x y hxy
    have h := hg0 _ hxy
    rw [map_mul] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hg1 x h)
    · exact Or.inr (hg1 y h)

end GlobalTheory.OriginPrimes
end

section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.origin_ideal_extension_prime : ∀ (A' : Type) [CommRing A'] [HenselianLocalRing A'] [IsSepClosed (ResidueField A')]
    (𝔭 : Ideal A') [𝔭.IsPrime] (E : Type) [CommRing E] [Algebra (Polynomial A') E]
    [Algebra.Etale (Polynomial A') E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A') E) = GlobalTheory.KeyOriginCut.originIdeal A' →
    (𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C)).IsPrime := by
  first | (exact @GlobalTheory.OriginPrimes.origin_primes) | (exact GlobalTheory.OriginPrimes.origin_primes) | (intros; apply GlobalTheory.OriginPrimes.origin_primes <;> assumption)
end
