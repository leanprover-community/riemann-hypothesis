import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUniqueOfBaseEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackCompFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenyPairBaseChangeGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveQcPow
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelStableIffPulledBackIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeIffPulledBackIdentityStatement
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PolKerAtPullbackOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteEtaleSurjectiveOfIsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieOfQuasiInverseIsogenyStatement
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsPolarizationDescentOfQuasiIsogeny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfPullbackQuasiInverseIsogenyTrivialAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleRosatiDescendedActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagRootPullbackQuasiInverseStatement
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PolarizationDescentAlongQuasiIsogenyCompat
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PowPolarizationIsoPullbackOfDescent
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PolarizationKernelOfPIsogenyQuasiInverse
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsObjMapOfPIsogenyPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyRepresentableFiniteEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenKernelStableHarrisTaylorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackKernelLocusIsClopenStatement
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsClopenLocusOfAnnihilator

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorPullback_comp_factors : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S₀ S₁ T : Scheme.{0}) (s₀ : S₀ ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (t : T ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o : GlobalTheory.UPel.HT.Obj b N t) (g : S₁ ⟶ S₀) (h : T ⟶ S₁), GlobalTheory.UPel.HT.ObjMap o₁ o₀ g → GlobalTheory.UPel.HT.ObjMap o o₀ (h ≫ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o o₁ h) := by
  first | exact @GlobalTheory.UPel.HT.PullFactor.objMap_factor | exact GlobalTheory.UPel.HT.PullFactor.objMap_factor | (intros; apply GlobalTheory.UPel.HT.PullFactor.objMap_factor <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverseIsogenyPair_baseChange_grpPullback : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ : A₁.left ⟶ A.left), IsAbelianScheme B → IsQuasiInv k ψ ψ' → IsGrpPullback A₁ A t φ → ∃ (B₁ : Over T) (_ : GrpObj B₁) (_ : IsCommMonObj B₁) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ ∧ IsGrpPullback B₁ B t θ ∧ IsQuasiInv k ψ₁ ψ₁' ∧ φ ≫ ψ.left = ψ₁.left ≫ θ ∧ θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  first | (exact @GlobalTheory.UPel.HT.ES.pullQuasiInv) | (exact GlobalTheory.UPel.HT.ES.pullQuasiInv) | (intros; apply GlobalTheory.UPel.HT.ES.pullQuasiInv  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.QCompat

theorem comp_quasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ B₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] [GrpObj B₁] [IsCommMonObj B₁] (φ : A₁.left ⟶ A.left) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ → 0 < k → IsQuasiInv k ψ ψ' → IsQuasiInv k ψ₁ ψ₁' → IsGrpPullback A₁ A t φ → φ ≫ ψ.left = ψ₁.left ≫ θ → θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  intro T Y t A B _ _ _ _ k ψ ψ' A₁ B₁ _ _ _ _ φ θ ψ₁ ψ₁' hB hk hq hq₁ hφ hsq
  obtain ⟨h1, h2, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow T B₁ hB k hk
  haveI : Epi ((𝟙 B₁) ^ k).left := Flat.epi_of_flat_of_surjective _
  have e₁ : ψ₁'.left ≫ ψ₁.left = ((𝟙 B₁) ^ k).left := by rw [← Over.comp_left, hq₁.2.2.2]
  haveI : Epi (ψ₁'.left ≫ ψ₁.left) := by rw [e₁]; infer_instance
  haveI : Epi ψ₁.left := epi_of_epi ψ₁'.left ψ₁.left
  rw [← cancel_epi ψ₁.left, ← Category.assoc, ← hsq, Category.assoc, ← Over.comp_left, hq.2.2.1,
    ← Category.assoc, ← Over.comp_left, hq₁.2.2.1]
  exact (GlobalTheory.LamF.IsGrpPullback.id_pow_left hφ k).symm

end GlobalTheory.UPel.HT.ES.QCompat
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverseIsogeny_square_compat_comp_quasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ B₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] [GrpObj B₁] [IsCommMonObj B₁] (φ : A₁.left ⟶ A.left) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ → 0 < k → IsQuasiInv k ψ ψ' → IsQuasiInv k ψ₁ ψ₁' → IsGrpPullback A₁ A t φ → φ ≫ ψ.left = ψ₁.left ≫ θ → θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  first | (exact @GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv) | (exact GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv) | (intros; apply GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.polKerAt_pullback_of_isGrpPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁' : B₁ ⟶ o₁.A) (ψ' : B ⟶ o.A) (c : ℕ), IsGrpPullback B₁ B t θ → θ ≫ ψ'.left = ψ₁'.left ≫ m.φ → (PolKerAt o ψ' c t ↔ PolKerAt o₁ ψ₁' c (𝟙 T)) := by
  first | exact @UpperTheory.Cb.polKerAt_pullback_of_isGrpPullback | exact UpperTheory.Cb.polKerAt_pullback_of_isGrpPullback
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_oAct_desc : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → KerStableAt o ψ (𝟙 Y) → ∃ act' : OActN D.O B, ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, he⟩ hB hq hst
  have hc : IsUnit (c : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [← Nat.cast_pow, map_natCast, ← he] at this
    exact this
  obtain ⟨hfin, het, hsurj⟩ := isFinite_etale_surjective_of_isQuasiInv Y o.A B c ψ ψ' o.ab hB hc hq
  haveI : Surjective ψ.left := hsurj
  haveI : Flat ψ.left := inferInstance
  haveI : QuasiCompact ψ.left := inferInstance
  haveI : IsMonHom ψ := hq.1
  have : Epi ψ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ
  have : Epi (ψ ⊗ₘ ψ) := GlobalTheory.FlatQuotient.epi_tensorHom ψ ψ
  have hd : ∀ a : D.O, ∃ t : B ⟶ B, ψ ≫ t = o.act.act a ≫ ψ := fun a => by
    haveI := o.act.hom a
    refine GlobalTheory.AbelianQuotient.exists_desc ψ (o.act.act a ≫ ψ) fun W x₁ x₂ h => ?_
    have h1 : (x₁ / x₂) ≫ ψ = 1 := by rw [GrpObj.div_comp, h, div_self']
    have h2 : (x₁ / x₂) ≫ o.act.act a ≫ ψ = 1 := hst W W.hom (Category.comp_id _) _ h1 a
    rwa [GrpObj.div_comp, div_eq_one] at h2
  choose t ht using hd
  refine ⟨{ act := t, hom := fun a => ?_, one := ?_, mul := fun a a' => ?_, add := fun a a' => ?_ },
    fun a => (ht a).symm⟩
  · haveI := o.act.hom a
    refine ⟨?_, ?_⟩
    · rw [← IsMonHom.one_hom (f := ψ), Category.assoc, ht, ← Category.assoc, IsMonHom.one_hom]
    · rw [← cancel_epi (ψ ⊗ₘ ψ), ← Category.assoc, ← IsMonHom.mul_hom, Category.assoc, ht,
        ← Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
        ← Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ht]
  · rw [← cancel_epi ψ, ht, o.act.one, Category.id_comp, Category.comp_id]
  · rw [← cancel_epi ψ, ht, o.act.mul, Category.assoc, ← ht, ← Category.assoc, ← ht, Category.assoc]
  · rw [← cancel_epi ψ, ht, o.act.add, Hom.mul_def, Hom.mul_def, comp_lift_assoc, ht, ht, ← lift_map, Category.assoc,
      Category.assoc, IsMonHom.mul_hom]

end GlobalTheory.UPel.HT.ES
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orderAction_descent_along_isogeny : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → KerStableAt o ψ (𝟙 Y) → ∃ act' : OActN D.O B, ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a := by
  first | (exact @GlobalTheory.UPel.HT.ES.exists_oAct_desc) | (exact GlobalTheory.UPel.HT.ES.exists_oAct_desc) | (intros; apply GlobalTheory.UPel.HT.ES.exists_oAct_desc  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_polarization_descent_of_quasi_isogeny : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) → ∃ P' : LB (G2 B).left, IsAxesTriv B P' ∧ LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) ∧ LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) := by
  first | exact @UpperTheory.Cb.exists_polarization_descent_of_quasi_isogeny | exact UpperTheory.Cb.exists_polarization_descent_of_quasi_isogeny
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.QuasiInvPull

theorem root_symm : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → LBIso P' (P'.pull (lift (snd B B) (fst B B)).left) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hc hB hq P' hP' _ H
  obtain ⟨e, rfl⟩ := hc
  have hpos : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hunit : IsUnit (((p ^ e : ℕ)) : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [← Nat.cast_pow, map_natCast] at this
  obtain ⟨hL, r₁, r₂⟩ := hP'
  set sw' := (lift (snd B B) (fst B B)).left with hsw'
  set sw := (lift (snd o.A o.A) (fst o.A o.A)).left with hsw
  set q := Hecke.sq2 ψ with hqdef
  have hQ : (P'.pull sw').IsLB := pull_isLB hL sw'
  have ax : ∀ (e₁ e₂ : B ⟶ G2 B), e₁ ≫ lift (snd B B) (fst B B) = e₂ →
      (∃ t : (P'.pull e₂.left).Gen, t.IsGen) → ∃ t : ((P'.pull sw').pull e₁.left).Gen, t.IsGen := by
    intro e₁ e₂ he ⟨t, ht⟩
    have hc : ∀ k : PUnit, (fun _ : PUnit => e₁.left) k ≫ sw' = 𝟙 _ ≫ (fun _ : PUnit => e₂.left) k := by
      intro _
      rw [Category.id_comp, hsw', ← Over.comp_left, he]
    have iso : LBIso ((P'.pull sw').pull e₁.left) (P'.pull e₂.left) :=
      LBIso.chartPull (chartPullLinComb P' sw' (fun _ => e₁.left) (fun _ => e₂.left) (fun _ => 1) (𝟙 _) hc)
        (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hL _))
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hL _) (pull_isLB hQ _) iso.symm t ht
  have a₁ := ax (lift (1 : B ⟶ B) (𝟙 B)) (lift (𝟙 B) (1 : B ⟶ B)) (by ext <;> simp) r₂
  have a₂ := ax (lift (𝟙 B) (1 : B ⟶ B)) (lift (1 : B ⟶ B) (𝟙 B)) (by ext <;> simp) r₁
  have E := GlobalTheory.HeckeSym.grpSchemeSquareProductMap_comm_swap ψ
  have hPow : (Hecke.lbPow o.P (p ^ e)).IsLB := DVR.linComb_isLB _ o.isLB _ _
  have step1 : LBIso (Hecke.lbPow o.P (p ^ e))
      (LB.LinComb (o.P.pull sw) (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb o.symm _ _
  have step2 : LBIso (LB.LinComb (o.P.pull sw) (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1))
      ((P'.pull sw').pull q) := by
    refine LBIso.chartPull (h := sw)
      (chartPullLinComb o.P sw (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) sw (fun _ => by simp))
      (chartPullLinComb P' sw' (fun _ : PUnit => q) (fun _ : PUnit => q) (fun _ => 1) sw (fun _ => E)) H
  have hmid : (LB.LinComb (o.P.pull sw) (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1)).IsLB :=
    DVR.linComb_isLB _ (pull_isLB o.isLB _) _ _
  have key : LBIso (P'.pull q) ((P'.pull sw').pull q) :=
    LBIso.trans (pull_isLB hL q) hPow (pull_isLB hQ q) H.symm
      (LBIso.trans hPow hmid (pull_isLB hQ q) step1 step2)
  exact lbIso_of_pullback_quasiInverseIsogeny_trivial_axes Y o.A B (p ^ e) ψ ψ' P' (P'.pull sw') hB hpos hunit hq ⟨hL, r₁, r₂⟩ ⟨hQ, a₁, a₂⟩ key

end GlobalTheory.QuasiInvPull
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverse_root_bundle_symmetric : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → LBIso P' (P'.pull (lift (snd B B) (fst B B)).left) := by
  first | (exact @GlobalTheory.QuasiInvPull.root_symm) | (exact GlobalTheory.QuasiInvPull.root_symm) | (intros; apply GlobalTheory.QuasiInvPull.root_symm  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.polarization_descent_along_quasi_isogeny_compat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over Y) (x : T ⟶ B), (∃ t : (P'.pull (lift (snd B T ≫ x) (fst B T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | exact @UpperTheory.Cb.polarization_descent_along_quasi_isogeny_compat | exact UpperTheory.Cb.polarization_descent_along_quasi_isogeny_compat
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.pow_polarization_iso_pullback_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Y) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ B) (fun a g => g ≫ act'.act a) (fun n g g' z => Out.WeilIs B (P'.pull (lift (𝟙 B) (𝟙 B)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y := by
  first | exact @UpperTheory.Cb.pow_polarization_iso_pullback_of_descent | exact UpperTheory.Cb.pow_polarization_iso_pullback_of_descent
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.polarization_kernel_of_p_isogeny_quasi_inverse : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) (ψ' : o'.A ⟶ o.A), IsUnit ((p : ℕ) : R) → IsPIsog c o o' ψ → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) := by
  first | exact @UpperTheory.Cb.polarization_kernel_of_p_isogeny_quasi_inverse | exact UpperTheory.Cb.polarization_kernel_of_p_isogeny_quasi_inverse
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_objMap_of_p_isogeny_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ o₁' : Obj b N s₁) (o o' : Obj b N s) (m : ObjMap o₁ o t) (ψ₁ : o₁.A ⟶ o₁'.A) (ψ : o.A ⟶ o'.A) (θ : o₁'.A.left ⟶ o'.A.left), IsUnit ((p : ℕ) : R) → IsPIsog c o₁ o₁' ψ₁ → IsPIsog c o o' ψ → IsGrpPullback o₁'.A o'.A t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → ∃ m' : ObjMap o₁' o' t, m'.φ = θ := by
  first | exact @UpperTheory.Cb.exists_objMap_of_p_isogeny_pullback | exact UpperTheory.Cb.exists_objMap_of_p_isogeny_pullback
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_clopen_locus_of_annihilator : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ TjAt r w j o ψ t := by
  first | exact @UpperTheory.Cb.exists_clopen_locus_of_annihilator | exact UpperTheory.Cb.exists_clopen_locus_of_annihilator
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogRep

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_comp {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
    {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem exists_factor (hN : 3 ≤ N) (hNp : N.Coprime p) {S₀ S₁ T : Scheme.{0}} {s₀ : S₀ ⟶ Sp R} {s₁ : S₁ ⟶ Sp R}
    {t : T ⟶ Sp R} {o₀ : Obj b N s₀} {o₁ : Obj b N s₁} {o : Obj b N t} {g : S₁ ⟶ S₀} {h : T ⟶ S₁} {x : T ⟶ S₀}
    (e : h ≫ g = x) (m₁ : ObjMap o₁ o₀ g) (m : ObjMap o o₀ x) : ∃ m' : ObjMap o o₁ h, m'.φ ≫ m₁.φ = m.φ := by
  subst e
  obtain ⟨m'⟩ := GlobalTheory.T.harrisTaylorPullback_comp_factors p D R b N _ _ _ _ _ _ o₀ o₁ o g h m₁ m
  obtain ⟨n, hn⟩ := exists_comp m' m₁
  exact ⟨m', hn.symm.trans (GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ _ _ _ _ n m rfl)⟩

theorem exists_pull {S S' : Scheme.{0}} {s : S ⟶ Sp R} (f : S' ⟶ S) (o : Obj b N s) {s' : S' ⟶ Sp R}
    (e : f ≫ s = s') : ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) := by
  subst e
  exact GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N S S' s f o

theorem isUnit_pow {S : Scheme.{0}} (s : S ⟶ Sp R) (hp : IsUnit ((p : ℕ) : R)) {c : ℕ} (hc : ∃ e : ℕ, c = p ^ e) :
    IsUnit (c : Γ(S, ⊤)) := by
  obtain ⟨e, rfl⟩ := hc
  have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  rwa [← Nat.cast_pow, map_natCast] at this

theorem exists_obj {c : ℕ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] {s : Y ⟶ Sp R} (o : Obj b N s) (B : Over Y)
    [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A) (hp : IsUnit ((p : ℕ) : R)) (hc : ∃ e : ℕ, c = p ^ e)
    (hB : IsAbelianScheme B) (hq : IsQuasiInv c ψ ψ') (h1 : KerStableAt o ψ (𝟙 Y)) (h2 : PolKerAt o ψ' c (𝟙 Y)) :
    ∃ (o' : Obj b N s) (χ : o.A ⟶ o'.A) (θ : o'.A.left ⟶ B.left), IsPIsog c o o' χ ∧
      IsGrpPullback o'.A B (𝟙 Y) θ ∧ ψ.left = χ.left ≫ θ := by
  obtain ⟨act', hact⟩ := GlobalTheory.T.exists_orderAction_descent_along_isogeny p D R b N c Y s o B ψ ψ' hp hc hB hq h1
  obtain ⟨P', hP', w1, w2⟩ := GlobalTheory.T.exists_polarization_descent_of_quasi_isogeny p D R b N c Y s o B ψ ψ' hp hc hB hq h2
  have hlie := GlobalTheory.T.harrisTaylor_lie_of_quasiInverseIsogeny p D R b N c Y s o B ψ ψ' hp hc hB hq act' hact
  haveI := hq.1
  let o' : Obj b N s :=
    { A := B, ab := hB, act := act', P := P', isLB := hP'.1, rig₁ := hP'.2.1, rig₂ := hP'.2.2
      symm := GlobalTheory.T.quasiInverse_root_bundle_symmetric p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2
      ample := GlobalTheory.T.relAmple_diag_root_pullback_quasiInverse p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2
      kerP := GlobalTheory.T.polarization_descent_along_quasi_isogeny_compat p D R b N c Y s o B ψ ψ' hp hc hB hq h2 P' hP' w1 w2
      rosati := GlobalTheory.T.quasiInverse_root_bundle_rosati_descended_action p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2 act' hact
      lie := hlie.1, lieRank := hlie.2
      eta := fun y => o.eta y ≫ ψ
      eta_add := fun x y => by rw [o.eta_add, MonObj.mul_comp]
      eta_lin := fun a x => by rw [o.eta_lin, Category.assoc, hact, Category.assoc]
      eta_ker := fun x => by rw [o.eta_ker, MonObj.one_comp]
      geom := GlobalTheory.T.pow_polarization_iso_pullback_of_descent p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2 act' hact }
  exact ⟨o', ψ, 𝟙 _, ⟨hc, hq.1, hact, fun _ => rfl, ⟨w2⟩, ψ', hq.2.1, hq.2.2.1, hq.2.2.2⟩,
    GlobalTheory.SiegLower.isGrpPullback_id B, (Category.comp_id _).symm⟩

end

theorem exists_rep : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (o₀ : Obj b N (Y.hom ≫ s)) (m₀ : ObjMap o₀ o Y.hom) (o' : Obj b N (Y.hom ≫ s)) (ψ : o₀.A ⟶ o'.A), IsFinite Y.hom ∧ Etale Y.hom ∧ IsPIsog c o₀ o' ψ ∧ IsTj r w j o₀ o' ψ ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (o₁ o₁' : Obj b N (x ≫ s)) (m : ObjMap o₁ o x) (ψ₁ : o₁.A ⟶ o₁'.A), IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (m₀' : ObjMap o₁ o₀ y) (m₁ : ObjMap o₁' o' y), m₀'.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ := by
  intro p _ D R _ _ b N hN hNp hp r w j c _ _ _ hc0 _ S _ s o
  have hc : ∃ e : ℕ, c = p ^ e := hc0.imp fun _ h => h.1
  have hcpos : 0 < c := by
    obtain ⟨e, rfl⟩ := hc
    exact pow_pos (Fact.out : p.Prime).pos e
  obtain ⟨Z, hZf, hZe, hZ⟩ := GlobalTheory.T.isogeny_representable_finite_etale S o.A c o.ab hcpos (isUnit_pow s hp hc)
  obtain ⟨oZ, ⟨mZ⟩⟩ := exists_pull Z.hom o rfl
  obtain ⟨B, _, _, ψ, ψ', hB, hq, huniv⟩ := hZ oZ.A mZ.φ mZ.cart
  obtain ⟨W₁, a₁, c₁, H₁⟩ := GlobalTheory.T.exists_clopen_kernelStable_harrisTaylor p D R b N c _ _ oZ B ψ ψ' hp hc hB hq
  obtain ⟨W₂, a₂, c₂, H₂⟩ := GlobalTheory.T.harrisTaylor_pullback_kernel_locus_isClopen p D R b N c _ _ oZ B ψ ψ' hp hc hB hq
  obtain ⟨W₃, a₃, c₃, H₃⟩ := GlobalTheory.T.exists_clopen_locus_of_annihilator p D R b N c _ _ oZ B ψ ψ' hp hc hB hq r w j
  haveI := hZf
  haveI := hZe
  obtain ⟨Y, i, hYf, hYe, hmono, Hi⟩ := GlobalTheory.LevCover.exists_sub (Z := Z)
    ⟨W₁ ∩ W₂ ∩ W₃, (a₁.inter a₂).inter a₃⟩ ((c₁.inter c₂).inter c₃)
  haveI := hYf
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have hi : Set.range i.left.base ⊆ W₁ ∩ W₂ ∩ W₃ := (Hi Y i).2 ⟨𝟙 Y, Category.id_comp i⟩
  obtain ⟨o₀, ⟨mi⟩⟩ := exists_pull i.left oZ (s' := Y.hom ≫ s) (by rw [← Category.assoc, Over.w i])
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ObjMap o₀ o Y.hom, m₀.φ = mi.φ ≫ mZ.φ := by
    have H : ∀ g, i.left ≫ Z.hom = g → ∃ m₀ : ObjMap o₀ o g, m₀.φ = mi.φ ≫ mZ.φ := by
      rintro _ rfl
      exact exists_comp mi mZ
    exact H _ (Over.w i)
  obtain ⟨B₀, _, _, θ₀, ψ₀, ψ₀', hB₀, hθ₀, hq₀, e₀, e₀'⟩ :=
    GlobalTheory.T.quasiInverseIsogenyPair_baseChange_grpPullback _ _ i.left oZ.A B c ψ ψ' o₀.A mi.φ hB hq mi.cart
  obtain ⟨o', χ, θ₁, hχ, hθ₁, e₁⟩ := exists_obj o₀ B₀ ψ₀ ψ₀' hp hc hB₀ hq₀
    ((GlobalTheory.T.kernelStable_iff_pulledBack_identity p D R b N _ _ _ _ _ o₀ oZ mi B₀ B θ₀ ψ₀ ψ hθ₀ e₀).1 ((H₁ _ _).1 fun z hz => (hi hz).1.1))
    ((GlobalTheory.T.polKerAt_pullback_of_isGrpPullback p D R b N _ _ _ _ _ o₀ oZ mi B₀ B θ₀ ψ₀' ψ' c hθ₀ e₀').1 ((H₂ _ _).1 fun z hz => (hi hz).1.2))
  have hθ : IsGrpPullback o'.A B i.left (θ₁ ≫ θ₀) := (hθ₁.comp hθ₀).congr (Category.id_comp _) rfl
  have eχ : mi.φ ≫ ψ.left = χ.left ≫ θ₁ ≫ θ₀ := by rw [e₀, e₁, Category.assoc]
  have htj : IsTj r w j o₀ o' χ := (tjAt_id_iff r w j o₀ o' χ).1
    ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o₀ oZ mi o'.A B (θ₁ ≫ θ₀) χ ψ r w j hθ eχ).1
      ((H₃ _ _).1 fun z hz => (hi hz).2))
  refine ⟨Y, o₀, m₀, o', χ, hYf, hYe, hχ, htj, fun T x o₁ o₁' m ψ₁ h1 h2 => ?_⟩
  obtain ⟨ψ₁', hq₁⟩ := h1.exists_quasiInv
  obtain ⟨z, ⟨hz, θ, θ', eθ, hθa, hθb, eψ⟩, zu⟩ := huniv T x o₁.A m.φ o₁'.A ψ₁ ψ₁' m.cart o₁'.ab hq₁
  obtain ⟨mz, hmz⟩ := exists_factor hN hNp hz mZ m
  obtain rfl : θ = mz.φ := mZ.cart.1.hom_ext (eθ.trans hmz.symm) (hθa.1.w.trans mz.cart.1.w.symm)
  have eψ' := GlobalTheory.T.quasiInverseIsogeny_square_compat_comp_quasiInv _ _ z oZ.A B c ψ ψ' o₁.A o₁'.A mz.φ θ' ψ₁ ψ₁' o₁'.ab hcpos hq hq₁ mz.cart eψ
  have hr : Set.range z.base ⊆ W₁ ∩ W₂ ∩ W₃ := Set.subset_inter (Set.subset_inter
    ((H₁ _ z).2 ((GlobalTheory.T.kernelStable_iff_pulledBack_identity p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁ ψ hθb eψ).2 (h1.kerStableAt _)))
    ((H₂ _ z).2 ((GlobalTheory.T.polKerAt_pullback_of_isGrpPullback p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁' ψ' c hθb eψ').2
      (GlobalTheory.T.polarization_kernel_of_p_isogeny_quasi_inverse p D R b N c _ _ o₁ o₁' ψ₁ ψ₁' hp h1 hq₁))))
    ((H₃ _ z).2 ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁ ψ r w j hθb eψ).2
      ((tjAt_id_iff r w j o₁ o₁' ψ₁).2 h2)))
  obtain ⟨y, hy⟩ := (Hi (Over.mk x) (Over.homMk z hz)).1 hr
  have hyz : y.left ≫ i.left = z := congrArg CommaMorphism.left hy
  haveI : Mono i.left := inferInstanceAs (Mono ((Over.forget S).map i))
  refine ⟨y.left, ⟨Over.w y, ?_⟩, ?_⟩
  · obtain ⟨m₀', hm⟩ := exists_factor hN hNp hyz mi mz
    let φ₁ : o₁'.A.left ⟶ o'.A.left := hθ.1.lift θ' (o₁'.A.hom ≫ y.left) (by rw [hθb.1.w, Category.assoc, hyz])
    have f1 : φ₁ ≫ θ₁ ≫ θ₀ = θ' := hθ.1.lift_fst _ _ _
    have f2 : φ₁ ≫ o'.A.hom = o₁'.A.hom ≫ y.left := hθ.1.lift_snd _ _ _
    have hφ₁ : IsGrpPullback o₁'.A o'.A y.left φ₁ := hθ.cancel (hθb.congr hyz.symm f1.symm) f2
    have e : m₀'.φ ≫ χ.left = ψ₁.left ≫ φ₁ := by
      apply hθ.1.hom_ext
      · rw [Category.assoc, ← eχ, ← Category.assoc, hm, eψ, Category.assoc, f1]
      · rw [Category.assoc, Over.w χ, m₀'.cart.1.w, Category.assoc, f2, ← Category.assoc, Over.w ψ₁]
    obtain ⟨m₁, hm₁⟩ := GlobalTheory.T.exists_objMap_of_p_isogeny_pullback p D R b N c _ _ _ _ y.left o₁ o₁' o₀ o' m₀' ψ₁ χ φ₁ hp h1 hχ hφ₁ e
    exact ⟨m₀', m₁, by rw [hm₁, e]⟩
  · rintro y' ⟨hy', n₀, n₁, e⟩
    rw [← cancel_mono i.left, hyz]
    have hx : (y' ≫ i.left) ≫ Z.hom = x := by rw [Category.assoc, Over.w i, hy']
    obtain ⟨n, hn⟩ := exists_comp n₀ mi
    obtain ⟨n', hn'⟩ := exists_comp n mZ
    refine zu _ ⟨hx, n₀.φ ≫ mi.φ, n₁.φ ≫ θ₁ ≫ θ₀, ?_, n₀.cart.comp mi.cart, n₁.cart.comp hθ, ?_⟩
    · rw [← hn, ← hn']
      exact GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ _ _ _ _ n' m hx
    · rw [Category.assoc, eχ, ← Category.assoc, e, Category.assoc]

end GlobalTheory.UPel.HT.ES.IsogRep
end
end
