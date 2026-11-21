import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfThickeningsLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianLiftAmpleBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigLBCubical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpPowOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackSelf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor.CycLift

theorem charZero_witt (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    CharZero (WittVector p K) := by
  obtain ⟨l, hl⟩ := CharP.exists (WittVector p K)
  rcases CharP.char_is_prime_or_zero (WittVector p K) l with h | h
  · exfalso
    have h1 : ((l : ℕ) : WittVector p K) = 0 := CharP.cast_eq_zero _ l
    have h2 : ((l : ℕ) : K) = 0 := by
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) h1
      rwa [map_natCast, map_zero] at this
    have h4 : p = l := (Nat.prime_dvd_prime_iff_eq hp.out h).1 ((CharP.cast_eq_zero_iff K p l).1 h2)
    subst h4
    exact WittVector.p_nonzero p K h1
  · subst h
    exact CharP.charP_to_charZero _

theorem isPrimitiveRoot_zetaAway {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zetaAway n) n :=
  IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn)
    Subtype.val_injective

theorem hom_ext {n : ℕ} (hn : n ≠ 0) {R : Type} [CommRing R] (f g : cycAway n →+* R)
    (h : f (zetaAway n) = g (zetaAway n)) : f = g := by
  have hinv : ∀ hx : (n : ℂ)⁻¹ ∈ cycAway n, f ⟨(n : ℂ)⁻¹, hx⟩ = g ⟨(n : ℂ)⁻¹, hx⟩ := by
    intro hx
    have hu : (⟨(n : ℂ)⁻¹, hx⟩ : cycAway n) * (n : cycAway n) = 1 :=
      Subtype.ext (by simp [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)])
    have hf := congrArg f hu
    have hg := congrArg g hu
    rw [map_mul, map_natCast, map_one] at hf hg
    calc f ⟨(n : ℂ)⁻¹, hx⟩ = f ⟨(n : ℂ)⁻¹, hx⟩ * ((n : R) * g ⟨(n : ℂ)⁻¹, hx⟩) := by
          rw [_root_.mul_comm (n : R), hg, _root_.mul_one]
      _ = g ⟨(n : ℂ)⁻¹, hx⟩ := by rw [← _root_.mul_assoc, hf, _root_.one_mul]
  ext ⟨x, hx⟩
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h
    · exact hinv _
  | zero => exact (map_zero f).trans (map_zero g).symm
  | one => exact (map_one f).trans (map_one g).symm
  | add x y hx hy ihx ihy =>
    change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
    rw [map_add, map_add, ihx, ihy]
  | neg x hx ih =>
    change f (-⟨x, hx⟩) = g (-⟨x, hx⟩)
    rw [map_neg, map_neg, ih]
  | mul x y hx hy ihx ihy =>
    change f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [map_mul, map_mul, ihx, ihy]

end GlobalTheory.SiegelTor.CycLift

namespace GlobalTheory.SiegelTor.CycLift

theorem exists_hom {n : ℕ} (hn : n ≠ 0) {F : Type} [Field F] [CharZero F] {y : F} (hy : IsPrimitiveRoot y n) :
    ∃ f : cycAway n →+* F, Function.Injective f ∧ f (zetaAway n) = y := by
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  set z : ℂ := ((zetaAway n : cycAway n) : ℂ) with hzdef
  have hz : IsPrimitiveRoot z n := (isPrimitiveRoot_zetaAway hn).map_of_injective (f := (cycAway n).subtype) Subtype.val_injective
  have hint : IsIntegral ℚ z := (hz.isIntegral hpos).tower_top
  let pb := IntermediateField.adjoin.powerBasis hint
  have hgen : pb.gen = IntermediateField.AdjoinSimple.gen ℚ z := rfl
  have hroot : Polynomial.aeval y (minpoly ℚ pb.gen) = 0 := by
    have hmp : minpoly ℚ pb.gen = minpoly ℚ z := by
      exact IntermediateField.minpoly_gen ℚ z
    rw [hmp, ← Polynomial.cyclotomic_eq_minpoly_rat hz hpos, Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hy.isRoot_cyclotomic hpos
  let ψ := pb.lift y hroot
  have hle : cycAway n ≤ (IntermediateField.adjoin ℚ {z}).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ z
    · show _ ∈ IntermediateField.adjoin ℚ {z}
      exact inv_mem (IntermediateField.natCast_mem _ n)
  refine ⟨(ψ : IntermediateField.adjoin ℚ {z} →+* F).comp (Subring.inclusion hle), ?_, ?_⟩
  · exact ((ψ : IntermediateField.adjoin ℚ {z} →+* F).injective).comp (Subring.inclusion_injective hle)
  · change ψ pb.gen = y
    exact PowerBasis.lift_gen _ _ _

end GlobalTheory.SiegelTor.CycLift

namespace GlobalTheory.SiegelTor.CycLift

theorem exists_complete_domain_lift : ∀ (n : ℕ), 3 ≤ n → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K),
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsNoetherianRing V) (βV : cycAway n →+* V)
      (π : V →+* K), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Function.Injective βV ∧ Function.Surjective π ∧
        π.comp βV = β := by
  intro n hn3 K _ _ β
  have hn : n ≠ 0 := by omega
  have hβζ := isPrimitiveRoot_map hn β
  have hnK : (n : K) ≠ 0 := by simpa using ((isUnit_natCast hn).map β).ne_zero
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hpp | hp0
  · haveI : Fact p.Prime := ⟨hpp⟩
    haveI := charZero_witt p K
    have hinj := IsFractionRing.injective (WittVector p K) (FractionRing (WittVector p K))
    haveI : CharZero (FractionRing (WittVector p K)) := charZero_of_injective_algebraMap hinj
    have hc : ∀ a : K, (WittVector.constantCoeff : WittVector p K →+* K) (WittVector.teichmuller p a) = a :=
      fun a => by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    set t : WittVector p K := WittVector.teichmuller p (β (zetaAway n)) with ht_def
    have ht : IsPrimitiveRoot t n := by
      refine ⟨?_, fun l hl => hβζ.dvd_of_pow_eq_one l ?_⟩
      · rw [ht_def, ← map_pow, hβζ.pow_eq_one, map_one]
      · have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) hl
        rwa [map_pow, map_one, hc] at this
    obtain ⟨f, hf, hfζ⟩ := exists_hom hn (ht.map_of_injective hinj)
    have hnW : IsUnit (n : WittVector p K) :=
      WittVector.isUnit_of_coeff_zero_ne_zero _ (by rw [← WittVector.constantCoeff_apply, map_natCast]; exact hnK)
    have hmem : ∀ x, f x ∈ (algebraMap (WittVector p K) (FractionRing (WittVector p K))).range := by
      rintro ⟨x, hx⟩
      induction hx using Subring.closure_induction with
      | mem x hx =>
        rcases hx with rfl | hx'
        · exact ⟨t, hfζ.symm⟩
        · subst hx'
          refine ⟨↑hnW.unit⁻¹, ?_⟩
          apply mul_right_cancel₀ (Nat.cast_ne_zero.2 hn : (n : FractionRing (WittVector p K)) ≠ 0)
          have e1 : algebraMap (WittVector p K) (FractionRing (WittVector p K)) ↑hnW.unit⁻¹ * n = 1 := by
            rw [← map_natCast (algebraMap (WittVector p K) (FractionRing (WittVector p K))) n, ← map_mul,
              hnW.val_inv_mul, map_one]
          have hu : (⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway n) * (n : cycAway n) = 1 :=
            Subtype.ext (by simp [inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0)])
          have e2 := congrArg f hu
          rw [map_mul, map_natCast, map_one] at e2
          exact e1.trans e2.symm
      | zero => show f 0 ∈ _; rw [map_zero]; exact zero_mem _
      | one => show f 1 ∈ _; rw [map_one]; exact one_mem _
      | add x y hx hy ihx ihy =>
        show f (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _; rw [map_add]; exact add_mem ihx ihy
      | neg x hx ih => show f (-⟨x, hx⟩) ∈ _; rw [map_neg]; exact neg_mem ih
      | mul x y hx hy ihx ihy =>
        show f (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _; rw [map_mul]; exact mul_mem ihx ihy
    let e : WittVector p K ≃+* (algebraMap (WittVector p K) (FractionRing (WittVector p K))).range :=
      RingEquiv.ofBijective (algebraMap (WittVector p K) (FractionRing (WittVector p K))).rangeRestrict
        ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
    let βV : cycAway n →+* WittVector p K := e.symm.toRingHom.comp (f.codRestrict _ hmem)
    have hβV : ∀ x, algebraMap (WittVector p K) (FractionRing (WittVector p K)) (βV x) = f x := fun x =>
      congrArg Subtype.val (e.apply_symm_apply (f.codRestrict _ hmem x))
    refine ⟨WittVector p K, inferInstance, inferInstance, inferInstance, inferInstance, βV, WittVector.constantCoeff,
      ?_, ?_, ?_, ?_⟩
    · rw [(WittVector.irreducible p).maximalIdeal_eq]
      exact WittVector.isAdicCompleteIdealSpanP
    · exact fun a b h => hf (by rw [← hβV, ← hβV, h])
    · exact fun a => ⟨WittVector.teichmuller p a, hc a⟩
    · refine hom_ext hn _ _ ?_
      have h1 : βV (zetaAway n) = t := hinj (by rw [hβV, hfζ])
      show WittVector.constantCoeff (βV (zetaAway n)) = β (zetaAway n)
      rw [h1, hc]
  · subst hp0
    haveI : CharZero K := CharP.charP_to_charZero K
    obtain ⟨f, hf, hfζ⟩ := exists_hom hn hβζ
    have hβ : β = f := hom_ext hn _ _ hfζ.symm
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, β, RingHom.id K, ?_, hβ ▸ hf,
      fun x => ⟨x, rfl⟩, RingHom.id_comp β⟩
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance

end GlobalTheory.SiegelTor.CycLift
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeLocalDomain_lift_cyclotomicAway : ∀ (n : ℕ), 3 ≤ n → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K), ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsNoetherianRing V) (βV : cycAway n →+* V) (π : V →+* K), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Function.Injective βV ∧ Function.Surjective π ∧ π.comp βV = β := by
  atlas_forward_decl GlobalTheory.SiegelTor.CycLift.exists_complete_domain_lift
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_trivial_on_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (J : Ideal R), J ≤ Ideal.jacobson ⊥ → ∀ (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → ∀ M : LB B.left, M.IsLB → RelAmple B M → ∀ (Y₀ : Over (Spec (CommRingCat.of (R ⧸ J)))) [GrpObj Y₀] (b : Y₀.left ⟶ B.left), IsGrpPullback Y₀ B (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) b → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → KTriv Y₀ N₀ → KTriv B M := by
  first | exact @GlobalTheory.KTrivJacobson.kTriv_of_quotient | exact GlobalTheory.KTrivJacobson.kTriv_of_quotient | (intros; apply GlobalTheory.KTrivJacobson.kTriv_of_quotient <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
theorem _root_.GlobalTheory.T.exists_abelian_lift_ample_bundle : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀], IsAbelianScheme Y₀ → ∀ L₀ : LB Y₀.left, L₀.IsLB → RelAmple Y₀ L₀ → KTriv Y₀ L₀ → ∃ (Y : Over (Sp R)) (_ : GrpObj Y) (L : LB Y.left) (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L ∧ IsGrpPullback Y₀ Y (spMap π) i ∧ LBIso L₀ (L.pull i) := by
  first | exact @GlobalTheory.SqStep.exists_lift | exact GlobalTheory.SqStep.exists_lift | (intros; apply GlobalTheory.SqStep.exists_lift <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumLift

theorem ker_factor_sq {R : Type} [CommRing R] (J : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R ⧸ J ^ (e + 1 + 1) →+* R ⧸ J ^ (e + 1)) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx hy
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have h := Ideal.mul_mem_mul hx hy
  rw [← pow_add] at h
  exact Ideal.pow_le_pow_right (by omega) h

theorem exists_lift_of_step (step : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀], IsAbelianScheme Y₀ → ∀ L₀ : LB Y₀.left, L₀.IsLB → RelAmple Y₀ L₀ → KTriv Y₀ L₀ → ∃ (Y : Over (Sp R)) (_ : GrpObj Y) (L : LB Y.left) (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L ∧ IsGrpPullback Y₀ Y (spMap π) i ∧ LBIso L₀ (L.pull i)) : ∀ (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsDomain R] [IsLocalRing R], IsAdicComplete (maximalIdeal R₁) R₁ → ∀ π : R₁ →+* R, Function.Surjective π → ∀ Q : GlobalTheory.PolDeg.Data R, ∃ (A : Over (Sp R₁)) (_ : GrpObj A) (_ : IsCommMonObj A) (i : Q.B.left ⟶ A.left) (l : (Q.B ⊗ Q.B).left ⟶ (A ⊗ A).left) (N : LB (A ⊗ A).left), IsAbelianScheme A ∧ IsGrpPullback Q.B A (spMap π) i ∧ IsSquare i l ∧ N.IsLB ∧ GlobalTheory.AbDual.IsAdditive N ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap N) ∧ LBIso (N.pull l) (abelian₂ Q.B Q.M.L) := by
  intro R₁ R _ _ _ _ _ _ _ hc π hπ Q
  set I := RingHom.ker π with hI
  have hItop : I ≠ ⊤ := by
    intro h
    have h1 : (1 : R₁) ∈ I := h ▸ Submodule.mem_top
    rw [hI, RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hIc : IsAdicComplete I R₁ := GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' R₁ I (maximalIdeal R₁) (le_maximalIdeal hItop) hc
  have hne : ∀ e : ℕ, I ^ (e + 1) ≠ ⊤ := fun e h =>
    hItop (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  haveI hnt : ∀ e : ℕ, Nontrivial (R₁ ⧸ I ^ (e + 1)) := fun e => Ideal.Quotient.nontrivial_iff.2 (hne e)
  haveI hloc : ∀ e : ℕ, IsLocalRing (R₁ ⧸ I ^ (e + 1)) := fun e =>
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let St : ℕ → Type 1 := fun e => Σ Y : Over (Sp (R₁ ⧸ I ^ (e + 1))), Σ _ : GrpObj Y,
    {L : LB Y.left // IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L}
  have hstep : ∀ (e : ℕ) (y : St e), ∃ (y' : St (e + 1)) (i : y.1.left ⟶ y'.1.left),
      @IsGrpPullback _ _ y.1 y.2.1 y'.1 y'.2.1 (thickTrans R₁ I e) i ∧ LBIso y.2.2.1 (y'.2.2.1.pull i) := by
    rintro e ⟨Y, g, L, hA, hL, ha, hK⟩
    obtain ⟨Y', g', L', i, hA', hL', ha', hK', hi, hLi⟩ := step (R₁ ⧸ I ^ (e + 1 + 1)) (R₁ ⧸ I ^ (e + 1))
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))))
      (Ideal.Quotient.factor_surjective _) (ker_factor_sq I e) Y hA L hL ha hK
    exact ⟨⟨Y', g', L', hA', hL', ha', hK'⟩, i, hi, hLi⟩
  choose nx β hβ hLβ using hstep
  let e₀ : R₁ ⧸ I ^ (0 + 1) ≃+* R :=
    (Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).trans (RingHom.quotientKerEquivOfSurjective hπ)
  let s : Sp (R₁ ⧸ I ^ (0 + 1)) ⟶ Sp R := spMap (e₀.symm : R →+* R₁ ⧸ I ^ (0 + 1))
  let t : Sp R ⟶ Sp (R₁ ⧸ I ^ (0 + 1)) := spMap (e₀ : R₁ ⧸ I ^ (0 + 1) →+* R)
  have hts : t ≫ s = 𝟙 _ := by
    simp only [t, s, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [RingEquiv.comp_symm]
    simp
  have htπ : t ≫ thick R₁ I 0 = spMap π := by
    simp only [t, thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let Y₀ : Over (Sp (R₁ ⧸ I ^ (0 + 1))) := (Over.pullback s).obj Q.B
  let g₀ : Y₀.left ⟶ Q.B.left := pullback.fst Q.B.hom s
  have G₀ : IsGrpPullback Y₀ Q.B s g₀ := isGrpPullback_pullback Q.B s
  have hL₀ : (Q.M.L.pull g₀).IsLB := pull_isLB Q.M.isLB g₀
  have hA₀ : IsAbelianScheme Y₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback Q.isAb G₀
  haveI := Q.isAb.proper
  have ha₀ : RelAmple Y₀ (Q.M.L.pull g₀) := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback Q.M.isLB Q.ample G₀.1
  have hK₀ : KTriv Y₀ (Q.M.L.pull g₀) := by
    obtain ⟨w, hw⟩ : LBIso (Q.M.L.pull g₀) (Q.M.L.pull g₀) := (GlobalTheory.CechPic.cls_eq_iff hL₀ hL₀).1 rfl
    exact kTriv_pull G₀ Q.M.isLB hL₀ ((isGen_iff w).1 hw) Q.ktriv
  let y₀ : St 0 := ⟨Y₀, inferInstance, Q.M.L.pull g₀, hA₀, hL₀, ha₀, hK₀⟩
  let Y : ∀ n : ℕ, St n := fun n => Nat.rec (motive := fun n => St n) y₀ (fun n y => nx n y) n
  letI : ∀ e, GrpObj (Y e).1 := fun e => (Y e).2.1
  obtain ⟨B, _, M, b, hB, hM, haM, hb, -, hiso⟩ := GlobalTheory.AlgGroup.exists_abelianScheme_of_tower R₁ I hItop hIc hc
    (fun e => (Y e).1) (fun e => β e (Y e)) (fun e => (Y e).2.2.2.1) (fun e => hβ e (Y e))
    (fun e => (Y e).2.2.1) (fun e => (Y e).2.2.2.2.1) (fun e => hLβ e (Y e)) (Y 0).2.2.2.2.2.1
  haveI : IsCommMonObj B := hB.comm
  let φ : Q.B.left ⟶ Y₀.left := pullback.lift (𝟙 _) (Q.B.hom ≫ t)
    (by rw [Category.id_comp, Category.assoc, hts, Category.comp_id])
  have hφ₁ : φ ≫ g₀ = 𝟙 _ := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ Y₀.hom = Q.B.hom ≫ t := pullback.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl Q.B).hom := inferInstanceAs (IsMonHom (𝟙 Q.B))
  have n₀ : IsGrpPullback Q.B Q.B (t ≫ s) (φ ≫ g₀) :=
    (isGrpPullback_of_iso (Iso.refl Q.B)).congr hts.symm hφ₁.symm
  have hcan : IsGrpPullback Q.B Y₀ t φ := IsGrpPullback.cancel G₀ n₀ hφ₂
  have hi : IsGrpPullback Q.B B (spMap π) (φ ≫ b 0) := (hcan.comp (hb 0)).congr htπ rfl
  have hLi : LBIso Q.M.L (M.pull (φ ≫ b 0)) := by
    refine (GlobalTheory.CechPic.cls_eq_iff Q.M.isLB (pull_isLB hM _)).1 ?_
    have a₂ : GlobalTheory.CechPic.cls _ hL₀ = GlobalTheory.CechPic.cls _ (pull_isLB hM (b 0)) :=
      (GlobalTheory.CechPic.cls_eq_iff _ _).2 (hiso 0)
    rw [GlobalTheory.CechPic.cls_pull hM, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hM (b 0) (pull_isLB hM (b 0)), ← a₂,
      GlobalTheory.CechPic.cls_pull Q.M.isLB, ← GlobalTheory.CechPic.pull_comp, hφ₁, GlobalTheory.CechPic.pull_id]
  have hJ : I ^ (0 + 1) ≤ Ideal.jacobson ⊥ :=
    (Ideal.pow_le_self (Nat.succ_ne_zero 0)).trans (IsAdicComplete.le_jacobson_bot I)
  have hK : KTriv B M := GlobalTheory.T.line_bundle_trivial_on_fibre R₁ (I ^ (0 + 1)) hJ B hB M hM haM Y₀ (b 0) (hb 0) _ hL₀ (hiso 0) hK₀
  have hP := GlobalTheory.AbDual.isPerfect_lam hM hK
  obtain ⟨H, hH, aH⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod hB hB hM haM hM haM
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv hB hB hH aH hP.isLB hP.zero_left hP.zero_right
  have w : (φ ≫ b 0) ≫ B.hom = Q.B.hom ≫ spMap π := hi.1.w
  exact ⟨B, inferInstance, hB.comm, φ ≫ b 0, _, abelian₂ B M, hB, hi, GlobalTheory.LamPull.exists_isSquare w, hP.isLB, a₁, a₂,
    (GlobalTheory.LamPull.lbIso_lam_pull hi hM Q.M.isLB hLi (GlobalTheory.LamPull.exists_isSquare w)).symm⟩

theorem exists_lift : ∀ (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsDomain R] [IsLocalRing R], IsAdicComplete (maximalIdeal R₁) R₁ → ∀ π : R₁ →+* R, Function.Surjective π → ∀ Q : GlobalTheory.PolDeg.Data R, ∃ (A : Over (Sp R₁)) (_ : GrpObj A) (_ : IsCommMonObj A) (i : Q.B.left ⟶ A.left) (l : (Q.B ⊗ Q.B).left ⟶ (A ⊗ A).left) (N : LB (A ⊗ A).left), IsAbelianScheme A ∧ IsGrpPullback Q.B A (spMap π) i ∧ IsSquare i l ∧ N.IsLB ∧ GlobalTheory.AbDual.IsAdditive N ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap N) ∧ LBIso (N.pull l) (abelian₂ Q.B Q.M.L) :=
  exists_lift_of_step GlobalTheory.T.exists_abelian_lift_ample_bundle

end GlobalTheory.MumLift
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PolLiftComplete

theorem exists_lift : ∀ (K : Type) [Field K] [IsAlgClosed K] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (π : V →+* K), Function.Surjective π → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) → ∃ (AV : Over (Sp V)) (_ : GrpObj AV) (_ : IsCommMonObj AV) (φ : A.left ⟶ AV.left) (φ₂ : (G2 A).left ⟶ (G2 AV).left) (PV : LB (G2 AV).left), IsAbelianScheme AV ∧ IsGrpPullback A AV (spMap π) φ ∧ IsSquare φ φ₂ ∧ PV.IsLB ∧ (∃ t : (PV.pull (lift (1 : AV ⟶ AV) (𝟙 AV)).left).Gen, t.IsGen) ∧ (∃ t : (PV.pull (lift (𝟙 AV) (1 : AV ⟶ AV)).left).Gen, t.IsGen) ∧ LBIso PV (PV.pull (lift (snd AV AV) (fst AV AV)).left) ∧ Out.RelAmple AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) ∧ (∀ (T : Over (Sp V)) (x : T ⟶ AV), (∃ t : (PV.pull (lift (snd AV T ≫ x) (fst AV T)).left).Gen, t.IsGen) → x = 1) ∧ LBIso P (PV.pull φ₂) := by
  intro K _ _ R₁ _ _ _ _ hc π hπ A _ _ hA P hP r₁ r₂ hs ha hker
  obtain ⟨L, hL, hΛ, haL⟩ := GlobalTheory.PolBundleLoc.exists_ample_root A hA hP r₁ r₂ hs ha
  have hKL : KTriv A L := GlobalTheory.KTrivOfLam.kTriv_of_lam_iso (Sp K) A hA P hP hker L hL hΛ
  set I := RingHom.ker π with hI
  have hItop : I ≠ ⊤ := by
    intro h
    have h1 : (1 : R₁) ∈ I := h ▸ Submodule.mem_top
    rw [hI, RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hIc : IsAdicComplete I R₁ := GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' R₁ I (maximalIdeal R₁) (le_maximalIdeal hItop) hc
  have hne : ∀ e : ℕ, I ^ (e + 1) ≠ ⊤ := fun e h =>
    hItop (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  haveI hnt : ∀ e : ℕ, Nontrivial (R₁ ⧸ I ^ (e + 1)) := fun e => Ideal.Quotient.nontrivial_iff.2 (hne e)
  haveI hloc : ∀ e : ℕ, IsLocalRing (R₁ ⧸ I ^ (e + 1)) := fun e =>
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let St : ℕ → Type 1 := fun e => Σ Y : Over (Sp (R₁ ⧸ I ^ (e + 1))), Σ _ : GrpObj Y,
    {L : LB Y.left // IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L}
  have hstep : ∀ (e : ℕ) (y : St e), ∃ (y' : St (e + 1)) (i : y.1.left ⟶ y'.1.left),
      @IsGrpPullback _ _ y.1 y.2.1 y'.1 y'.2.1 (thickTrans R₁ I e) i ∧ LBIso y.2.2.1 (y'.2.2.1.pull i) := by
    rintro e ⟨Y, g, L, hA, hL, ha, hK⟩
    obtain ⟨Y', g', L', i, hA', hL', ha', hK', hi, hLi⟩ := GlobalTheory.SqStep.exists_lift (R₁ ⧸ I ^ (e + 1 + 1))
      (R₁ ⧸ I ^ (e + 1))
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))))
      (Ideal.Quotient.factor_surjective _) (GlobalTheory.MumLift.ker_factor_sq I e) Y hA L hL ha hK
    exact ⟨⟨Y', g', L', hA', hL', ha', hK'⟩, i, hi, hLi⟩
  choose nx β hβ hLβ using hstep
  let e₀ : R₁ ⧸ I ^ (0 + 1) ≃+* K :=
    (Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).trans (RingHom.quotientKerEquivOfSurjective hπ)
  let s : Sp (R₁ ⧸ I ^ (0 + 1)) ⟶ Sp K := spMap (e₀.symm : K →+* R₁ ⧸ I ^ (0 + 1))
  let t : Sp K ⟶ Sp (R₁ ⧸ I ^ (0 + 1)) := spMap (e₀ : R₁ ⧸ I ^ (0 + 1) →+* K)
  have hts : t ≫ s = 𝟙 _ := by
    simp only [t, s, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [RingEquiv.comp_symm]
    simp
  have htπ : t ≫ thick R₁ I 0 = spMap π := by
    simp only [t, thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let Y₀ : Over (Sp (R₁ ⧸ I ^ (0 + 1))) := (Over.pullback s).obj A
  let g₀ : Y₀.left ⟶ A.left := pullback.fst A.hom s
  have G₀ : IsGrpPullback Y₀ A s g₀ := isGrpPullback_pullback A s
  have hL₀ : (L.pull g₀).IsLB := pull_isLB hL g₀
  have hA₀ : IsAbelianScheme Y₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA G₀
  haveI := hA.proper
  have ha₀ : RelAmple Y₀ (L.pull g₀) := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL haL G₀.1
  have hK₀ : KTriv Y₀ (L.pull g₀) := by
    obtain ⟨w, hw⟩ : LBIso (L.pull g₀) (L.pull g₀) := (GlobalTheory.CechPic.cls_eq_iff hL₀ hL₀).1 rfl
    exact kTriv_pull G₀ hL hL₀ ((isGen_iff w).1 hw) hKL
  let y₀ : St 0 := ⟨Y₀, inferInstance, L.pull g₀, hA₀, hL₀, ha₀, hK₀⟩
  let Y : ∀ n : ℕ, St n := fun n => Nat.rec (motive := fun n => St n) y₀ (fun n y => nx n y) n
  letI : ∀ e, GrpObj (Y e).1 := fun e => (Y e).2.1
  obtain ⟨B, _, M, b, hB, hM, haM, hb, -, hiso⟩ := GlobalTheory.AlgGroup.exists_abelianScheme_of_tower R₁ I hItop hIc hc
    (fun e => (Y e).1) (fun e => β e (Y e)) (fun e => (Y e).2.2.2.1) (fun e => hβ e (Y e))
    (fun e => (Y e).2.2.1) (fun e => (Y e).2.2.2.2.1) (fun e => hLβ e (Y e)) (Y 0).2.2.2.2.2.1
  haveI : IsCommMonObj B := hB.comm
  let φ : A.left ⟶ Y₀.left := pullback.lift (𝟙 _) (A.hom ≫ t)
    (by rw [Category.id_comp, Category.assoc, hts, Category.comp_id])
  have hφ₁ : φ ≫ g₀ = 𝟙 _ := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ Y₀.hom = A.hom ≫ t := pullback.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  have n₀ : IsGrpPullback A A (t ≫ s) (φ ≫ g₀) :=
    (isGrpPullback_of_iso (Iso.refl A)).congr hts.symm hφ₁.symm
  have hcan : IsGrpPullback A Y₀ t φ := IsGrpPullback.cancel G₀ n₀ hφ₂
  have hi : IsGrpPullback A B (spMap π) (φ ≫ b 0) := (hcan.comp (hb 0)).congr htπ rfl
  have hLi : LBIso L (M.pull (φ ≫ b 0)) := by
    refine (GlobalTheory.CechPic.cls_eq_iff hL (pull_isLB hM _)).1 ?_
    have a₂ : GlobalTheory.CechPic.cls _ hL₀ = GlobalTheory.CechPic.cls _ (pull_isLB hM (b 0)) :=
      (GlobalTheory.CechPic.cls_eq_iff _ _).2 (hiso 0)
    rw [GlobalTheory.CechPic.cls_pull hM, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hM (b 0) (pull_isLB hM (b 0)), ← a₂,
      GlobalTheory.CechPic.cls_pull hL, ← GlobalTheory.CechPic.pull_comp, hφ₁, GlobalTheory.CechPic.pull_id]
  have hJ : I ^ (0 + 1) ≤ Ideal.jacobson ⊥ :=
    (Ideal.pow_le_self (Nat.succ_ne_zero 0)).trans (IsAdicComplete.le_jacobson_bot I)
  have hK : KTriv B M :=
    GlobalTheory.KTrivJacobson.kTriv_of_quotient R₁ (I ^ (0 + 1)) hJ B hB M hM haM Y₀ (b 0) (hb 0) _ hL₀ (hiso 0) hK₀
  have hPf := GlobalTheory.AbDual.isPerfect_lam hM hK
  have hr : Out.Rigidified B M := GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R₁) (pull_isLB hM _)
  have hΘ := GlobalTheory.HodgeWeil.triv_theta GlobalTheory.CubeTop.cubeTheorem hB hM
  have w : (φ ≫ b 0) ≫ B.hom = A.hom ≫ spMap π := hi.1.w
  have sq := GlobalTheory.LamPull.exists_isSquare w
  have hlamA : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hlamB : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
  refine ⟨B, inferInstance, hB.comm, φ ≫ b 0, _, abelian₂ B M, hB, hi, sq, hPf.isLB, hPf.zero_left, hPf.zero_right,
    GlobalTheory.FullSiegel.lam_symm hM, GlobalTheory.EighthPowerLocal.relAmple_diag_lam hB hM hΘ haM,
    fun T x h => GlobalTheory.FullSiegel.eq_one_of_lam_triv hM hr hK T x h, ?_⟩
  exact LBIso.trans hP hlamA (pull_isLB hlamB _) (LBIso.symm hΛ)
    (GlobalTheory.LamPull.lbIso_lam_pull hi hM hL hLi sq)

end GlobalTheory.PolLiftComplete
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_principal_symmetric_bundle_complete : ∀ (K : Type) [Field K] [IsAlgClosed K] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (π : V →+* K), Function.Surjective π → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) → ∃ (AV : Over (Sp V)) (_ : GrpObj AV) (_ : IsCommMonObj AV) (φ : A.left ⟶ AV.left) (φ₂ : (G2 A).left ⟶ (G2 AV).left) (PV : LB (G2 AV).left), IsAbelianScheme AV ∧ IsGrpPullback A AV (spMap π) φ ∧ IsSquare φ φ₂ ∧ PV.IsLB ∧ (∃ t : (PV.pull (lift (1 : AV ⟶ AV) (𝟙 AV)).left).Gen, t.IsGen) ∧ (∃ t : (PV.pull (lift (𝟙 AV) (1 : AV ⟶ AV)).left).Gen, t.IsGen) ∧ LBIso PV (PV.pull (lift (snd AV AV) (fst AV AV)).left) ∧ Out.RelAmple AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) ∧ (∀ (T : Over (Sp V)) (x : T ⟶ AV), (∃ t : (PV.pull (lift (snd AV T ≫ x) (fst AV T)).left).Gen, t.IsGen) → x = 1) ∧ LBIso P (PV.pull φ₂) := by
  first | exact @GlobalTheory.PolLiftComplete.exists_lift | exact GlobalTheory.PolLiftComplete.exists_lift | (intros; apply GlobalTheory.PolLiftComplete.exists_lift; all_goals assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsLiftComplete

theorem existsUnique_torsion_lift : ∀ (V K : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [Field K] (n : ℕ), IsAdicComplete (IsLocalRing.maximalIdeal V) V → IsUnit (n : V) → ∀ π : V →+* K, Function.Surjective π → ∀ (A₀ : Over (Sp K)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (i : A₀.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A₀ A (spMap π) i → ∀ s₀ : 𝟙_ (Over (Sp K)) ⟶ A₀, s₀ ^ n = 1 → ∃! s : 𝟙_ (Over (Sp V)) ⟶ A, s ^ n = 1 ∧ s₀.left ≫ i = spMap π ≫ s.left := by
  intro V K _ _ _ _ n hc hn π hπ A₀ _ _ A _ _ i hA hpb s₀ hs₀
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := hc
  haveI : HenselianLocalRing V := GlobalTheory.henselianLocalRing_of_henselianRing V
  haveI : Smooth A.hom := hA.smooth
  have hn' : IsUnit (n : Γ(Sp V, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  haveI := GlobalTheory.GrpTangent.etale_id_pow A hn'
  let T' : Over (Sp K) := 𝟙_ (Over (Sp K))
  let T : Over (Sp V) := Over.mk (T'.hom ≫ spMap π)
  have hwi : i ≫ A.hom = A₀.hom ≫ spMap π := hpb.1.w
  have hpt : ∀ x : T' ⟶ A₀, (x.left ≫ i) ≫ A.hom = T.hom := by
    intro x
    rw [Category.assoc, hwi, ← Category.assoc, Over.w x]
    rfl
  let pt : (T' ⟶ A₀) → (T ⟶ A) := fun x => Over.homMk (x.left ≫ i) (hpt x)
  have hone : pt 1 = 1 := by
    have h := hpb.2 T' 1 1 (pt 1) (pt 1) rfl rfl
    rw [_root_.mul_one] at h
    have h2 : pt 1 * pt 1 = pt 1 := Over.OverMorphism.ext h
    exact mul_eq_left.mp h2
  have hpow : ∀ m : ℕ, (pt s₀) ^ m = pt (s₀ ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact Over.OverMorphism.ext (hpb.2 T' (s₀ ^ m) s₀ ((pt s₀) ^ m) (pt s₀) (by rw [ih]; rfl) rfl)
  have hx : (pt s₀) ^ n = 1 := by rw [hpow, hs₀, hone]
  let f : A.left ⟶ A.left := (𝟙 A ^ n).left
  have hf : ∀ {Y : Over (Sp V)} (y : Y ⟶ A), y.left ≫ f = (y ^ n).left := by
    intro Y y
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hone' : ∀ {Y : Over (Sp V)} , ((1 : Y ⟶ A)).left = Y.hom ≫ (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left := by
    intro Y
    rw [Hom.one_def, Over.comp_left]
    congr 1
  have hw : (s₀.left ≫ i) ≫ f = Spec.map (CommRingCat.ofHom π) ≫ (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left := by
    have := hf (pt s₀)
    rw [hx, hone'] at this
    simpa [pt, T, T'] using this
  obtain ⟨l, ⟨hl1, hl2⟩, huniq⟩ :=
    GlobalTheory.existsUnique_lift_of_etale_of_henselian f π hπ (s₀.left ≫ i) _ hw
  have hls : l ≫ A.hom = (𝟙_ (Over (Sp V))).hom := by
    have e : f ≫ A.hom = A.hom := Over.w (𝟙 A ^ n)
    rw [← e, ← Category.assoc, hl2]
    exact Over.w (η[A] : 𝟙_ (Over (Sp V)) ⟶ A)
  let s : 𝟙_ (Over (Sp V)) ⟶ A := Over.homMk l hls
  have hsn : ∀ s' : 𝟙_ (Over (Sp V)) ⟶ A, s' ^ n = 1 ↔ s'.left ≫ f = (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left := by
    intro s'
    have e1 : ((1 : 𝟙_ (Over (Sp V)) ⟶ A)).left = (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left := by
      rw [hone']; exact Category.id_comp _
    rw [hf]
    constructor
    · intro h; rw [h, e1]
    · intro h
      apply Over.OverMorphism.ext
      rw [h, e1]
  refine ⟨s, ⟨(hsn s).2 hl2, hl1.symm⟩, ?_⟩
  rintro s' ⟨h1, h2⟩
  exact Over.OverMorphism.ext (huniq s'.left ⟨h2.symm, (hsn s').1 h1⟩)

end GlobalTheory.TorsLiftComplete
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LevLift

theorem exists_eq_val_add {J : Type} {n : ℕ} [NeZero n] (a : J → ℤ) :
    ∃ b : J → ℤ, a = (fun i => (((a i : ZMod n)).val : ℤ)) + n • b :=
  ⟨fun i => a i / n, funext fun i => by
    rw [Pi.add_apply, Pi.smul_apply, ZMod.val_intCast, nsmul_eq_mul]
    exact (Int.emod_add_mul_ediv (a i) n).symm⟩

section Count

variable {G : Type} [CommGroup G] {J : Type} [Fintype J] [DecidableEq J] {n : ℕ} [NeZero n] (f : (J → ℤ) → G)
  (hadd : ∀ a b, f (a + b) = f a * f b) (hker : ∀ a, f a = 1 ↔ ∃ b, a = n • b)
include hadd hker

theorem eq_val (a : J → ℤ) : f a = f (fun i => (((a i : ZMod n)).val : ℤ)) := by
  obtain ⟨b, hb⟩ := exists_eq_val_add (n := n) a
  conv_lhs => rw [hb]
  rw [hadd, (hker (n • b)).2 ⟨b, rfl⟩, _root_.mul_one]

theorem inj : Function.Injective (fun c : J → ZMod n => f (fun i => ((c i).val : ℤ))) := by
  intro c c' h
  simp only at h
  have h1 : f ((fun i => ((c i).val : ℤ)) - (fun i => ((c' i).val : ℤ))) = 1 := by
    have e := hadd ((fun i => ((c i).val : ℤ)) - (fun i => ((c' i).val : ℤ))) (fun i => ((c' i).val : ℤ))
    rw [sub_add_cancel, h] at e
    exact mul_eq_right.1 e.symm
  obtain ⟨b, hb⟩ := (hker _).1 h1
  funext i
  have e := congrFun hb i
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at e
  have e2 := congrArg (fun z : ℤ => (z : ZMod n)) e
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_self, zero_mul] at e2
  exact sub_eq_zero.1 e2

theorem card_eq (htors : ∀ a, f a ^ n = 1) (hsurj : ∀ x : G, x ^ n = 1 → ∃ a, f a = x) :
    Nat.card {x : G // x ^ n = 1} = n ^ Fintype.card J := by
  let F : (J → ZMod n) → {x : G // x ^ n = 1} := fun c => ⟨f (fun i => ((c i).val : ℤ)), htors _⟩
  have hF : Function.Bijective F := ⟨fun c c' e => inj f hadd hker (congrArg Subtype.val e), fun x => by
    obtain ⟨a, ha⟩ := hsurj x.1 x.2
    exact ⟨fun i => (a i : ZMod n), Subtype.ext (by rw [← ha, eq_val f hadd hker a])⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

theorem surj (htors : ∀ a, f a ^ n = 1) (hcard : Nat.card {x : G // x ^ n = 1} = n ^ Fintype.card J) :
    ∀ x : G, x ^ n = 1 → ∃ a, f a = x := by
  intro x hx
  let F : (J → ZMod n) → {x : G // x ^ n = 1} := fun c => ⟨f (fun i => ((c i).val : ℤ)), htors _⟩
  have hFi : Function.Injective F := fun c c' e => inj f hadd hker (congrArg Subtype.val e)
  have hne : Nat.card {x : G // x ^ n = 1} ≠ 0 := by
    rw [hcard]; exact pow_ne_zero _ (NeZero.ne n)
  haveI : Finite {x : G // x ^ n = 1} := Nat.finite_of_card_ne_zero hne
  have hle : Nat.card {x : G // x ^ n = 1} ≤ Nat.card (J → ZMod n) := by
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  obtain ⟨c, hc⟩ := (hFi.bijective_of_nat_card_le hle).2 ⟨x, hx⟩
  exact ⟨_, congrArg Subtype.val hc⟩

end Count

end GlobalTheory.LevLift

namespace GlobalTheory.LevLift

theorem exists_level_lift : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (βV : cycAway n →+* V) (π : V →+* K), Function.Surjective π → ∀ (c : SiegPre g n (zetaAway n) (spMap (π.comp βV))), c.Principal → ∀ (AV : Over (Sp V)) [GrpObj AV] [IsCommMonObj AV] (φ : c.A.left ⟶ AV.left) (φ₂ : (G2 c.A).left ⟶ (G2 AV).left) (PV : LB (G2 AV).left), IsAbelianScheme AV → IsGrpPullback c.A AV (spMap π) φ → IsSquare φ φ₂ → PV.IsLB → (∃ t : (PV.pull (lift (1 : AV ⟶ AV) (𝟙 AV)).left).Gen, t.IsGen) → (∃ t : (PV.pull (lift (𝟙 AV) (1 : AV ⟶ AV)).left).Gen, t.IsGen) → LBIso PV (PV.pull (lift (snd AV AV) (fst AV AV)).left) → Out.RelAmple AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) → (∀ (T : Over (Sp V)) (x : T ⟶ AV), (∃ t : (PV.pull (lift (snd AV T ≫ x) (fst AV T)).left).Gen, t.IsGen) → x = 1) → LBIso c.P (PV.pull φ₂) → ∃ lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp V)) ⟶ AV), (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ n = 1) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp V) (β : cycAway n →+* k) (z : kˣ), x ≫ spMap βV = spMap β → (z : k) = β (zetaAway n) → (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b)) ∧ (∀ g' : Over.mk x ⟶ AV, g' ^ n = 1 → ∃ a, toUnit _ ≫ lev a = g') ∧ ∀ a b, Out.WeilIs AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) n (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b)))) ∧ ∀ a, (c.lev a).left ≫ φ = spMap π ≫ (lev a).left := by
  intro g n hn3 hnodd K _ _ V _ _ _ _ hcV βV π hπ c hcP AV _ _ φ φ₂ PV hAV hφ hsq hPV hr₁ hr₂ hsym hamp hkerV hiso
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn0⟩
  have hnR : IsUnit (n : V) := by simpa using (isUnit_natCast hn0).map βV
  have hnΓ : IsUnit (n : Γ(Sp V, ⊤)) := by
    have := hnR.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
    rwa [map_natCast] at this
  have hP : GlobalTheory.TChart.IsPPol AV PV := ⟨⟨hPV, hr₁, hr₂, hsym⟩, hamp, hkerV⟩

  have hζc : IsPrimitiveRoot (zetaAway n) n :=
    IsPrimitiveRoot.of_map_of_injective (f := (cycAway n).subtype) (Complex.isPrimitiveRoot_exp n hn0) Subtype.val_injective
  let ζU : (cycAway n)ˣ := (hζc.isUnit hn0).unit
  let ζR : Vˣ := Units.map βV.toMonoidHom ζU
  have hζR : IsPrimitiveRoot ζR n := IsPrimitiveRoot.coe_units_iff.1 (GlobalTheory.LevSpread.prim_map hn0 βV)

  have hdiag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((PV.pull (lift (𝟙 AV) (𝟙 AV)).left).pull φ) := by
    have ext2 : ∀ {X : Scheme.{0}} (u v : X ⟶ (G2 AV).left), u ≫ (fst AV AV).left = v ≫ (fst AV AV).left →
        u ≫ (snd AV AV).left = v ≫ (snd AV AV).left → u = v := fun u v h1 h2 => Over.tensorObj_ext _ _ h1 h2
    have d1 : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ (fst c.A c.A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
    have d2 : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ (snd c.A c.A).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
    have d1' : (lift (𝟙 AV) (𝟙 AV)).left ≫ (fst AV AV).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
    have d2' : (lift (𝟙 AV) (𝟙 AV)).left ≫ (snd AV AV).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
    have hd : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 AV) (𝟙 AV)).left := by
      apply ext2
      · rw [Category.assoc, hsq.1, ← Category.assoc, d1, Category.id_comp, Category.assoc, d1', Category.comp_id]
      · rw [Category.assoc, hsq.2, ← Category.assoc, d2, Category.id_comp, Category.assoc, d2', Category.comp_id]
    have h3 := GlobalTheory.ThetaAffineGlue.lbIso_pull hiso (lift (𝟙 c.A) (𝟙 c.A)).left
    rw [hd] at h3
    have hΔ := pull_isLB hPV (lift (𝟙 AV) (𝟙 AV)).left
    exact h3.trans (pull_isLB c.isLB _) (pull_isLB hPV _) (pull_isLB hΔ _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull
        (show LBIso (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) from
          LBIso.trans hΔ (pull_isLB hΔ _) hΔ (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ)
            (LBIso.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ))) φ).symm

  have hL := fun a => GlobalTheory.TorsLiftComplete.existsUnique_torsion_lift V K n hcV hnR π hπ c.A AV φ hAV hφ (c.lev a)
    (c.lev_tors a)
  choose σ hσ using fun a => (hL a).exists
  have hσn : ∀ a, σ a ^ n = 1 := fun a => (hσ a).1
  have hcomp : ∀ a, (c.lev a).left ≫ φ = spMap π ≫ (σ a).left := fun a => (hσ a).2
  let E := GlobalTheory.ObjPull.pushEquiv hφ (𝟙_ (Over (Sp K)))
  let T₁ : Over (Sp V) := Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap π)
  have hσx : ∀ a, toUnit T₁ ≫ σ a = E (c.lev a) := fun a => by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GlobalTheory.ObjPull.toUnit_left', GlobalTheory.ObjPull.pushEquiv_left, hcomp]
    exact congrArg (· ≫ (σ a).left) (Category.id_comp _)
  haveI : PreconnectedSpace (𝟙_ (Over (Sp V))).left := inferInstanceAs (PreconnectedSpace (Sp V))
  have inj : ∀ (T : Over (Sp V)) [Nonempty T.left] (s s' : 𝟙_ (Over (Sp V)) ⟶ AV), s ^ n = 1 → s' ^ n = 1 →
      toUnit T ≫ s = toUnit T ≫ s' → s = s' := fun T _ s s' hs hs' h =>
    GlobalTheory.LevSpread.eq_of_comp_eq AV hAV hnΓ (𝟙_ _) s s' hs hs' T (toUnit T) h
  haveI : Nonempty T₁.left := inferInstanceAs (Nonempty (Sp K))
  have hadd : ∀ a a', σ (a + a') = σ a * σ a' := fun a a' =>
    inj T₁ _ _ (hσn _) (by rw [mul_pow, hσn, hσn, _root_.mul_one])
      (by rw [MonObj.comp_mul, hσx, hσx, hσx, c.lev_add, map_mul])
  have one_iff : ∀ (T : Over (Sp V)) [Nonempty T.left] a, toUnit T ≫ σ a = 1 ↔ σ a = 1 := fun T _ a =>
    ⟨fun h => inj T (σ a) 1 (hσn a) (one_pow n) (h.trans (MonObj.comp_one _).symm),
      fun h => by rw [h, MonObj.comp_one]⟩

  let iK : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let x₀ : Sp (AlgebraicClosure K) ⟶ Sp K := spMap iK
  obtain ⟨g1, g2, g3⟩ := c.geom (AlgebraicClosure K) x₀ ((iK.comp π).comp βV)
    (Units.map ((iK.comp π).comp βV).toMonoidHom ζU) (by rw [← Spec.map_comp]; rfl) rfl
  let T₀ : Over (Sp V) := Over.mk ((Over.mk x₀).hom ≫ spMap π)
  haveI : Nonempty T₀.left := inferInstanceAs (Nonempty (Sp (AlgebraicClosure K)))
  have push : ∀ a, GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀) (toUnit _ ≫ c.lev a) = toUnit T₀ ≫ σ a := fun a => by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, hcomp,
      GlobalTheory.ObjPull.toUnit_left', GlobalTheory.ObjPull.toUnit_left']
    exact (Category.assoc _ _ _).symm
  have hker : ∀ a, σ a = 1 ↔ ∃ b, a = n • b := fun a => by
    rw [← one_iff T₀, ← push, map_eq_one_iff _ (GlobalTheory.ObjPull.pushEquiv hφ _).injective]
    exact g1 a

  haveI : ConnectedSpace (Sp V) := GlobalTheory.AbelianDim.connectedSpace_spec_of_isLocalRing V
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim_of_connected AV hAV
  have kerAt : ∀ (T : Over (Sp V)) [Nonempty T.left] a, toUnit T ≫ σ a = 1 ↔ ∃ b, a = n • b := fun T _ a => by
    rw [one_iff T]; exact hker a
  have addAt : ∀ (T : Over (Sp V)) a a', toUnit T ≫ σ (a + a') = (toUnit T ≫ σ a) * (toUnit T ≫ σ a') :=
    fun T a a' => by rw [hadd, MonObj.comp_mul]
  have torsAt : ∀ (T : Over (Sp V)) a, (toUnit T ≫ σ a) ^ n = 1 := fun T a => by
    rw [← MonObj.comp_pow, hσn, MonObj.comp_one]
  have surj₀ : ∀ gg : T₀ ⟶ AV, gg ^ n = 1 → ∃ a, toUnit T₀ ≫ σ a = gg := fun gg hg => by
    obtain ⟨a, ha⟩ := g2 ((GlobalTheory.ObjPull.pushEquiv hφ (Over.mk x₀)).symm gg)
      (by rw [← map_pow, hg, map_one])
    exact ⟨a, by rw [← push, ha, MulEquiv.apply_symm_apply]⟩
  have card₀ := card_eq (fun a => toUnit T₀ ≫ σ a) (addAt T₀) (kerAt T₀) (torsAt T₀) surj₀
  have cardd := GlobalTheory.TorsionCover.card_torsion AV hAV hd ((Over.mk x₀).hom ≫ spMap π)
    (GlobalTheory.TorsionCover.natCast_ne_zero hnΓ ((Over.mk x₀).hom ≫ spMap π))
  have hdg : d = g := by
    have e : n ^ (2 * d) = n ^ (2 * g) := by
      rw [← cardd, show 2 * g = Fintype.card (Fin g ⊕ Fin g) by simp [two_mul]]
      exact card₀
    have := Nat.pow_right_injective (show 2 ≤ n by omega) e
    omega
  subst hdg
  refine ⟨σ, hadd, hσn, fun k _ _ x β z hxβ hz => ?_, hcomp⟩
  obtain ⟨ρ, rfl⟩ : ∃ ρ : V →+* k, spMap ρ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hβ : β = ρ.comp βV := by
    have e : spMap (ρ.comp βV) = spMap β := by rw [← hxβ]; exact Spec.map_comp _ _
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective e)).symm
  have hzU : z = Units.map ρ.toMonoidHom ζR := Units.ext (by rw [hz, hβ]; rfl)
  subst hzU
  haveI : Nonempty (Over.mk (spMap ρ)).left := inferInstanceAs (Nonempty (Sp k))
  refine ⟨fun a => kerAt _ a, fun gg hg => ?_, fun a a' => ?_⟩
  · have cardk := GlobalTheory.TorsionCover.card_torsion AV hAV hd (spMap ρ) (GlobalTheory.TorsionCover.natCast_ne_zero hnΓ (spMap ρ))
    exact surj (fun a => toUnit (Over.mk (spMap ρ)) ≫ σ a) (addAt _) (kerAt _) (torsAt _)
      (by rw [cardk]; simp [two_mul]) gg hg
  · have H' := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm (Sp V) (Sp K) AV c.A (spMap π) φ
      (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) (pull_isLB hPV _)
      (pull_isLB c.isLB _) hφ hdiag (Over.mk x₀) (n : ℤ) _ _ (toUnit T₀ ≫ σ a) (toUnit T₀ ≫ σ a') _
      (by rw [← push]; rfl) (by rw [← push]; rfl)).1 (g3 a a')
    have ht : (Over.mk x₀).hom ≫ spMap π = spMap (iK.comp π) := by
      show x₀ ≫ spMap π = _
      rw [← Spec.map_comp]; rfl
    have hu : (Units.map ((iK.comp π).comp βV).toMonoidHom ζU) ^ (2 * omegaStd a a') =
        Units.map (iK.comp π).toMonoidHom (ζR ^ (2 * omegaStd a a')) := by
      rw [map_zpow]; rfl
    rw [hu] at H'
    simp only [T₀] at H'
    rw [ht] at H'
    have H'' := GlobalTheory.LevSpread.l3 V AV hAV PV hP n (by omega) hnR (σ a) (σ a') (hσn a) (hσn a') ζR hζR
      (2 * omegaStd a a') (AlgebraicClosure K) (iK.comp π) H' k ρ
    rw [← map_zpow]
    exact H''

end GlobalTheory.LevLift
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_symplecticLevel_lift_closedPoint : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (βV : cycAway n →+* V) (π : V →+* K), Function.Surjective π → ∀ (c : SiegPre g n (zetaAway n) (spMap (π.comp βV))), c.Principal → ∀ (AV : Over (Sp V)) [GrpObj AV] [IsCommMonObj AV] (φ : c.A.left ⟶ AV.left) (φ₂ : (G2 c.A).left ⟶ (G2 AV).left) (PV : LB (G2 AV).left), IsAbelianScheme AV → IsGrpPullback c.A AV (spMap π) φ → IsSquare φ φ₂ → PV.IsLB → (∃ t : (PV.pull (lift (1 : AV ⟶ AV) (𝟙 AV)).left).Gen, t.IsGen) → (∃ t : (PV.pull (lift (𝟙 AV) (1 : AV ⟶ AV)).left).Gen, t.IsGen) → LBIso PV (PV.pull (lift (snd AV AV) (fst AV AV)).left) → Out.RelAmple AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) → (∀ (T : Over (Sp V)) (x : T ⟶ AV), (∃ t : (PV.pull (lift (snd AV T ≫ x) (fst AV T)).left).Gen, t.IsGen) → x = 1) → LBIso c.P (PV.pull φ₂) → ∃ lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp V)) ⟶ AV), (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ n = 1) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp V) (β : cycAway n →+* k) (z : kˣ), x ≫ spMap βV = spMap β → (z : k) = β (zetaAway n) → (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b)) ∧ (∀ g' : Over.mk x ⟶ AV, g' ^ n = 1 → ∃ a, toUnit _ ≫ lev a = g') ∧ ∀ a b, Out.WeilIs AV (PV.pull (lift (𝟙 AV) (𝟙 AV)).left) n (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b)))) ∧ ∀ a, (c.lev a).left ≫ φ = spMap π ≫ (lev a).left := by
  first | (exact @GlobalTheory.LevLift.exists_level_lift) | (exact GlobalTheory.LevLift.exists_level_lift) | (intros; apply GlobalTheory.LevLift.exists_level_lift  <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLift0

theorem exists_lift_domain : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K]
    (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal →
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (βV : cycAway n →+* V) (π : V →+* K)
      (cV : SiegPre g n (zetaAway n) (spMap βV)),
      Function.Injective βV ∧ π.comp βV = β ∧ cV.Principal ∧ SiegPB c cV (spMap π) := by
  intro g n hg hn hodd K _ _ β c hc
  obtain ⟨V, _, _, _, _, βV, π, hV, hinj, hπ, hβ⟩ := GlobalTheory.T.exists_completeLocalDomain_lift_cyclotomicAway n hn K β
  subst hβ
  obtain ⟨AV, _, _, φ, φ₂, PV, hAV, hpb, hsq, hPV, r₁, r₂, hsy, ham, hker, hiso⟩ :=
    GlobalTheory.T.exists_lift_principal_symmetric_bundle_complete K V hV π hπ c.A c.ab c.P c.isLB c.rig₁ c.rig₂ c.symm hc.1 hc.2
  obtain ⟨lev, hadd, htor, hgeom, hcomp⟩ :=
    GlobalTheory.T.exists_unique_symplecticLevel_lift_closedPoint g n hn hodd K V hV βV π hπ c hc AV φ φ₂ PV hAV hpb hsq hPV r₁ r₂ hsy ham hker hiso
  let cV : SiegPre g n (zetaAway n) (spMap βV) :=
    { A := AV, ab := hAV, P := PV, isLB := hPV, rig₁ := r₁, rig₂ := r₂, symm := hsy, lev := lev,
      lev_add := hadd, lev_tors := htor, geom := hgeom }
  exact ⟨V, inferInstance, inferInstance, βV, π, cV, hinj, rfl, ⟨ham, hker⟩, φ, φ₂, hpb, hsq, hiso, hcomp⟩

end GlobalTheory.SiegLift0
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_siegel_object_exists_charZero_lift : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (βV : cycAway n →+* V) (π : V →+* K) (cV : SiegPre g n (zetaAway n) (spMap βV)), Function.Injective βV ∧ π.comp βV = β ∧ cV.Principal ∧ SiegPB c cV (spMap π) := by
  atlas_forward_decl GlobalTheory.SiegLift0.exists_lift_domain
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelFieldClass

theorem dense_generic {A V : Type} [CommRing A] [CommRing V] [IsDomain V] (β : A →+* V)
    (hβ : Function.Injective β) : Dense {x : Sp V | (spMap β x).asIdeal = ⊥} := by
  let ξ : Sp V := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)
  have hξ : ξ ∈ {x : Sp V | (spMap β x).asIdeal = ⊥} := by
    show (PrimeSpectrum.comap (CommRingCat.ofHom β).hom ⟨⊥, Ideal.isPrime_bot⟩).asIdeal = ⊥
    simp only [PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom]
    exact (RingHom.injective_iff_ker_eq_bot β).1 hβ
  have hd : Dense ({ξ} : Set (Sp V)) := by
    rw [dense_iff_closure_eq]
    show closure ({(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)} : Set (PrimeSpectrum V)) = Set.univ
    rw [PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  exact hd.mono (Set.singleton_subset_iff.2 hξ)

theorem classifies_algClosed : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp K ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ _ β c hc
  obtain ⟨V, _, _, βV, π, cV, hinj, hcomp, hpr, hpb⟩ := GlobalTheory.T.principal_siegel_object_exists_charZero_lift g n hg hn hodd K β c hc
  obtain ⟨f, hf, hfpb⟩ := F.rep (Sp V) (spMap βV) cV inferInstance (dense_generic βV hinj) hpr
  refine ⟨spMap π ≫ f, ?_, GlobalTheory.SiegelPullComp.pb_comp hfpb hpb⟩
  rw [Category.assoc, hf, ← hcomp]
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.SiegelFieldClass
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_family_classifies_principal_algClosed : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp K ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  atlas_forward_decl GlobalTheory.SiegelFieldClass.classifies_algClosed
end
