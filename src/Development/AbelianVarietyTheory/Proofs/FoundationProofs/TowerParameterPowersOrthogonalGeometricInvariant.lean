import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowDivPrimeZpowIntegralClosureUnit
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

section
section
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.GeoFix

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem exists_finset_of_mem_closure (R A : Set Ω) {x : Ω} (hx : x ∈ Subfield.closure (R ∪ A)) :
    ∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ x ∈ Subfield.closure (R ∪ (S : Set Ω)) := by
  classical
  have mono : ∀ {S S' : Finset Ω}, S ⊆ S' →
      Subfield.closure (R ∪ (S : Set Ω)) ≤ Subfield.closure (R ∪ (S' : Set Ω)) := fun h =>
    Subfield.closure_mono (Set.union_subset_union_right _ (Finset.coe_subset.2 h))
  have two : ∀ {y z : Ω}, (∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ y ∈ Subfield.closure (R ∪ (S : Set Ω))) →
      (∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ z ∈ Subfield.closure (R ∪ (S : Set Ω))) →
      ∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ y ∈ Subfield.closure (R ∪ (S : Set Ω)) ∧
        z ∈ Subfield.closure (R ∪ (S : Set Ω)) := by
    rintro y z ⟨S, hS, hy⟩ ⟨S', hS', hz⟩
    refine ⟨S ∪ S', ?_, mono Finset.subset_union_left hy, mono Finset.subset_union_right hz⟩
    rw [Finset.coe_union]; exact Set.union_subset hS hS'
  let F : Subfield Ω :=
    { carrier := {y | ∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ y ∈ Subfield.closure (R ∪ (S : Set Ω))}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨S, hS, h1, h2⟩ := two ha hb
        exact ⟨S, hS, mul_mem h1 h2⟩
      one_mem' := ⟨∅, by simp, one_mem _⟩
      add_mem' := fun {a b} ha hb => by
        obtain ⟨S, hS, h1, h2⟩ := two ha hb
        exact ⟨S, hS, add_mem h1 h2⟩
      zero_mem' := ⟨∅, by simp, zero_mem _⟩
      neg_mem' := fun {a} ⟨S, hS, h1⟩ => ⟨S, hS, neg_mem h1⟩
      inv_mem' := fun a ⟨S, hS, h1⟩ => ⟨S, hS, inv_mem h1⟩ }
  have hle : Subfield.closure (R ∪ A) ≤ F := by
    rw [Subfield.closure_le]
    rintro y (hy | hy)
    · exact ⟨∅, by simp, Subfield.subset_closure (Or.inl hy)⟩
    · refine ⟨{y}, by simpa using hy, Subfield.subset_closure (Or.inr (by simp))⟩
  exact hle hx

variable (p Ω) in

def geoField : Subfield Ω :=
  Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x : Ω | IsAlgZp p x})

theorem mem_geoField_of_fixed (h : IsClo p Ω) (x : Ω) (hx : ∀ g ∈ Ggeo p Ω, g x = x) :
    x ∈ geoField p Ω := by
  haveI := h.clo
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  have hR : ∀ a : O0 p, algebraMap (O0 p) Ω a ∈ geoField p Ω := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  let f : O0 p →+* geoField p Ω := (algebraMap (O0 p) Ω).codRestrict (geoField p Ω) hR
  have hf : (algebraMap (geoField p Ω) Ω).comp f = algebraMap (O0 p) Ω := by ext; rfl
  have hfi : Function.Injective f := fun a b hab => h.inj (congrArg Subtype.val hab)
  haveI : Algebra.IsAlgebraic (geoField p Ω) Ω := ⟨fun a => by
    obtain ⟨P, hP0, hP⟩ := h.alg.isAlgebraic a
    refine ⟨P.map f, (Polynomial.map_ne_zero_iff hfi).2 hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hf, ← Polynomial.aeval_def, hP]⟩
  haveI : IsAlgClosure (geoField p Ω) Ω := ⟨h.clo, inferInstance⟩
  haveI : IsGalois (geoField p Ω) Ω := IsAlgClosure.isGalois _ Ω
  have hbot : x ∈ (⊥ : IntermediateField (geoField p Ω) Ω) := by
    refine (InfiniteGalois.mem_bot_iff_fixed x).2 fun σ => ?_
    let τ : Ω ≃ₐ[O0 p] Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv)
      (fun a => σ.commutes ⟨_, hR a⟩)
    have hτ : τ ∈ Ggeo p Ω := fun y hy => σ.commutes ⟨y, Subfield.subset_closure (Or.inr hy)⟩
    exact hx τ hτ
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hbot
  exact y.2

theorem fixed_mem_closure : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ x : Ω, (∀ g ∈ Ggeo p Ω, g x = x) → ∃ S : Finset Ω, (∀ s ∈ S, IsAlgZp p s) ∧
      x ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) := by
  intro p _ Ω _ _ h x hx
  obtain ⟨S, hS, hxS⟩ := exists_finset_of_mem_closure _ _ (mem_geoField_of_fixed h x hx)
  exact ⟨S, fun s hs => hS hs, hxS⟩

end GlobalTheory.K5.GeoFix
end
end

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_fixed_mem_closure_finite_algZp : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, (∀ g ∈ Ggeo p Ω, g x = x) → ∃ S : Finset Ω, (∀ s ∈ S, IsAlgZp p s) ∧
    x ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) := by
  atlas_forward_decl GlobalTheory.K5.GeoFix.fixed_mem_closure
end

section
section
namespace GlobalTheory

theorem exists_finite_pid_subalgebra_div_padicInt :
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgebraic ℤ_[p] s) →
  ∃ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R ∧ IsPrincipalIdealRing R ∧ ∀ s ∈ S, ∃ a ∈ R, ∃ b ∈ R, s = a / b := by
  intro p _ Ω _ _ hinj S hS
  haveI : FaithfulSMul ℤ_[p] Ω := (faithfulSMul_iff_algebraMap_injective ℤ_[p] Ω).mpr hinj
  letI : Algebra (FractionRing ℤ_[p]) Ω := FractionRing.liftAlgebra ℤ_[p] Ω
  haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) Ω := FractionRing.isScalarTower_liftAlgebra ℤ_[p] Ω
  set L := IntermediateField.adjoin (FractionRing ℤ_[p]) (S : Set Ω) with hL
  haveI : FiniteDimensional (FractionRing ℤ_[p]) L := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    exact ((hS x hx).extendScalars (IsFractionRing.injective ℤ_[p] (FractionRing ℤ_[p]))).isIntegral
  haveI : Algebra.IsSeparable (FractionRing ℤ_[p]) L := inferInstance
  haveI : IsDedekindDomain (integralClosure ℤ_[p] L) :=
    integralClosure.isDedekindDomain ℤ_[p] (FractionRing ℤ_[p]) L
  haveI : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L) :=
    IsIntegralClosure.finite ℤ_[p] (FractionRing ℤ_[p]) L (integralClosure ℤ_[p] L)
  have hPID : IsPrincipalIdealRing (integralClosure ℤ_[p] L) := by
    apply IsPrincipalIdealRing.of_finite_primes
    haveI := GlobalTheory.finite_maximalSpectrum_of_finite_of_isLocalRing ℤ_[p] (integralClosure ℤ_[p] L)
    apply ((Set.finite_range (fun M : MaximalSpectrum (integralClosure ℤ_[p] L) => M.asIdeal)).insert ⊥).subset
    intro I hI
    by_cases h : I = ⊥
    · exact Or.inl h
    · exact Or.inr ⟨⟨I, (show I.IsPrime from hI).isMaximal h⟩, rfl⟩
  let f : L →ₐ[ℤ_[p]] Ω :=
    { algebraMap L Ω with
      commutes' := fun r => by
        change ((algebraMap ℤ_[p] L r : L) : Ω) = _
        rw [IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) L r]
        exact (IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) Ω r).symm }
  have hf : Function.Injective f := Subtype.val_injective
  let e := Subalgebra.equivMapOfInjective (integralClosure ℤ_[p] L) f hf
  refine ⟨(integralClosure ℤ_[p] L).map f, Module.Finite.equiv e.toLinearEquiv,
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective, ?_⟩
  intro s hs
  obtain ⟨c, hc0, hci⟩ := (hS s hs).exists_integral_multiple
  have hsL : s ∈ L := IntermediateField.subset_adjoin _ _ hs
  refine ⟨c • s, ?_, algebraMap ℤ_[p] Ω c, Subalgebra.algebraMap_mem _ c, ?_⟩
  · rw [Subalgebra.mem_map]
    refine ⟨c • ⟨s, hsL⟩, ?_, rfl⟩
    show IsIntegral ℤ_[p] (c • (⟨s, hsL⟩ : L))
    rw [← isIntegral_algHom_iff f hf]
    exact hci
  · rw [Algebra.smul_def, mul_div_cancel_left₀ _ ((map_ne_zero_iff _ hinj).mpr hc0)]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_pid_subalgebra_padicInt_contains_fractions : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgebraic ℤ_[p] s) →
  ∃ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R ∧ IsPrincipalIdealRing R ∧ ∀ s ∈ S, ∃ a ∈ R, ∃ b ∈ R, s = a / b := by
  atlas_forward_decl GlobalTheory.exists_finite_pid_subalgebra_div_padicInt
end

section
section
namespace GlobalTheory

theorem exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt :
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ v : Valuation Ω NNReal, (∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1) → v (p : Ω) < 1 →
  ∀ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R → IsPrincipalIdealRing R →
  ∃ π ∈ R, π ≠ 0 ∧ v π < 1 ∧ (p : Ω) / π ∈ R ∧ ∃ f : ℕ, 0 < f ∧ ∀ t ∈ R, (t ^ p ^ f - t) / π ∈ R := by
  intro p _ Ω _ _ hinj v hint hp R hfin hpid
  have hle : ∀ x : R, v (x : Ω) ≤ 1 := fun x => hint _ ((IsIntegral.of_finite ℤ_[p] x).map R.val)
  obtain ⟨P, hP⟩ : ∃ P : Ideal R, ∀ x, x ∈ P ↔ v (x : Ω) < 1 := by
    refine ⟨{ carrier := {x | v (x : Ω) < 1}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun x => Iff.rfl⟩
    · intro a b ha hb
      simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at *
      exact lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb)
    · simp
    · intro c x hx
      simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, map_mul] at *
      calc v (c:Ω) * v x ≤ 1 * v x := mul_le_mul' (hle c) le_rfl
        _ = v x := one_mul _
        _ < 1 := hx
  have hpR : ((p : R) : Ω) = (p : Ω) := by simp
  have hpP : (p : R) ∈ P := by rw [hP, hpR]; exact hp
  have hp0 : (p : Ω) ≠ 0 := by
    intro h
    have h1 : algebraMap ℤ_[p] Ω (p : ℤ_[p]) = algebraMap ℤ_[p] Ω 0 := by simp [h]
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (hinj h1)
  have hPprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro h
      have h1 : (1 : R) ∈ P := h ▸ Submodule.mem_top
      rw [hP] at h1; simp at h1
    · intro x y hxy
      rw [hP, hP]; rw [hP] at hxy
      simp only [Subalgebra.coe_mul, map_mul] at hxy
      by_contra hc
      push_neg at hc
      have hx1 : v x = 1 := le_antisymm (hle x) hc.1
      have hy1 : v y = 1 := le_antisymm (hle y) hc.2
      rw [hx1, hy1, one_mul] at hxy
      exact lt_irrefl _ hxy
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    apply hp0; rw [← hpR, hpP]; rfl
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hPne
  set g := Submodule.IsPrincipal.generator P with hgdef
  have hgmem : g ∈ P := Submodule.IsPrincipal.generator_mem P
  have hg0 : g ≠ 0 := by
    intro h; apply hPne
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero P).mpr h
  have hdvd : ∀ x : R, x ∈ P → ∃ c : R, x = g * c := fun x hx =>
    (Submodule.IsPrincipal.mem_iff_generator_dvd P).mp hx

  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hpk : ((p : ℕ) : R ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hpP
  have hchar : CharP (R ⧸ P) p := by
    rw [← ringChar.eq_iff]
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp (ringChar.dvd hpk) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  have hunder : P.under ℤ_[p] = IsLocalRing.maximalIdeal ℤ_[p] := by
    apply le_antisymm
    · apply IsLocalRing.le_maximalIdeal
      intro h
      apply hPprime.ne_top
      rw [Ideal.eq_top_iff_one] at h ⊢
      simpa [Ideal.mem_comap] using h
    · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]
      show (p : ℤ_[p]) ∈ P.comap (algebraMap ℤ_[p] R)
      rw [Ideal.mem_comap, map_natCast]; exact hpP
  haveI : Finite (ℤ_[p] ⧸ P.under ℤ_[p]) := by
    rw [hunder]
    exact Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  haveI : Finite (R ⧸ P) := Module.finite_of_finite (ℤ_[p] ⧸ P.under ℤ_[p])
  letI := Fintype.ofFinite (R ⧸ P)
  obtain ⟨n, -, hcard⟩ := FiniteField.card (R ⧸ P) p
  refine ⟨(g : Ω), g.2, ?_, ?_, ?_, (n : ℕ), n.pos, ?_⟩
  · exact fun h => hg0 (Subtype.ext h)
  · exact (hP g).mp hgmem
  · obtain ⟨c, hc⟩ := hdvd _ hpP
    have : (p : Ω) = (g : Ω) * (c : Ω) := by rw [← hpR, hc]; rfl
    rw [this, mul_div_cancel_left₀ _ (fun h => hg0 (Subtype.ext h))]
    exact c.2
  · intro t ht
    have hmk : Ideal.Quotient.mk P (⟨t, ht⟩ ^ p ^ (n : ℕ)) = Ideal.Quotient.mk P ⟨t, ht⟩ := by
      rw [map_pow, ← hcard, FiniteField.pow_card]
    rw [Ideal.Quotient.eq] at hmk
    obtain ⟨c, hc⟩ := hdvd _ hmk
    have : t ^ p ^ (n : ℕ) - t = (g : Ω) * (c : Ω) := by
      have := congrArg (fun x : R => (x : Ω)) hc
      simpa using this
    rw [this, mul_div_cancel_left₀ _ (fun h => hg0 (Subtype.ext h))]
    exact c.2

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_valuation_lt_one_frobenius_congr : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ v : Valuation Ω NNReal, (∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1) → v (p : Ω) < 1 →
  ∀ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R → IsPrincipalIdealRing R →
  ∃ π ∈ R, π ≠ 0 ∧ v π < 1 ∧ (p : Ω) / π ∈ R ∧ ∃ f : ℕ, 0 < f ∧ ∀ t ∈ R, (t ^ p ^ f - t) / π ∈ R := by
  atlas_forward_decl GlobalTheory.exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt
end

section
section
namespace GlobalTheory

theorem localAlg_frob_fixed_isField_and_pth_roots :
    ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsLocalRing A]
  (T : Finset A) (f : ℕ), 0 < f → Algebra.adjoin k (T : Set A) = ⊤ → (∀ t ∈ T, t ^ p ^ f = t) →
  IsField A ∧ ∀ (y : A) (a : k), y ^ p = algebraMap k A a → ∃ b : k, y = algebraMap k A b := by
  intro p hp k A _ _ _ _ _ T f hf hT hfix
  have hp1 : 1 < p ^ f := Nat.one_lt_pow hf.ne' hp.out.one_lt

  have hint : ∀ t ∈ (T : Set A), IsIntegral k t := by
    intro t ht
    refine ⟨Polynomial.X ^ (p ^ f) - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hp1)
    · simp [hfix t ht]
  have hfinA : Module.Finite k (Algebra.adjoin k (T : Set A)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral T.finite_toSet hint
  rw [hT] at hfinA
  haveI : Module.Finite k A := Module.Finite.equiv (Subalgebra.topEquiv (R := k) (A := A)).toLinearEquiv

  have hpk : ((p ^ f : ℕ) : k) = 0 := by
    rw [CharP.cast_eq_zero_iff k p]; exact dvd_pow_self p hf.ne'
  have hD : KaehlerDifferential.D k A = 0 := by
    apply Derivation.ext_of_adjoin_eq_top (T : Set A) hT
    intro t ht
    have h1 := (KaehlerDifferential.D k A).leibniz_pow t (p ^ f)
    rw [hfix t ht] at h1
    rw [h1, ← Nat.cast_smul_eq_nsmul k, hpk, zero_smul]
    rfl
  haveI : Subsingleton (Ω[A⁄k]) := by
    constructor
    intro x y
    have hx : ∀ z : Ω[A⁄k], z = 0 := by
      intro z
      have htop := KaehlerDifferential.span_range_derivation k A
      have hz : z ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by rw [htop]; trivial
      rw [hD] at hz
      have : Set.range (⇑(0 : Derivation k A (Ω[A⁄k]))) ⊆ ({0} : Set (Ω[A⁄k])) := by
        rintro _ ⟨w, rfl⟩; simp
      have := Submodule.span_mono (R := A) this hz
      simpa using this
    rw [hx x, hx y]
  haveI : Algebra.FormallyUnramified k A := ⟨inferInstance⟩
  haveI : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hField : IsField A := IsArtinianRing.isField_of_isReduced_of_isLocalRing A
  refine ⟨hField, ?_⟩
  intro y a hy
  letI : Field A := hField.toField
  haveI : Algebra.IsSeparable k A := Algebra.FormallyUnramified.isSeparable k A
  haveI : ExpChar k p := ExpChar.prime hp.out
  have hmem : y ∈ perfectClosure k A := by
    rw [mem_perfectClosure_iff_pow_mem p]
    exact ⟨1, by rw [pow_one, hy]; exact ⟨a, rfl⟩⟩
  rw [perfectClosure.eq_bot_of_isSeparable, IntermediateField.mem_bot] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb.symm⟩

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_and_pthRoots_of_localAlg_frobenius_fixed : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsLocalRing A]
  (T : Finset A) (f : ℕ), 0 < f → Algebra.adjoin k (T : Set A) = ⊤ → (∀ t ∈ T, t ^ p ^ f = t) →
  IsField A ∧ ∀ (y : A) (a : k), y ^ p = algebraMap k A a → ∃ b : k, y = algebraMap k A b := by
  atlas_forward_decl GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots
end

section
section
namespace GlobalTheory.K5.IntFrac

open Polynomial

theorem mem_adjoin_inv_of_isIntegral' {R K : Type*} [CommRing R] [Field K] [Algebra R K] {z : K}
    (hz : z ≠ 0) (hi : IsIntegral R z) : z ∈ Algebra.adjoin R {z⁻¹} := by
  obtain ⟨p, hpm, hp⟩ := hi
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one,
    one_mul] at hp
  obtain ⟨m, hm⟩ : ∃ m, p.natDegree = m + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h => ?_
    rw [h, Finset.sum_range_zero, pow_zero, zero_add] at hp
    exact one_ne_zero hp
  rw [hm] at hp
  have hzn : z ^ (m + 1) = -∑ i ∈ Finset.range (m + 1), algebraMap R K (p.coeff i) * z ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hp
  have h1 : z = z ^ (m + 1) * z⁻¹ ^ m := by
    rw [pow_succ, mul_comm (z ^ m) z, mul_assoc, ← mul_pow, mul_inv_cancel₀ hz, one_pow, mul_one]
  have hterm : ∀ i ∈ Finset.range (m + 1), algebraMap R K (p.coeff i) * z ^ i * z⁻¹ ^ m =
      algebraMap R K (p.coeff i) * z⁻¹ ^ (m - i) := by
    intro i hi
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    rw [hk, Nat.add_sub_cancel_left, mul_assoc, pow_add, ← mul_assoc (z ^ i), ← mul_pow,
      mul_inv_cancel₀ hz, one_pow, one_mul]
  have key : z = -∑ i ∈ Finset.range (m + 1), algebraMap R K (p.coeff i) * z⁻¹ ^ (m - i) := by
    rw [← Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← neg_mul, ← hzn]
    exact h1
  have hmem : -∑ i ∈ Finset.range (m + 1), algebraMap R K (p.coeff i) * z⁻¹ ^ (m - i) ∈
      Algebra.adjoin R {z⁻¹} := by
    refine Subalgebra.neg_mem _ (Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _
      (Subalgebra.algebraMap_mem _ _) (Subalgebra.pow_mem _ (Algebra.subset_adjoin ?_) _))
    exact Set.mem_singleton _
  rw [← key] at hmem
  exact hmem

theorem mem_of_div_le_one : ∀ (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] (v : Valuation Ω NNReal), (∀ x : Ω, v x ≤ 1 ↔ IsIntegral O x) →
  ∀ (B : Subalgebra O Ω), (∀ x ∈ B, v x ≤ 1) → ∀ π ∈ B, π ≠ 0 → v π < 1 → (∀ x ∈ B, v x < 1 → x / π ∈ B) →
  ∀ a ∈ B, ∀ b ∈ B, v (a / b) ≤ 1 → a / b ∈ B := by
  intro O Ω _ _ _ v hv B hB π hπB hπ0 hπ1 hdiv
  have hvπ : 0 < v π := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hπ0)
  have hA : ∀ n : ℕ, ∀ a ∈ B, v (a / π ^ n) ≤ 1 → a / π ^ n ∈ B := by
    intro n
    induction n with
    | zero => intro a ha _; simpa using ha
    | succ k ih =>
      intro a ha hle
      have hlt : v a < 1 := by
        have he : v a = v (a / π ^ (k + 1)) * v π ^ (k + 1) := by
          rw [map_div₀, map_pow, div_mul_cancel₀]
          exact pow_ne_zero _ hvπ.ne'
        rw [he]
        calc v (a / π ^ (k + 1)) * v π ^ (k + 1) ≤ 1 * v π ^ (k + 1) := by gcongr
          _ < 1 := by
            rw [one_mul]
            exact pow_lt_one₀ hvπ.le hπ1 (Nat.succ_ne_zero k)
      have he : a / π ^ (k + 1) = a / π / π ^ k := by rw [pow_succ', div_div]
      rw [he] at hle ⊢
      exact ih _ (hdiv a ha hlt) hle
  intro a ha b hb hab
  by_cases hb0 : b = 0
  · rw [hb0, div_zero]
    exact B.zero_mem
  have hvb : 0 < v b := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hb0)
  have hex : ∃ n, v π ^ (n + 1) < v b := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hvb hπ1
    cases m with
    | zero => exact absurd (hB b hb) (not_le.mpr (by simpa using hm))
    | succ k => exact ⟨k, hm⟩
  classical
  set n := Nat.find hex with hndef
  have hn : v π ^ (n + 1) < v b := Nat.find_spec hex
  have hle : v b ≤ v π ^ n := by
    by_cases h0 : n = 0
    · rw [h0, pow_zero]
      exact hB b hb
    · have hmin := Nat.find_min hex (show n - 1 < n by omega)
      have hn1 : n - 1 + 1 = n := by omega
      rw [hn1] at hmin
      exact not_lt.mp hmin
  have hvπn : 0 < v π ^ n := pow_pos hvπ n
  have hvw_le : v (b / π ^ n) ≤ 1 := by
    rw [map_div₀, map_pow, div_le_one₀ hvπn]
    exact hle
  have hwB : b / π ^ n ∈ B := hA n b hb hvw_le
  have hvw : v (b / π ^ n) = 1 := by
    refine le_antisymm hvw_le (not_lt.mp fun hlt => ?_)
    have h2 := hB _ (hdiv _ hwB hlt)
    rw [div_div, ← pow_succ, map_div₀, map_pow, div_le_one₀ (pow_pos hvπ _)] at h2
    exact not_le.mpr hn h2
  have hw0 : b / π ^ n ≠ 0 := by
    intro h
    rw [h, map_zero] at hvw
    exact zero_ne_one hvw
  have hwinv : (b / π ^ n)⁻¹ ∈ B := by
    have hint : IsIntegral O (b / π ^ n)⁻¹ := (hv _).mp (by rw [map_inv₀, hvw, inv_one])
    have hmem := mem_adjoin_inv_of_isIntegral' (inv_ne_zero hw0) hint
    rw [inv_inv] at hmem
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hwB) hmem
  have haπ : a / π ^ n ∈ B := by
    apply hA n a ha
    have he : a / π ^ n = a / b * (b / π ^ n) := by field_simp
    rw [he, map_mul, hvw, mul_one]
    exact hab
  have he : a / b = a / π ^ n * (b / π ^ n)⁻¹ := by field_simp
  rw [he]
  exact B.mul_mem haπ hwinv

end GlobalTheory.K5.IntFrac
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.div_mem_subalgebra_of_valuation_le_one_of_uniformizer : ∀ (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] (v : Valuation Ω NNReal), (∀ x : Ω, v x ≤ 1 ↔ IsIntegral O x) →
  ∀ (B : Subalgebra O Ω), (∀ x ∈ B, v x ≤ 1) → ∀ π ∈ B, π ≠ 0 → v π < 1 → (∀ x ∈ B, v x < 1 → x / π ∈ B) →
  ∀ a ∈ B, ∀ b ∈ B, v (a / b) ≤ 1 → a / b ∈ B := by
  atlas_forward_decl GlobalTheory.K5.IntFrac.mem_of_div_le_one
end

section
section
open GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.NotPow

theorem residue_core : ∀ (p : ℕ) [Fact p.Prime] (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω], (Ideal.span {(p : O)}).IsMaximal →
  ∀ (v : Valuation Ω NNReal), (∀ x : Ω, v x ≤ 1 ↔ IsIntegral O x) →
  ∀ (T : Finset Ω), (∀ t ∈ T, IsIntegral O t) → ∀ π ∈ Algebra.adjoin O (T : Set Ω), π ≠ 0 → v π < 1 →
  (p : Ω) / π ∈ Algebra.adjoin O (T : Set Ω) →
  ∀ f : ℕ, 0 < f → (∀ t ∈ T, (t ^ p ^ f - t) / π ∈ Algebra.adjoin O (T : Set Ω)) →
  (∀ x ∈ Algebra.adjoin O (T : Set Ω), v x < 1 → x / π ∈ Algebra.adjoin O (T : Set Ω)) ∧
  ∀ y ∈ Algebra.adjoin O (T : Set Ω), ∀ a : O, v (y ^ p - algebraMap O Ω a) < 1 → ∃ b : O, v (y - algebraMap O Ω b) < 1 := by
  intro p _ O Ω _ _ _ hmax v hv T hT π hπ hπ0 hvπ hpπ f hf hstep
  classical
  have hint : ∀ x ∈ Algebra.adjoin O (T : Set Ω), v x ≤ 1 := fun x hx =>
    (hv x).2 (Algebra.adjoin_le (S := integralClosure O Ω) (fun t ht => hT t ht) hx)
  have hunit : ∀ x ∈ Algebra.adjoin O (T : Set Ω), v x = 1 →
      ∃ w ∈ Algebra.adjoin O (T : Set Ω), x * w = 1 := by
    intro x hx hx1
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx1
      exact zero_ne_one hx1
    obtain ⟨P, hPm, hP⟩ := (hv x⁻¹).1 (by rw [map_inv₀, hx1, inv_one])
    letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
    have h1 := Polynomial.eval₂_reverse_mul_pow (algebraMap O Ω) x⁻¹ P
    rw [hP, invOf_eq_inv, inv_inv] at h1
    have h2 : Polynomial.eval₂ (algebraMap O Ω) x P.reverse = 0 :=
      (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ (inv_ne_zero hx0))
    have h3 := Polynomial.divX_mul_X_add P.reverse
    rw [Polynomial.coeff_zero_reverse, hPm.leadingCoeff, Polynomial.C_1] at h3
    rw [← h3, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
      Polynomial.eval₂_one] at h2
    refine ⟨-Polynomial.eval₂ (algebraMap O Ω) x (Polynomial.divX P.reverse), neg_mem ?_, ?_⟩
    · have hm := (Polynomial.aeval (⟨x, hx⟩ : Algebra.adjoin O (T : Set Ω))
        (Polynomial.divX P.reverse)).2
      rwa [Polynomial.aeval_subalgebra_coe, Polynomial.aeval_def] at hm
    · linear_combination -h2
  let I : Ideal (Algebra.adjoin O (T : Set Ω)) := Ideal.span {⟨π, hπ⟩}
  have memI : ∀ z : Algebra.adjoin O (T : Set Ω), z ∈ I ↔
      (z : Ω) / π ∈ Algebra.adjoin O (T : Set Ω) := by
    intro z
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, rfl⟩
      show ((w : Ω) * π) / π ∈ _
      rw [mul_div_cancel_right₀ _ hπ0]
      exact w.2
    · intro h
      exact ⟨⟨(z : Ω) / π, h⟩, Subtype.ext (div_mul_cancel₀ _ hπ0)⟩
  have hvI : ∀ z : Algebra.adjoin O (T : Set Ω), z ∈ I → v z < 1 := by
    intro z hz
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    show v ((w : Ω) * π) < 1
    rw [map_mul]
    calc v w * v π ≤ 1 * v π := mul_le_mul_of_nonneg_right (hint _ w.2) zero_le
      _ < 1 := by rw [one_mul]; exact hvπ
  have hpI : (p : Algebra.adjoin O (T : Set Ω)) ∈ I := by
    rw [memI]
    simpa using hpπ
  haveI hmaxI := hmax
  letI hk : Field (O ⧸ Ideal.span {(p : O)}) := Ideal.Quotient.field _
  haveI : CharP (O ⧸ Ideal.span {(p : O)}) p :=
    CharP.quotient O p (fun hu => hmax.ne_top (Ideal.span_singleton_eq_top.2 hu))
  let φ : (O ⧸ Ideal.span {(p : O)}) →+* Algebra.adjoin O (T : Set Ω) ⧸ I :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp (algebraMap O _)) (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
      exact I.mul_mem_left _ hpI)
  letI : Algebra (O ⧸ Ideal.span {(p : O)}) (Algebra.adjoin O (T : Set Ω) ⧸ I) := φ.toAlgebra
  haveI hnt : Nontrivial (Algebra.adjoin O (T : Set Ω) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (by
    intro h
    have h1 : (1 : Algebra.adjoin O (T : Set Ω)) ∈ I := by rw [h]; exact Submodule.mem_top
    have := hvI 1 h1
    simp at this)
  haveI : IsLocalRing (Algebra.adjoin O (T : Set Ω) ⧸ I) := by
    refine { toNontrivial := hnt, isUnit_or_isUnit_of_add_one := ?_ }
    intro a b hab
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hxy : x + y - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, hab, map_one, sub_self]
    have hv1 := hvI _ hxy
    have key : v x = 1 ∨ v y = 1 := by
      by_contra hcon
      push_neg at hcon
      have hx' : v x < 1 := lt_of_le_of_ne (hint _ x.2) hcon.1
      have hy' : v y < 1 := lt_of_le_of_ne (hint _ y.2) hcon.2
      have e1 : (1 : Ω) = ((x : Ω) + y) - ((x + y - 1 : Algebra.adjoin O (T : Set Ω)) : Ω) := by
        push_cast
        ring
      have : v (1 : Ω) < 1 := by
        rw [e1]
        exact lt_of_le_of_lt (v.map_sub _ _)
          (max_lt (lt_of_le_of_lt (v.map_add _ _) (max_lt hx' hy')) hv1)
      simp at this
    rcases key with h | h
    · obtain ⟨w, hw, hxw⟩ := hunit _ x.2 h
      left
      have e : x * ⟨w, hw⟩ = 1 := Subtype.ext hxw
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I ⟨w, hw⟩) ?_
      rw [← map_mul, e, map_one]
    · obtain ⟨w, hw, hyw⟩ := hunit _ y.2 h
      right
      have e : y * ⟨w, hw⟩ = 1 := Subtype.ext hyw
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I ⟨w, hw⟩) ?_
      rw [← map_mul, e, map_one]
  let T' : Finset (Algebra.adjoin O (T : Set Ω) ⧸ I) :=
    T.attach.image (fun t => Ideal.Quotient.mk I ⟨t.1, Algebra.subset_adjoin (Finset.mem_coe.2 t.2)⟩)
  have hgen0 : ∀ x (hx : x ∈ Algebra.adjoin O (T : Set Ω)),
      Ideal.Quotient.mk I ⟨x, hx⟩ ∈ Algebra.adjoin (O ⧸ Ideal.span {(p : O)})
        (T' : Set (Algebra.adjoin O (T : Set Ω) ⧸ I)) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem t ht =>
      apply Algebra.subset_adjoin
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩
    | algebraMap r =>
      convert Subalgebra.algebraMap_mem
        (Algebra.adjoin (O ⧸ Ideal.span {(p : O)}) (T' : Set (Algebra.adjoin O (T : Set Ω) ⧸ I)))
        (Ideal.Quotient.mk (Ideal.span {(p : O)}) r) using 1
      rfl
    | add x y hx hy ihx ihy =>
      have e : (⟨x + y, add_mem hx hy⟩ : Algebra.adjoin O (T : Set Ω)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, map_add]
      exact add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      have e : (⟨x * y, mul_mem hx hy⟩ : Algebra.adjoin O (T : Set Ω)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, map_mul]
      exact mul_mem ihx ihy
  have hgen : Algebra.adjoin (O ⧸ Ideal.span {(p : O)})
      (T' : Set (Algebra.adjoin O (T : Set Ω) ⧸ I)) = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hgen0 x hx
  have hfrob : ∀ t ∈ T', t ^ p ^ f = t := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨⟨t0, ht0⟩, -, rfl⟩ := ht
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, memI]
    simpa using hstep t0 ht0
  obtain ⟨hfield, hroot⟩ := GlobalTheory.T.isField_and_pthRoots_of_localAlg_frobenius_fixed p (O ⧸ Ideal.span {(p : O)})
    (Algebra.adjoin O (T : Set Ω) ⧸ I) T' f hf hgen hfrob
  have hzero : ∀ z : Algebra.adjoin O (T : Set Ω), v z < 1 → z ∈ I := by
    intro z hz
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    by_contra hne
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : z * w - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hb, map_one, sub_self]
    have h2 := hvI _ h1
    have h3 : v ((z : Ω) * w) < 1 := by
      rw [map_mul]
      calc v z * v w ≤ v z * 1 := mul_le_mul_of_nonneg_left (hint _ w.2) zero_le
        _ < 1 := by rw [mul_one]; exact hz
    have e1 : (1 : Ω) = (z : Ω) * w - ((z * w - 1 : Algebra.adjoin O (T : Set Ω)) : Ω) := by
      push_cast
      ring
    have : v (1 : Ω) < 1 := by
      rw [e1]
      exact lt_of_le_of_lt (v.map_sub _ _) (max_lt h3 h2)
    simp at this
  refine ⟨fun x hx hvx => (memI ⟨x, hx⟩).1 (hzero _ hvx), ?_⟩
  intro y hy a hva
  have hI : (⟨y, hy⟩ : Algebra.adjoin O (T : Set Ω)) ^ p - algebraMap O _ a ∈ I :=
    hzero _ (by simpa using hva)
  have heq : (Ideal.Quotient.mk I ⟨y, hy⟩) ^ p =
      algebraMap (O ⧸ Ideal.span {(p : O)}) _ (Ideal.Quotient.mk _ a) := by
    have h0 := (Ideal.Quotient.eq_zero_iff_mem).2 hI
    rw [map_sub, map_pow] at h0
    exact sub_eq_zero.1 h0
  obtain ⟨b', hb'⟩ := hroot _ _ heq
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  refine ⟨b, ?_⟩
  have h5 : (⟨y, hy⟩ : Algebra.adjoin O (T : Set Ω)) - algebraMap O _ b ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hb', sub_eq_zero]
    rfl
  simpa using hvI _ h5

theorem q_not_pow_mod (p : ℕ) [hp : Fact p.Prime] (a : O0 p) : ¬ (p : O0 p) ∣ a ^ p - qO p := by
  intro h
  obtain ⟨e, he⟩ := exists_completedLaurent_quot_prime_equiv_laurentFp p
  have h1 := (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr h
  rw [map_sub, map_pow, sub_eq_zero] at h1
  have h2 := congrArg e h1
  rw [map_pow, he] at h2
  have h3 := congrArg HahnSeries.order h2
  rw [HahnSeries.order_pow, HahnSeries.order_single one_ne_zero, nsmul_eq_mul] at h3
  have h4 : (p : ℤ) ∣ 1 := Dvd.intro _ h3
  exact hp.out.not_dvd_one (by exact_mod_cast h4)

theorem not_pow_mod_max : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgZp p s) →
  ∀ y ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)), IsInt p y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt p ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω)) := by
  intro p _ Ω _ _ hclo S hS y hy hyint
  rintro ⟨m, hm, hmint⟩
  classical
  obtain ⟨v, hv, -, hvp0, hvp1⟩ := exists_valuation_isInt p Ω hclo
  haveI := Basic.charZero_of_isClo hclo
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have huni := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
  have hmax : (Ideal.span {(p : O0 p)}).IsMaximal := by
    rw [← huni]
    exact IsLocalRing.maximalIdeal.isMaximal _
  letI : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap ℤ_[p] Ω) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have e := PadicInt.unitCoeff_spec hx0
    rw [e, map_mul, map_pow, map_natCast] at hx
    rcases mul_eq_zero.1 hx with h | h
    · exact ((Units.isUnit _).map (algebraMap ℤ_[p] Ω)).ne_zero h
    · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h
  have hvint : ∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1 := fun x hx =>
    (hv x).2 (IsIntegral.tower_top (A := O0 p) hx)
  have hSalg : ∀ s ∈ S, IsAlgebraic ℤ_[p] s := by
    intro s hs
    obtain ⟨P, hP0, hP⟩ := hS s hs
    exact ⟨P, hP0, by rwa [Polynomial.aeval_map_algebraMap] at hP⟩
  obtain ⟨R, hRfin, hRpid, hRS⟩ := GlobalTheory.T.exists_finite_pid_subalgebra_padicInt_contains_fractions p Ω hinj S hSalg
  obtain ⟨π, hπR, hπ0, hvπ, hpπ, f, hf, hstep⟩ :=
    GlobalTheory.T.exists_uniformizer_valuation_lt_one_frobenius_congr p Ω hinj v hvint hvp1 R hRfin hRpid
  have hfg : (Subalgebra.toSubmodule R).FG := Module.Finite.iff_fg.1 hRfin
  obtain ⟨T, hT⟩ := Subalgebra.fg_of_fg_toSubmodule hfg
  have hRB : ∀ x ∈ R, x ∈ Algebra.adjoin (O0 p) (T : Set Ω) := by
    intro x hx
    have hle : Algebra.adjoin ℤ_[p] (T : Set Ω) ≤
        (Algebra.adjoin (O0 p) (T : Set Ω)).restrictScalars ℤ_[p] :=
      Algebra.adjoin_le (fun t ht => (Subalgebra.mem_restrictScalars _).2 (Algebra.subset_adjoin ht))
    rw [hT] at hle
    exact (Subalgebra.mem_restrictScalars _).1 (hle hx)
  have hTR : ∀ t ∈ T, t ∈ R := fun t ht => hT ▸ Algebra.subset_adjoin (Finset.mem_coe.2 ht)
  have hTint : ∀ t ∈ T, IsIntegral (O0 p) t := fun t ht =>
    (IsIntegral.of_mem_of_fg R hfg t (hTR t ht)).tower_top
  obtain ⟨hdiv, hres⟩ := residue_core p (O0 p) Ω hmax v hv T hTint π (hRB _ hπR) hπ0 hvπ
    (hRB _ hpπ) f hf (fun t ht => hRB _ (hstep t (hTR t ht)))
  have hBint : ∀ x ∈ Algebra.adjoin (O0 p) (T : Set Ω), v x ≤ 1 := fun x hx =>
    (hv x).2 (Algebra.adjoin_le (S := integralClosure (O0 p) Ω) (fun t ht => hTint t ht) hx)
  have hclosed := GlobalTheory.T.div_mem_subalgebra_of_valuation_le_one_of_uniformizer (O0 p) Ω v hv _ hBint π (hRB _ hπR) hπ0 hvπ hdiv
  have hsub : Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) ≤
      Subfield.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω) := by
    rw [Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ c)
    · obtain ⟨a, ha, b, hb, rfl⟩ := hRS x hx
      exact div_mem (Subfield.subset_closure (hRB _ ha)) (Subfield.subset_closure (hRB _ hb))
  obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.1 (hsub hy)
  have hcl : ∀ z ∈ Subring.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω),
      z ∈ Algebra.adjoin (O0 p) (T : Set Ω) := fun z hz =>
    (Subring.closure_le (t := (Algebra.adjoin (O0 p) (T : Set Ω)).toSubring)).2 (fun _ h => h) hz
  have hyv : v y ≤ 1 := (hv y).2 hyint
  have hyB : y ∈ Algebra.adjoin (O0 p) (T : Set Ω) := by
    rw [← hab]
    exact hclosed a (hcl a ha) b (hcl b hb) (by rw [hab]; exact hyv)
  have hvq : v (y ^ p - algebraMap (O0 p) Ω (qO p)) < 1 := by
    have h1 := (hv _).2 hmint
    rw [map_div₀, map_pow] at h1
    have h2 : v (y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m < 1 :=
      lt_of_le_of_lt ((div_le_one₀ hvp0).1 h1) hvp1
    by_contra hc
    push_neg at hc
    exact absurd h2 (not_lt.2 (one_le_pow₀ hc))
  obtain ⟨b, hb⟩ := hres y hyB (qO p) hvq
  have hbv : v (algebraMap (O0 p) Ω b) ≤ 1 := (hv _).2 isIntegral_algebraMap
  have hvb : v (algebraMap (O0 p) Ω (b ^ p - qO p)) < 1 := by
    have e : algebraMap (O0 p) Ω (b ^ p - qO p) = (y ^ p - algebraMap (O0 p) Ω (qO p)) -
        (y ^ p - (algebraMap (O0 p) Ω b) ^ p) := by
      rw [map_sub, map_pow]
      ring
    have hg : v (y ^ p - (algebraMap (O0 p) Ω b) ^ p) < 1 := by
      rw [← geom_sum₂_mul, map_mul]
      have hs : v (∑ i ∈ Finset.range p, y ^ i * (algebraMap (O0 p) Ω b) ^ (p - 1 - i)) ≤ 1 := by
        apply v.map_sum_le
        intro i _
        rw [map_mul, map_pow, map_pow]
        exact mul_le_one' (pow_le_one' hyv _) (pow_le_one' hbv _)
      calc _ ≤ 1 * v (y - algebraMap (O0 p) Ω b) := mul_le_mul_of_nonneg_right hs zero_le
        _ < 1 := by rw [one_mul]; exact hb
    rw [e]
    exact lt_of_le_of_lt (v.map_sub _ _) (max_lt hvq hg)
  apply q_not_pow_mod p b
  by_contra hnd
  have hu : IsUnit (b ^ p - qO p) := by
    by_contra hnu
    apply hnd
    have hmem : b ^ p - qO p ∈ IsLocalRing.maximalIdeal (O0 p) :=
      (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [huni] at hmem
    exact Ideal.mem_span_singleton.1 hmem
  obtain ⟨u, hu⟩ := hu
  have h1 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h2 : v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) ≤ 1 := (hv _).2 isIntegral_algebraMap
  rw [← hu] at hvb
  have h4 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) < 1 :=
    calc _ ≤ v (algebraMap (O0 p) Ω (u : O0 p)) * 1 := mul_le_mul_of_nonneg_left h2 zero_le
      _ < 1 := by rw [mul_one]; exact hvb
  rw [h1] at h4
  exact lt_irrefl _ h4

end GlobalTheory.K5.NotPow
end

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerParameter_not_pow_mod_maximalIdeal_adjoin_algebraic : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgZp p s) →
  ∀ y ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)), IsInt p y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt p ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω)) := by
  atlas_forward_decl GlobalTheory.K5.NotPow.not_pow_mod_max
end

section
section
open GlobalTheory.K5

namespace GlobalTheory.K5.ResidueIndep

open Polynomial

theorem field_indep {k : Type} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] (K : Subfield k)
    (N : ℕ) (t : k) (ha : t ^ p ^ N ∈ K) (hna : ∀ b ∈ K, b ^ p ≠ t ^ p ^ N)
    (c : ℕ → k) (hc : ∀ j < p ^ N, c j ∈ K)
    (hs : ∑ j ∈ Finset.range (p ^ N), c j * t ^ j = 0) : ∀ j < p ^ N, c j = 0 := by
  classical
  haveI : ExpChar K p := ExpChar.prime hp.out
  obtain ⟨n, y, hf⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C (F := K) p (x := t)).1
    ((minpoly.natSepDegree_eq_one_iff_pow_mem (F := K) p (x := t)).2 ⟨N, ⟨⟨_, ha⟩, rfl⟩⟩)
  have hy : t ^ p ^ n = (y : k) := by
    have := minpoly.aeval K t
    rw [hf] at this
    simp only [map_sub, map_pow, aeval_X, aeval_C] at this
    exact sub_eq_zero.1 this
  have hNn : N ≤ n := by
    by_contra h
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.1 h)
    refine hna ((y : k) ^ p ^ r) (K.pow_mem y.2 _) ?_
    rw [← hy, ← pow_mul, ← pow_mul, pow_add, pow_add, pow_one, mul_assoc]
  let c' : ℕ → K := fun j => if h : j < p ^ N then ⟨c j, hc j h⟩ else 0
  let P : K[X] := ∑ j ∈ Finset.range (p ^ N), monomial j (c' j)
  have hP : aeval t P = 0 := by
    rw [← hs, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [aeval_monomial]
    simp only [c', dif_pos (Finset.mem_range.1 hj)]
    rfl
  have hP0 : P = 0 := by
    by_contra h
    have h1 := minpoly.degree_le_of_ne_zero K t h hP
    have h2 : P.degree < ((p ^ N : ℕ) : WithBot ℕ) := by
      refine (degree_sum_le _ _).trans_lt ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro j hj
      exact (degree_monomial_le _ _).trans_lt (by exact_mod_cast Finset.mem_range.1 hj)
    rw [hf, degree_X_pow_sub_C (pow_pos hp.out.pos n)] at h1
    have h3 := h1.trans_lt h2
    have h4 : p ^ n < p ^ N := by exact_mod_cast h3
    exact absurd (Nat.pow_le_pow_right hp.out.pos hNn) (not_le.2 h4)
  intro j hj
  have h1 : P.coeff j = c' j := by
    simp only [P, finset_sum_coeff, coeff_monomial]
    rw [Finset.sum_ite_eq' , if_pos (Finset.mem_range.2 hj)]
  rw [hP0, coeff_zero] at h1
  have h2 := congrArg Subtype.val h1
  simp only [c', dif_pos hj] at h2
  exact h2.symm

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem mem_rad_iff (h : IsClo p Ω) (x : integralClosure (O0 p) Ω) :
    x ∈ (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical ↔
      ∃ m : ℕ, 0 < m ∧ IsInt p ((x : Ω) ^ m / (p : Ω)) := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hn
    refine ⟨n + 1, n.succ_pos, ?_⟩
    have h1 : (z : Ω) * p = (x : Ω) ^ n := by exact_mod_cast congrArg Subtype.val hz
    have h2 : (x : Ω) ^ (n + 1) / p = ((z * x : integralClosure (O0 p) Ω) : Ω) := by
      rw [pow_succ, ← h1]; push_cast; field_simp
    rw [h2]
    exact (z * x).2
  · rintro ⟨m, -, hm⟩
    refine ⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hm⟩, Subtype.ext ?_⟩⟩
    push_cast
    field_simp

theorem isInt_inv (h : IsClo p Ω) (x : Ω)
    (hx : ¬ ∃ m : ℕ, 0 < m ∧ IsInt p (x ^ m / (p : Ω))) : x ≠ 0 ∧ IsInt p x⁻¹ := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpi : IsIntegral (O0 p) (p : Ω) := by exact_mod_cast Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx ⟨1, one_pos, by simpa [IsInt] using isIntegral_zero⟩
  refine ⟨hx0, ?_⟩
  obtain ⟨a, b, hb, h1, h2⟩ := GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit p Ω h x hx0
  by_cases ha : 0 < a
  · exfalso
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = (n + 1 : ℕ) := ⟨(a - 1).toNat, by push_cast; omega⟩
    refine hx ⟨b, hb, ?_⟩
    have : x ^ b / (p : Ω) = x ^ b / (p : Ω) ^ ((n + 1 : ℕ) : ℤ) * (p : Ω) ^ n := by
      rw [zpow_natCast]; field_simp; ring
    rw [this]
    exact IsIntegral.mul h1 (hpi.pow n)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -(n : ℤ) := ⟨(-a).toNat, by omega⟩
    refine IsIntegral.of_pow hb ?_
    have : x⁻¹ ^ b = (p : Ω) ^ (-(n : ℤ)) / x ^ b * (p : Ω) ^ n := by
      rw [zpow_neg, zpow_natCast, inv_pow]; field_simp
    rw [this]
    exact IsIntegral.mul h2 (hpi.pow n)

theorem rad_isMaximal (h : IsClo p Ω) :
    (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical.IsMaximal := by
  haveI := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [Ideal.isMaximal_iff]
  constructor
  · rw [mem_rad_iff h]
    rintro ⟨m, -, hm⟩
    refine Basic.not_cong_one_zero h 1 one_ne_zero ⟨_, hm, ?_⟩
    simp [hp0]
  · intro J x _ hx hxJ
    rw [mem_rad_iff h] at hx
    obtain ⟨h0, h1⟩ := isInt_inv h _ hx
    have : (1 : integralClosure (O0 p) Ω) = ⟨_, h1⟩ * x :=
      Subtype.ext (inv_mul_cancel₀ h0).symm
    rw [this]
    exact J.mul_mem_left _ hxJ

theorem residue_indep : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ E : Subfield Ω, Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) →
  (∀ y ∈ E, IsInt p y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt p ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω))) →
  ∀ (T : Tower p Ω) (N : ℕ) (d : ℕ → Ω), (∀ j < p ^ N, d j ∈ E ∧ IsInt p (d j)) →
  (∃ m : ℕ, 0 < m ∧ IsInt p ((∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j) ^ m / (p : Ω))) →
  ∀ j < p ^ N, ∃ m : ℕ, 0 < m ∧ IsInt p (d j ^ m / (p : Ω)) := by
  intro p hp Ω _ _ h E hE hq T N d hd hs
  classical
  set M := (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical with hM
  have hmem : ∀ x : integralClosure (O0 p) Ω, Ideal.Quotient.mk M x = 0 ↔
      ∃ m : ℕ, 0 < m ∧ IsInt p ((x : Ω) ^ m / (p : Ω)) := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hM, mem_rad_iff h]
  haveI : M.IsMaximal := rad_isMaximal h
  letI : Field (integralClosure (O0 p) Ω ⧸ M) := Ideal.Quotient.field M
  haveI : CharP (integralClosure (O0 p) Ω ⧸ M) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk M),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
  let K : Subfield (integralClosure (O0 p) Ω ⧸ M) :=
    { (E.toSubring.comap (integralClosure (O0 p) Ω).val.toRingHom).map (Ideal.Quotient.mk M) with
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        by_cases h0 : Ideal.Quotient.mk M y = 0
        · exact ⟨0, E.zero_mem, by rw [h0, inv_zero, map_zero]⟩
        · obtain ⟨h1, h2⟩ := isInt_inv h (y : Ω) (fun hh => h0 ((hmem y).2 hh))
          refine ⟨⟨_, h2⟩, E.inv_mem hy, ?_⟩
          refine eq_inv_of_mul_eq_one_left ?_
          rw [← map_mul, ← map_one (Ideal.Quotient.mk M)]
          congr 1
          exact Subtype.ext (inv_mul_cancel₀ h1) }
  have hqi : IsIntegral (O0 p) (T.qq N) :=
    IsIntegral.of_pow (pow_pos hp.out.pos N) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : integralClosure (O0 p) Ω := ⟨_, hqi⟩
  have ht : ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) = algebraMap (O0 p) Ω (qO p) := by
    rw [← Basic.qq_pow T N]; rfl
  let d' : ℕ → integralClosure (O0 p) Ω := fun j => if hj : j < p ^ N then ⟨d j, (hd j hj).2⟩ else 0
  have hd' : ∀ j < p ^ N, (d' j : Ω) = d j := fun j hj => by simp only [d', dif_pos hj]
  have key := field_indep p K N (Ideal.Quotient.mk M t)
    ⟨t ^ p ^ N, by
      show ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) ∈ E
      rw [ht]; exact hE ⟨_, rfl⟩, map_pow _ _ _⟩
    (by
      rintro _ ⟨y, hy, rfl⟩ hb
      refine hq y hy y.2 ?_
      rw [← ht]
      have := (hmem (y ^ p - t ^ p ^ N)).1 (by rw [map_sub, map_pow, map_pow, hb, sub_self])
      exact this)
    (fun j => Ideal.Quotient.mk M (d' j))
    (fun j hj => ⟨d' j, by
      show (d' j : Ω) ∈ E
      rw [hd' j hj]; exact (hd j hj).1, rfl⟩)
    (by
      have e : ((∑ j ∈ Finset.range (p ^ N), d' j * t ^ j : integralClosure (O0 p) Ω) : Ω) =
          ∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j := by
        push_cast
        exact Finset.sum_congr rfl fun j hj => by rw [hd' j (Finset.mem_range.1 hj)]
      have := (hmem _).2 (e ▸ hs)
      simpa only [map_sum, map_mul, map_pow] using this)
  intro j hj
  rw [← hd' j hj]
  exact (hmem _).1 (key j hj)

end GlobalTheory.K5.ResidueIndep
end

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_tower_powers_linearIndependent : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ E : Subfield Ω, Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) →
  (∀ y ∈ E, IsInt p y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt p ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω))) →
  ∀ (T : Tower p Ω) (N : ℕ) (d : ℕ → Ω), (∀ j < p ^ N, d j ∈ E ∧ IsInt p (d j)) →
  (∃ m : ℕ, 0 < m ∧ IsInt p ((∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j) ^ m / (p : Ω))) →
  ∀ j < p ^ N, ∃ m : ℕ, 0 < m ∧ IsInt p (d j ^ m / (p : Ω)) := by
  atlas_forward_decl GlobalTheory.K5.ResidueIndep.residue_indep
end

section
open GlobalTheory.K5

namespace GlobalTheory.K5.Orth

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem p_ne_zero' (h : IsClo p Ω) : (p : Ω) ≠ 0 := by
  haveI := GlobalTheory.K5.Basic.charZero_of_isClo h
  exact_mod_cast hp.out.ne_zero

theorem not_isInt_inv_p (h : IsClo p Ω) : ¬ IsInt p ((p : Ω)⁻¹) := by
  intro hi
  apply GlobalTheory.K5.Basic.not_cong_one_zero h 1 one_ne_zero
  refine ⟨(p : Ω)⁻¹, hi, ?_⟩
  rw [pow_one, sub_zero, mul_inv_cancel₀ (p_ne_zero' h)]

theorem isInt_natPow_p (k : ℕ) : IsInt p ((p : Ω) ^ k) := by
  have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ω) ((p : ℤ) ^ k)
  simpa using this

theorem isInt_div (h : IsClo p Ω) {x y : Ω} (hy : y ≠ 0) {a a' : ℤ} {b b' : ℕ} (hb : 0 < b)
    (hb' : 0 < b') (h1 : IsInt p (x ^ b / (p : Ω) ^ a)) (h2 : IsInt p ((p : Ω) ^ a' / y ^ b'))
    (hle : (a' : ℚ) / b' ≤ a / b) : IsInt p (x / y) := by
  have hp0 := p_ne_zero' h
  have he : 0 ≤ a * b' - a' * b := by
    have hb0 : (0 : ℚ) < b := by exact_mod_cast hb
    have hb0' : (0 : ℚ) < b' := by exact_mod_cast hb'
    rw [div_le_div_iff₀ hb0' hb0] at hle
    have : (a' * b : ℚ) ≤ a * b' := hle
    exact_mod_cast (sub_nonneg.2 this)
  obtain ⟨e, he'⟩ := Int.eq_ofNat_of_zero_le he
  have key : (x / y) ^ (b * b') = (x ^ b / (p : Ω) ^ a) ^ b' * ((p : Ω) ^ a' / y ^ b') ^ b *
      (p : Ω) ^ e := by
    have hpe : (p : Ω) ^ e = ((p : Ω) ^ a) ^ b' / ((p : Ω) ^ a') ^ b := by
      rw [← zpow_natCast, ← he', zpow_sub₀ hp0, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    rw [hpe]
    have hP : (p : Ω) ^ a ≠ 0 := zpow_ne_zero _ hp0
    have hP' : (p : Ω) ^ a' ≠ 0 := zpow_ne_zero _ hp0
    generalize (p : Ω) ^ a = P at *
    generalize (p : Ω) ^ a' = P' at *
    have e1 : (y ^ b') ^ b = y ^ (b * b') := by rw [← pow_mul, mul_comm]
    have e2 : (x ^ b) ^ b' = x ^ (b * b') := by rw [← pow_mul]
    simp only [div_pow, e1, e2]
    have h3 : (P ^ b') ≠ 0 := pow_ne_zero _ hP
    have h4 : (P' ^ b) ≠ 0 := pow_ne_zero _ hP'
    have h5 : y ^ (b * b') ≠ 0 := pow_ne_zero _ hy
    rw [div_mul_div_comm, div_mul_div_comm, div_eq_div_iff h5 (mul_ne_zero (mul_ne_zero h3 h5) h4)]
    ring
  have hi : IsInt p ((x / y) ^ (b * b')) := by
    rw [key]
    exact ((h1.pow b').mul (h2.pow b)).mul (isInt_natPow_p e)
  exact IsIntegral.of_pow (Nat.mul_pos hb hb') hi

end GlobalTheory.K5.Orth

namespace GlobalTheory.K5.Orth

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem normalize (h : IsClo p Ω)
    (hV : ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsInt p (x ^ b / (p : Ω) ^ a) ∧
      IsInt p ((p : Ω) ^ a / x ^ b))
    (n : ℕ) (c : ℕ → Ω) (hc : ∃ j < n, ¬ IsInt p (c j)) :
    ∃ l : Ω, IsAlgZp p l ∧ (∃ m : ℕ, 0 < m ∧ IsInt p (l ^ m / (p : Ω))) ∧
      (∀ j < n, IsInt p (l * c j)) ∧
      ∃ j < n, ¬ ∃ m : ℕ, 0 < m ∧ IsInt p ((l * c j) ^ m / (p : Ω)) := by
  classical
  have hp0 := p_ne_zero' h
  choose A B hB h1 h2 using hV
  let w : Ω → ℚ := fun x => if hx : x = 0 then 0 else (A x hx : ℚ) / B x hx
  obtain ⟨j1, hj1, hnj1⟩ := hc
  have hc1 : c j1 ≠ 0 := fun e => hnj1 (e ▸ isIntegral_zero)
  obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image ((Finset.range n).filter (fun j => c j ≠ 0))
    (fun j => w (c j)) ⟨j1, by simp [hj1, hc1]⟩
  simp only [Finset.mem_filter, Finset.mem_range] at hj0 hmin
  obtain ⟨hj0n, hx0⟩ := hj0
  have hdiv : ∀ j < n, c j ≠ 0 → IsInt p (c j / c j0) := by
    intro j hj hcj
    refine isInt_div h hx0 (hB _ hcj) (hB _ hx0) (h1 _ hcj) (h2 _ hx0) ?_
    have := hmin j ⟨hj, hcj⟩
    simpa [w, hcj, hx0] using this
  have hb := hB _ hx0
  have hu := h1 _ hx0
  have hu' := h2 _ hx0
  generalize A (c j0) hx0 = a at hu hu'
  generalize B (c j0) hx0 = b at hb hu hu'
  have hxInt_of : IsInt p (c j0) → ∀ j < n, IsInt p (c j) := by
    intro hxi j hj
    by_cases hcj : c j = 0
    · rw [hcj]; exact isIntegral_zero
    · have := (hdiv j hj hcj).mul hxi
      rwa [div_mul_cancel₀ _ hx0] at this
  have ha : a < 0 := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hneg
    apply hnj1
    apply hxInt_of _ j1 hj1
    have e : c j0 ^ b = (c j0 ^ b / (p : Ω) ^ a) * (p : Ω) ^ k := by
      rw [hk, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ hp0)]
    exact IsIntegral.of_pow hb (e ▸ hu.mul (isInt_natPow_p k))
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 ha.le)
  haveI := h.clo
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq ((p : Ω) ^ k) hb
  have hk1 : 1 ≤ k := by omega
  have hpa : (p : Ω) ^ a = ((p : Ω) ^ k)⁻¹ := by
    rw [← zpow_natCast, ← hk, zpow_neg, inv_inv]
  have hlx : (l * c j0) ^ b = c j0 ^ b / (p : Ω) ^ a := by
    rw [mul_pow, hl, hpa, div_inv_eq_mul, mul_comm]
  have hlxi : IsInt p (l * c j0) := IsIntegral.of_pow hb (hlx ▸ hu)
  refine ⟨l, ?_, ⟨b, hb, ?_⟩, ?_, j0, hj0n, ?_⟩
  · refine ⟨Polynomial.X ^ b - Polynomial.C ((p : ℤ_[p]) ^ k), Polynomial.X_pow_sub_C_ne_zero hb _, ?_⟩
    simp [hl]
  · rw [hl]
    have e : (p : Ω) ^ k / p = (p : Ω) ^ (k - 1) := by
      rw [div_eq_iff hp0, ← pow_succ, Nat.sub_add_cancel hk1]
    rw [e]
    exact isInt_natPow_p _
  · intro j hj
    by_cases hcj : c j = 0
    · rw [hcj, mul_zero]; exact isIntegral_zero
    · have e : (c j / c j0) * (l * c j0) = l * c j := by
        rw [mul_comm l (c j0), ← mul_assoc, div_mul_cancel₀ _ hx0, mul_comm]
      exact e ▸ (hdiv j hj hcj).mul hlxi
  · rintro ⟨m, hm, hsm⟩
    apply not_isInt_inv_p h
    have hz : l * c j0 ≠ 0 := by
      intro e0
      rw [e0, zero_pow hb.ne', eq_comm, div_eq_zero_iff] at hlx
      rcases hlx with h0 | h0
      · exact hx0 (pow_eq_zero_iff hb.ne' |>.1 h0)
      · exact zpow_ne_zero _ hp0 h0
    have hinv : (p : Ω) ^ a / c j0 ^ b = ((l * c j0) ^ b)⁻¹ := by rw [hlx, inv_div]
    rw [hinv] at hu'
    obtain ⟨b1, rfl⟩ : ∃ b1, b = b1 + 1 := ⟨b - 1, by omega⟩
    have e : ((p : Ω))⁻¹ = ((l * c j0) ^ m / p) ^ (b1 + 1) * (((l * c j0) ^ (b1 + 1))⁻¹) ^ m *
        (p : Ω) ^ b1 := by
      generalize l * c j0 = z at hz
      rw [div_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm (b1 + 1) m, pow_succ (p : Ω) b1]
      have hzz : z ^ (m * (b1 + 1)) ≠ 0 := pow_ne_zero _ hz
      have hpp : (p : Ω) ^ b1 ≠ 0 := pow_ne_zero _ hp0
      rw [div_mul_eq_mul_div, mul_inv_cancel₀ hzz, div_mul_eq_mul_div, one_mul, mul_comm _ (p : Ω),
        eq_div_iff (mul_ne_zero hp0 hpp), inv_mul_cancel_left₀ hp0]
    rw [e]
    exact ((hsm.pow _).mul (hu'.pow m)).mul (isInt_natPow_p b1)

end GlobalTheory.K5.Orth

namespace GlobalTheory.K5.Orth

theorem orth : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) →
    IsInt p (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) → ∀ j < p ^ N, IsInt p (c j) := by
  intro p _ Ω _ _ h T N c hfix hint
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨l, hlalg, ⟨m0, hm0, hlsm⟩, hlint, j0, hj0, hj0ns⟩ :=
    normalize h (GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit p Ω h) (p ^ N) c hne
  choose S hSalg hSmem using fun j => GlobalTheory.T.geometric_fixed_mem_closure_finite_algZp p Ω h (c j) (hfix j)
  let S' : Finset Ω := insert l ((Finset.range (p ^ N)).biUnion S)
  have hS'alg : ∀ s ∈ S', IsAlgZp p s := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact hlalg
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hs
      exact hSalg j s hj
  set E := Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S' : Set Ω)) with hE
  have hrange : Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) :=
    fun x hx => Subfield.subset_closure (Or.inl hx)
  have hlE : l ∈ E := Subfield.subset_closure (Or.inr (Finset.mem_insert_self _ _))
  have hcE : ∀ j < p ^ N, c j ∈ E := by
    intro j hj
    refine Subfield.closure_mono ?_ (hSmem j)
    apply Set.union_subset_union_right
    intro s hs
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, hs⟩)
  have hsum : (∑ j ∈ Finset.range (p ^ N), (l * c j) * T.qq N ^ j) =
      l * ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsmall : ∃ m : ℕ, 0 < m ∧
      IsInt p ((∑ j ∈ Finset.range (p ^ N), (l * c j) * T.qq N ^ j) ^ m / (p : Ω)) := by
    refine ⟨m0, hm0, ?_⟩
    rw [hsum, mul_pow, mul_div_right_comm]
    exact hlsm.mul (hint.pow m0)
  have := GlobalTheory.T.residue_tower_powers_linearIndependent p Ω h E hrange (GlobalTheory.T.towerParameter_not_pow_mod_maximalIdeal_adjoin_algebraic p Ω h S' hS'alg) T N (fun j => l * c j)
    (fun j hj => ⟨E.mul_mem hlE (hcE j hj), hlint j hj⟩) hsmall j0 hj0
  exact hj0ns this

end GlobalTheory.K5.Orth
end
