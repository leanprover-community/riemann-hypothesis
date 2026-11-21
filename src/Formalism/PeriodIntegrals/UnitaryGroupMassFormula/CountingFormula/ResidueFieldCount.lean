import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGFL

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Polynomial
open ValuativeRel

theorem fl_hensel {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    (hl : IsNonarchimedeanLocalField F) : HenselianRing 𝒪[F] 𝓂[F] := by
  haveI := hl
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  exact IsAdicComplete.henselianRing _ _

theorem fl_coe_mul {F : Type} [Field F] [ValuativeRel F] (a b : 𝒪[F]) :
    ((a * b : 𝒪[F]) : F) = (a : F) * b := rfl

theorem fl_sq_div {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (b n : 𝒪[F]) (hbn : b * b = n) (hn : n ∈ 𝓂[F]) :
    ∃ z ∈ L.O, algebraMap F E b = algebraMap F E ϖ * z := by
  haveI := hl
  have hb : b ∈ 𝓂[F] := by
    have h2 : b * b ∈ 𝓂[F] := hbn ▸ hn
    rcases (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).isPrime.mem_or_mem h2 with h | h <;> exact h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  exact ⟨algebraMap F E c, fl_int_mem L c, by rw [fl_coe_mul, map_mul]⟩

theorem fl_local {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (hinj : Function.Injective (algebraMap F E))
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    ∀ x ∈ L.O, (¬ ∃ z ∈ L.O, x = algebraMap F E ϖ * z) → ∃ y ∈ L.O, x * y = 1 := by
  intro x hx hnd
  haveI := hl
  obtain ⟨n, hn⟩ := fl_norm L hinj hx
  obtain ⟨t, ht⟩ := fl_trace L hinj hx
  have hquad : x * x = algebraMap F E t * x - algebraMap F E n := by
    rw [ht, hn]; ring
  by_cases hnu : IsUnit n
  · obtain ⟨u, rfl⟩ := hnu
    refine ⟨L.cj x * algebraMap F E ((↑u⁻¹ : 𝒪[F]) : F), mul_mem (fl_cj_mem L hx) (fl_int_mem L _), ?_⟩
    rw [← mul_assoc, ← hn, ← map_mul, ← fl_coe_mul, Units.mul_inv]
    simp
  · exfalso
    have hnm : n ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal n).2 hnu
    have hspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    by_cases htm : t ∈ 𝓂[F]
    · apply hnd
      rw [hspan, Ideal.mem_span_singleton] at htm hnm
      obtain ⟨t', rfl⟩ := htm
      obtain ⟨n', rfl⟩ := hnm
      have hsp : x * x ∈ Submodule.span L.O {algebraMap F E ϖ} := by
        refine Submodule.mem_span_singleton.2 ⟨⟨algebraMap F E t' * x - algebraMap F E n',
          sub_mem (mul_mem (fl_int_mem L t') hx) (fl_int_mem L n')⟩, ?_⟩
        rw [hquad, fl_coe_mul, fl_coe_mul, map_mul, map_mul]
        show (algebraMap F E t' * x - algebraMap F E n') * algebraMap F E ϖ = _
        ring
      obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 (L.unram ϖ hϖ x hx hsp)
      exact ⟨z, z.2, by rw [← hz, Subring.smul_def]; exact mul_comm _ _⟩
    · haveI := fl_hensel hl
      haveI := IsLocalRing.maximalIdeal.isMaximal 𝒪[F]
      let f : Polynomial 𝒪[F] := X ^ 2 + (C n - C t * X)
      have hf : f.Monic := by
        refine (monic_X_pow 2).add_of_left ?_
        rw [degree_X_pow]
        refine lt_of_le_of_lt (degree_sub_le _ _) ?_
        exact max_lt (lt_of_le_of_lt degree_C_le (by norm_num))
          (lt_of_le_of_lt (degree_C_mul_X_le t) (by norm_num))
      have h0 : f.eval 0 ∈ 𝓂[F] := by simpa [f] using hnm
      have h1 : IsUnit (Ideal.Quotient.mk 𝓂[F] (f.derivative.eval 0)) := by
        letI := Ideal.Quotient.field 𝓂[F]
        have hne : Ideal.Quotient.mk 𝓂[F] (f.derivative.eval 0) ≠ 0 := by
          rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
          simpa [f, Polynomial.derivative_sub, Polynomial.derivative_mul] using htm
        exact hne.isUnit
      obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian f hf 0 h0 h1
      have hroot : a ^ 2 + (n - t * a) = 0 := by simpa [f, Polynomial.IsRoot] using ha
      have hrootE : algebraMap F E (a : F) ^ 2 + (algebraMap F E (n : F) -
          algebraMap F E (t : F) * algebraMap F E (a : F)) = 0 := by
        have := congrArg (fun r : 𝒪[F] => algebraMap F E (r : F)) hroot
        simpa [map_sub, map_mul, map_pow, map_add] using this
      have hfac : (x - algebraMap F E (a : F)) * (x - (algebraMap F E (t : F) - algebraMap F E (a : F))) = 0 := by
        linear_combination hquad - hrootE
      have hxF : ∃ b : 𝒪[F], x = algebraMap F E (b : F) := by
        by_cases hxa : x - algebraMap F E (a : F) = 0
        · exact ⟨a, sub_eq_zero.1 hxa⟩
        · obtain ⟨u, hu⟩ := hE _ hxa
          have : x - (algebraMap F E (t : F) - algebraMap F E (a : F)) = 0 := by
            have h2 := congrArg (fun y => (↑u⁻¹ : E) * y) hfac
            simp only [mul_zero] at h2
            rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h2
            exact h2
          refine ⟨t - a, ?_⟩
          rw [sub_eq_zero.1 this]
          simp
      obtain ⟨b, rfl⟩ := hxF
      have hcj : L.cj (algebraMap F E (b : F)) = algebraMap F E (b : F) := L.cj.commutes _
      rw [hcj, ← map_mul, ← fl_coe_mul] at hn
      have hbn : b * b = n := Subtype.val_injective (hinj hn).symm
      exact hnd (fl_sq_div L hl ϖ hϖ b n hbn hnm)

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S
open ValuativeRel

theorem fl_inj {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) : Function.Injective (algebraMap F E) := by
  haveI : Nontrivial E := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h1 := L.rank
    have h2 := Module.finrank_zero_of_subsingleton (R := F) (M := E)
    omega
  exact (algebraMap F E).injective

theorem fl_norm_ne {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hE : ∀ x : E, x ≠ 0 → IsUnit x)
    {x : E} (hx0 : x ≠ 0) (n : 𝒪[F]) (hn : algebraMap F E n = x * L.cj x) : n ≠ 0 := by
  haveI : Nontrivial E := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h1 := L.rank
    have h2 := Module.finrank_zero_of_subsingleton (R := F) (M := E)
    omega
  intro hn0
  rw [hn0] at hn
  have hcj : L.cj x ≠ 0 := fun h => hx0 ((map_eq_zero_iff L.cj L.cj.injective).mp h)
  have hu : IsUnit (x * L.cj x) := (hE x hx0).mul (hE _ hcj)
  apply hu.ne_zero
  rw [← hn]
  simp

theorem fl_fact {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (hinj : Function.Injective (algebraMap F E))
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    ∀ x ∈ L.O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u := by
  haveI := hl
  have key : ∀ n : 𝒪[F], ∀ x ∈ L.O, x ≠ 0 → algebraMap F E n = x * L.cj x →
      ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u := by
    intro n
    refine WellFounded.induction (wellFounded_dvdNotUnit (α := 𝒪[F]))
      (C := fun n : 𝒪[F] => ∀ x ∈ L.O, x ≠ 0 → algebraMap F E n = x * L.cj x →
        ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u) n ?_
    intro n ih x hx hx0 hn
    by_cases hdiv : ∃ z ∈ L.O, x = algebraMap F E ϖ * z
    · obtain ⟨z, hz, rfl⟩ := hdiv
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp at hx0
      obtain ⟨n', hn'⟩ := fl_norm L hinj hz
      have hcj : L.cj (algebraMap F E ϖ) = algebraMap F E ϖ := L.cj.commutes _
      have heq : n = n' * (ϖ * ϖ) := by
        apply Subtype.ext
        apply hinj
        calc algebraMap F E (n : F) = algebraMap F E ϖ * z * L.cj (algebraMap F E ϖ * z) := hn
          _ = (z * L.cj z) * (algebraMap F E ϖ * algebraMap F E ϖ) := by rw [map_mul, hcj]; ring
          _ = algebraMap F E n' * (algebraMap F E ϖ * algebraMap F E ϖ) := by rw [hn']
          _ = algebraMap F E ((n' * (ϖ * ϖ) : 𝒪[F]) : F) := by
            rw [show ((n' * (ϖ * ϖ) : 𝒪[F]) : F) = (n' : F) * ((ϖ : F) * (ϖ : F)) from rfl, map_mul, map_mul]
      have hdvd : DvdNotUnit n' n := by
        refine ⟨fl_norm_ne L hE hz0 n' hn', ϖ * ϖ, ?_, heq⟩
        rw [IsUnit.mul_iff]
        exact fun h => hϖ.not_isUnit h.1
      obtain ⟨k, u, hu, hw, hzu⟩ := ih n' hdvd z hz hz0 hn'
      exact ⟨k + 1, u, hu, hw, by rw [hzu, pow_succ]; ring⟩
    · obtain ⟨y, hy, hxy⟩ := fl_local L hl hE hinj ϖ hϖ x hx hdiv
      exact ⟨0, x, hx, ⟨y, hy, hxy⟩, by simp⟩
  intro x hx hx0
  obtain ⟨n, hn⟩ := fl_norm L hinj hx
  exact key n x hx hx0 hn

theorem local_density_integral : FLocO := by
  intro F E _ _ _ _ _ _ L hl _ hE ϖ hϖ
  have hinj := fl_inj L
  exact ⟨fl_local L hl hE hinj ϖ hϖ, fl_den L, fl_fact L hl hE hinj ϖ hϖ⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S
open ValuativeRel

theorem fr_max {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    (Ideal.span {piO L ϖ}).IsMaximal := by
  have hinj := fl_inj L
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h1
    rw [Ideal.mem_span_singleton'] at h1
    obtain ⟨z, hz⟩ := h1
    have hz' : (z : E) * algebraMap F E ϖ = 1 := by
      have := congrArg Subtype.val hz
      simpa [piO] using this
    have hϖ0 : (ϖ : F) ≠ 0 := by
      intro h; apply hϖ.ne_zero; exact Subtype.ext h
    have hzF : (z : E) = algebraMap F E (ϖ : F)⁻¹ := by
      have h2 : algebraMap F E (ϖ : F) * algebraMap F E (ϖ : F)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hϖ0, map_one]
      calc (z : E) = (z : E) * (algebraMap F E ϖ * algebraMap F E (ϖ : F)⁻¹) := by rw [h2, mul_one]
        _ = algebraMap F E (ϖ : F)⁻¹ := by rw [← mul_assoc, hz', one_mul]
    have hmem : (ϖ : F)⁻¹ ∈ 𝒪[F] := fl_mem_int L hinj (hzF ▸ z.2)
    apply hϖ.not_isUnit
    have h3 : ϖ * ⟨_, hmem⟩ = 1 := Subtype.ext (by
      show (ϖ : F) * (ϖ : F)⁻¹ = 1
      exact mul_inv_cancel₀ hϖ0)
    exact ⟨⟨ϖ, ⟨_, hmem⟩, h3, by rw [mul_comm]; exact h3⟩, rfl⟩
  · intro J x hIJ hx hxJ
    have hnd : ¬ ∃ z ∈ L.O, (x : E) = algebraMap F E ϖ * z := by
      rintro ⟨z, hz, hxz⟩
      apply hx
      rw [Ideal.mem_span_singleton']
      exact ⟨⟨z, hz⟩, Subtype.ext (by simp [piO, hxz, mul_comm])⟩
    obtain ⟨y, hy, hxy⟩ := fl_local L hl hE hinj ϖ hϖ x x.2 hnd
    have : (1 : L.O) = x * ⟨y, hy⟩ := Subtype.ext (by simp [hxy])
    rw [this]
    exact J.mul_mem_right _ hxJ

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S
open ValuativeRel

theorem fr_ic_free {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hc : CharZero F) (hE : ∀ x : E, x ≠ 0 → IsUnit x) :
    Module.Free 𝒪[F] (integralClosure 𝒪[F] E) ∧ Module.Finite 𝒪[F] (integralClosure 𝒪[F] E) ∧
      Module.finrank 𝒪[F] (integralClosure 𝒪[F] E) = 2 := by
  haveI := hl
  haveI := hc
  have hnt : Nontrivial E := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have := L.rank
    rw [Module.finrank_zero_of_subsingleton] at this
    omega
  letI : Field E := (show IsField E from
    ⟨exists_pair_ne E, mul_comm, fun {x} hx => (hE x hx).exists_right_inv⟩).toField
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ L.rank
  haveI : Module.IsTorsionFree 𝒪[F] E := FaithfulSMul.to_isTorsionFree _ E
  refine ⟨IsIntegralClosure.module_free 𝒪[F] F E (integralClosure 𝒪[F] E),
    IsIntegralClosure.finite 𝒪[F] F E (integralClosure 𝒪[F] E), ?_⟩
  rw [IsIntegralClosure.rank 𝒪[F] F E (integralClosure 𝒪[F] E), L.rank]

theorem fr_card {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hc : CharZero F) (hE : ∀ x : E, x ≠ 0 → IsUnit x) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    Nat.card (L.O ⧸ Ideal.span {piO L ϖ}) = Nat.card 𝓀[F] ^ 2 := by
  classical
  haveI := hl
  obtain ⟨hfree, hfin, hrank⟩ := fr_ic_free L hl hc hE
  set A := integralClosure 𝒪[F] E with hA

  have hOA : L.O = A.toSubring := by
    ext x
    rw [L.O_def]
    rfl
  let e : L.O ≃+* A.toSubring := RingEquiv.subringCongr hOA

  let b : Module.Basis (Fin 2) 𝒪[F] A := (Module.finBasisOfFinrankEq 𝒪[F] A hrank)

  let πA : A := algebraMap 𝒪[F] A ϖ
  have hmemI : ∀ x : A, x ∈ (Ideal.span {πA} : Ideal A) ↔ ∃ y : A, x = ϖ • y := by
    intro x
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [Algebra.smul_def, mul_comm]⟩
  let I' : Submodule 𝒪[F] A := (Ideal.span {πA} : Ideal A).restrictScalars 𝒪[F]
  let P : Submodule 𝒪[F] (Fin 2 → 𝒪[F]) := Submodule.pi Set.univ fun _ => Ideal.span {ϖ}
  have hmap : I'.map (b.equivFun : A →ₗ[𝒪[F]] (Fin 2 → 𝒪[F])) = P := by
    ext v
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem, P, Submodule.mem_pi, Set.mem_univ,
      true_implies, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨x, hx, rfl⟩ i
      obtain ⟨y, rfl⟩ := (hmemI x).mp hx
      exact ⟨b.equivFun y i, by rw [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]⟩
    · intro h
      choose w hw using h
      refine ⟨ϖ • b.equivFun.symm w, (hmemI _).mpr ⟨_, rfl⟩, ?_⟩
      funext i
      rw [LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, ← hw i,
        mul_comm]
  have hmax : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  calc Nat.card (L.O ⧸ Ideal.span {piO L ϖ})
      = Nat.card (A.toSubring ⧸ Ideal.span {e (piO L ϖ)}) := by
        apply Nat.card_congr
        refine (Ideal.quotientEquiv _ _ e ?_).toEquiv
        rw [Ideal.map_span, Set.image_singleton]
        rfl
    _ = Nat.card (A ⧸ (Ideal.span {πA} : Ideal A)) := by
        rfl
    _ = Nat.card (A ⧸ I') := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv 𝒪[F] _).toEquiv.symm
    _ = Nat.card ((Fin 2 → 𝒪[F]) ⧸ P) := by
        apply Nat.card_congr
        rw [← hmap]
        exact (Submodule.Quotient.equiv I' _ b.equivFun rfl).toEquiv
    _ = Nat.card (Fin 2 → 𝒪[F] ⧸ Ideal.span {ϖ}) := Nat.card_congr (Submodule.quotientPi _).toEquiv
    _ = Nat.card (𝒪[F] ⧸ Ideal.span {ϖ}) ^ 2 := by
        rw [Nat.card_fun, Nat.card_fin]
    _ = Nat.card 𝓀[F] ^ 2 := by
        congr 1
        apply Nat.card_congr
        exact (Ideal.quotEquivOfEq hmax).toEquiv.symm

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S
open ValuativeRel

theorem fr_frob {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hc : CharZero F) (hE : ∀ x : E, x ≠ 0 → IsUnit x) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    ∀ x y : L.O, (y : E) = L.cj x →
      Ideal.Quotient.mk (Ideal.span {piO L ϖ}) y =
        Ideal.Quotient.mk (Ideal.span {piO L ϖ}) x ^ Nat.card 𝓀[F] := by
  have := hl
  have hinj := fl_inj L
  have hmax : 𝓂[F] = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hmaxI : (Ideal.span {piO L ϖ}).IsMaximal := fr_max L hl hE ϖ hϖ
  let I := Ideal.span {piO L ϖ}
  let : Field (L.O ⧸ I) := Ideal.Quotient.field I
  have hcard : Nat.card (L.O ⧸ I) = Nat.card 𝓀[F] ^ 2 := fr_card L hl hc hE ϖ hϖ
  have hq0 : 0 < Nat.card 𝓀[F] := Nat.card_pos
  have : Finite (L.O ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  let : Fintype (L.O ⧸ I) := Fintype.ofFinite _
  let : Fintype 𝓀[F] := Fintype.ofFinite _
  let ι0 : 𝒪[F] →+* L.O :=
    ((algebraMap F E).comp (valuation F).integer.subtype).codRestrict L.O (fun a => fl_int_mem L a)
  have hι0 : ∀ a : 𝒪[F], (ι0 a : E) = algebraMap F E a := fun _ => rfl
  let f0 : 𝒪[F] →+* (L.O ⧸ I) := (Ideal.Quotient.mk I).comp ι0
  have hf0ϖ : f0 ϖ = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.2
    have : ι0 ϖ = piO L ϖ := rfl
    rw [this]
    exact Ideal.subset_span rfl
  have : IsLocalHom f0 := ⟨fun a ha => by
    by_contra hna
    have ham : a ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal a).2 hna
    rw [hmax, Ideal.mem_span_singleton'] at ham
    obtain ⟨b, rfl⟩ := ham
    rw [map_mul, hf0ϖ, mul_zero] at ha
    exact not_isUnit_zero ha⟩
  let ρ : 𝓀[F] →+* (L.O ⧸ I) := IsLocalRing.ResidueField.lift f0
  let : Algebra 𝓀[F] (L.O ⧸ I) := ρ.toAlgebra
  have hρ : ∀ a : 𝒪[F], algebraMap 𝓀[F] (L.O ⧸ I) (IsLocalRing.residue 𝒪[F] a) = f0 a := fun _ => rfl
  let cjO : L.O ≃+* L.O :=
    { toFun := fun x => ⟨L.cj x, fl_cj_mem L x.2⟩
      invFun := fun x => ⟨L.cj x, fl_cj_mem L x.2⟩
      left_inv := fun x => Subtype.ext (L.cj_cj x)
      right_inv := fun x => Subtype.ext (L.cj_cj x)
      map_mul' := fun x y => Subtype.ext (map_mul L.cj (x : E) (y : E))
      map_add' := fun x y => Subtype.ext (map_add L.cj (x : E) (y : E)) }
  have hcjι : ∀ a : 𝒪[F], cjO (ι0 a) = ι0 a := fun a => Subtype.ext (AlgEquiv.commutes L.cj _)
  have hIcj : I = I.map (cjO : L.O →+* L.O) := by
    show Ideal.span {piO L ϖ} = (Ideal.span {piO L ϖ}).map (cjO : L.O →+* L.O)
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (hcjι ϖ).symm
  let σ0 : (L.O ⧸ I) ≃+* (L.O ⧸ I) := Ideal.quotientEquiv I I cjO hIcj
  have hσ0 : ∀ x : L.O, σ0 (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (cjO x) := fun _ => rfl
  let σ : (L.O ⧸ I) ≃ₐ[𝓀[F]] (L.O ⧸ I) := AlgEquiv.ofRingEquiv (f := σ0) (fun a => by
    obtain ⟨a', rfl⟩ := IsLocalRing.residue_surjective a
    rw [hρ]
    show σ0 (Ideal.Quotient.mk I (ι0 a')) = Ideal.Quotient.mk I (ι0 a')
    rw [hσ0, hcjι])
  have hσ : ∀ x : L.O, σ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (cjO x) := fun _ => rfl
  let Fr := FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F] (L.O ⧸ I)
  have hFr : ∀ z, Fr z = z ^ Fintype.card 𝓀[F] := fun _ => rfl
  have hkey : ∀ z, (Fr z - z) * (Fr z - σ z) = 0 := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨t, ht⟩ := fl_trace L hinj x.2
    obtain ⟨n, hn⟩ := fl_norm L hinj x.2
    have hT : Ideal.Quotient.mk I x + σ (Ideal.Quotient.mk I x) =
        algebraMap 𝓀[F] (L.O ⧸ I) (IsLocalRing.residue 𝒪[F] t) := by
      rw [hσ, ← map_add, hρ]
      show _ = Ideal.Quotient.mk I (ι0 t)
      congr 1
      exact Subtype.ext (by rw [hι0, ht]; rfl)
    have hN : Ideal.Quotient.mk I x * σ (Ideal.Quotient.mk I x) =
        algebraMap 𝓀[F] (L.O ⧸ I) (IsLocalRing.residue 𝒪[F] n) := by
      rw [hσ, ← map_mul, hρ]
      show _ = Ideal.Quotient.mk I (ι0 n)
      congr 1
      exact Subtype.ext (by rw [hι0, hn]; rfl)
    have h0 : Ideal.Quotient.mk I x ^ 2 - algebraMap 𝓀[F] (L.O ⧸ I) (IsLocalRing.residue 𝒪[F] t) *
        Ideal.Quotient.mk I x + algebraMap 𝓀[F] (L.O ⧸ I) (IsLocalRing.residue 𝒪[F] n) = 0 := by
      rw [← hT, ← hN]; ring
    have h1 := congrArg Fr h0
    rw [map_add, map_sub, map_pow, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, map_zero,
      ← hT, ← hN] at h1
    linear_combination h1
  have hq1 : 1 < Fintype.card 𝓀[F] := Fintype.one_lt_card
  have hfr : Module.finrank 𝓀[F] (L.O ⧸ I) = 2 := by
    have h := Module.card_eq_pow_finrank (K := 𝓀[F]) (V := L.O ⧸ I)
    rw [Fintype.card_eq_nat_card, hcard, Fintype.card_eq_nat_card] at h
    rw [← Fintype.card_eq_nat_card] at h
    exact (Nat.pow_right_injective hq1 h).symm
  have hσFr : σ = Fr := by
    obtain ⟨m, hm⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow 𝓀[F] (L.O ⧸ I)).2 σ
    have hm2 : m.1 < 2 := hfr ▸ m.2
    rcases (by omega : m.1 = 0 ∨ m.1 = 1) with h | h
    · exfalso
      have hs1 : σ = 1 := by rw [← hm]; simp only [h, pow_zero]
      have hF1 : Fr = 1 := by
        ext z
        have := hkey z
        rw [hs1, AlgEquiv.one_apply, mul_self_eq_zero, sub_eq_zero] at this
        exact this
      have ho := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic 𝓀[F] (L.O ⧸ I)
      rw [show FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F] (L.O ⧸ I) = 1 from hF1, orderOf_one,
        hfr] at ho
      omega
    · rw [← hm]; simp only [h, pow_one]; rfl
  intro x y hxy
  have hy : y = cjO x := Subtype.ext hxy
  rw [hy, ← hσ x, hσFr, hFr, Fintype.card_eq_nat_card]

theorem residue_field_count : FResField := by
  intro F E _ _ _ _ _ _ L hl hc hE ϖ hϖ
  exact ⟨fr_max L hl hE ϖ hϖ, fr_card L hl hc hE ϖ hϖ, fr_frob L hl hc hE ϖ hϖ⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end
