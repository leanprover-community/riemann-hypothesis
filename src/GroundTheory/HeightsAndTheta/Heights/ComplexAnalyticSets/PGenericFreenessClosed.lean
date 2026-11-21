import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFreeness
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericNoetherNormalisation
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumRMulNe
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProofSimp

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace GenericFreeness

open Module

universe u

variable {A : Type u} [CommRing A]

def IsGenericallyFree (A : Type u) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
  ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)

theorem free_iff_of_isLocalizedModule (f : A) {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers f) g]
    (Rf : Type*) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf] [Module Rf N]
    [IsScalarTower A Rf N] :
    Module.Free Rf N ↔ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  let e₁ : Localization.Away f ≃+* Rf :=
    (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) Rf).toRingEquiv
  let e₂ : LocalizedModule (Submonoid.powers f) M ≃ₗ[A] N := IsLocalizedModule.iso _ g
  have key : ∀ (r : Localization.Away f) (x : LocalizedModule (Submonoid.powers f) M),
      e₂ (r • x) = e₁ r • e₂ x := by
    intro r x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) r
    have hs := IsLocalizedModule.map_units g s
    rw [Module.End.isUnit_iff] at hs
    apply hs.1
    simp only [Module.algebraMap_end_apply]
    have h1 : (s : A) • IsLocalization.mk' (Localization.Away f) a s = algebraMap A _ a := by
      rw [Algebra.smul_def, IsLocalization.mk'_spec']
    have h2 : (s : A) • e₁ (IsLocalization.mk' (Localization.Away f) a s) = algebraMap A Rf a := by
      have : e₁ (IsLocalization.mk' (Localization.Away f) a s) = IsLocalization.mk' Rf a s :=
        IsLocalization.algEquiv_mk' _ _
      rw [this, Algebra.smul_def, IsLocalization.mk'_spec']
    rw [← map_smul, ← smul_assoc, h1, algebraMap_smul, ← smul_assoc, h2, algebraMap_smul, map_smul]
  haveI := RingHomInvPair.of_ringEquiv e₁
  haveI := RingHomInvPair.of_ringEquiv_symm e₁
  let e : LinearEquiv (e₁ : Localization.Away f →+* Rf) (LocalizedModule (Submonoid.powers f) M) N :=
    { e₂.toAddEquiv with map_smul' := fun r x ↦ key r x }
  exact (Module.Free.iff_of_equiv e).symm

theorem isLocalizedModule_powers_mul (a c : A) {M N P : Type*} [AddCommGroup M] [Module A M]
    {Ra : Type*} [CommRing Ra] [Algebra A Ra] [IsLocalization.Away a Ra]
    [AddCommGroup N] [Module A N] [Module Ra N] [IsScalarTower A Ra N]
    [AddCommGroup P] [Module A P] [Module Ra P] [IsScalarTower A Ra P]
    (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers a) g]
    (h : N →ₗ[Ra] P) [IsLocalizedModule (Submonoid.powers (algebraMap A Ra c)) h] :
    IsLocalizedModule (Submonoid.powers (a * c)) (h.restrictScalars A ∘ₗ g) := by
  have hh : IsLocalizedModule (Submonoid.powers c) (h.restrictScalars A) :=
    IsLocalizedModule.restrictScalars_powers c h
  have ha : IsUnit (algebraMap A (Module.End A P) a) := by
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := Ra) a
    rw [Module.End.isUnit_iff]
    have hb : Function.Bijective (fun p : P ↦ (u : Ra) • p) := by
      refine ⟨fun p q hpq ↦ ?_, fun p ↦ ⟨(↑u⁻¹ : Ra) • p, ?_⟩⟩
      · have := congr_arg (fun x : P ↦ (↑u⁻¹ : Ra) • x) hpq
        simpa only [smul_smul, Units.inv_mul, one_smul] using this
      · show (u : Ra) • ((↑u⁻¹ : Ra) • p) = p
        rw [smul_smul, Units.mul_inv, one_smul]
    convert hb using 1
    funext p
    simp [hu]
  have hc : IsUnit (algebraMap A (Module.End A P) c) :=
    hh.map_units ⟨c, Submonoid.mem_powers c⟩
  constructor
  · rintro ⟨_, k, rfl⟩
    show IsUnit (algebraMap A (Module.End A P) ((a * c) ^ k))
    rw [map_pow, map_mul]
    exact (ha.mul hc).pow k
  · intro y
    obtain ⟨⟨n, ⟨_, j, rfl⟩⟩, hn⟩ := hh.surj y
    obtain ⟨⟨m, ⟨_, i, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers a) g n
    refine ⟨⟨(a ^ j * c ^ i) • m, ⟨(a * c) ^ (i + j), i + j, rfl⟩⟩, ?_⟩
    simp only [Submonoid.smul_def] at hn hm ⊢
    have e1 : (h.restrictScalars A ∘ₗ g) ((a ^ j * c ^ i) • m) =
        (a ^ j * c ^ i * a ^ i) • (h.restrictScalars A) n := by
      rw [LinearMap.comp_apply, map_smul, ← hm, map_smul, map_smul, smul_smul]
    rw [e1, ← hn, smul_smul]
    congr 1
    ring
  · intro m₁ m₂ e
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := hh.exists_of_eq e
    simp only [Submonoid.smul_def] at hj
    rw [← map_smul, ← map_smul] at hj
    obtain ⟨⟨_, i, rfl⟩, hi⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers a) (f := g) hj
    refine ⟨⟨(a * c) ^ (i + j), i + j, rfl⟩, ?_⟩
    simp only [Submonoid.smul_def] at hi ⊢
    have : (a * c) ^ (i + j) = a ^ j * c ^ i * (a ^ i * c ^ j) := by ring
    rw [this]
    simp only [mul_smul (a ^ j * c ^ i), mul_smul (a ^ i) (c ^ j), hi]

theorem free_away_mul {f : A} (g : A) {M : Type*} [AddCommGroup M] [Module A M]
    (hf : Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) :
    Module.Free (Localization.Away (f * g)) (LocalizedModule (Submonoid.powers (f * g)) M) := by
  let Ra := Localization.Away f
  let N := LocalizedModule (Submonoid.powers f) M
  let T := Localization.Away (algebraMap A Ra g)
  let P := LocalizedModule (Submonoid.powers (algebraMap A Ra g)) N
  have hP : Module.Free T P :=
    Module.free_of_isLocalizedModule (Submonoid.powers (algebraMap A Ra g))
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A Ra g)) N)
  haveI := isLocalizedModule_powers_mul f g (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A Ra g)) N)
  exact (free_iff_of_isLocalizedModule (f * g)
    ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap A Ra g)) N).restrictScalars A ∘ₗ
      LocalizedModule.mkLinearMap (Submonoid.powers f) M) T).1 hP

theorem IsGenericallyFree.of_linearEquiv {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M']
    [Module A M'] (e : M ≃ₗ[A] M') (hM : IsGenericallyFree A M) : IsGenericallyFree A M' := by
  obtain ⟨f, hf, hfree⟩ := hM
  refine ⟨f, hf, ?_⟩
  exact (free_iff_of_isLocalizedModule f
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M ∘ₗ e.symm.toLinearMap) (Localization.Away f)).1 hfree

theorem isGenericallyFree_of_smul_eq_zero {M : Type*} [AddCommGroup M] [Module A M] (a : A) (ha : a ≠ 0)
    (h : ∀ m : M, a • m = 0) : IsGenericallyFree A M := by
  refine ⟨a, ha, ?_⟩
  have h0 : ∀ x : LocalizedModule (Submonoid.powers a) M, x = 0 := fun x ↦ by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      exact LocalizedModule.eq_zero_of_smul_eq_zero a (Submonoid.mem_powers a) _
        (by rw [LocalizedModule.smul'_mk, h, LocalizedModule.zero_mk])
  haveI : Subsingleton (LocalizedModule (Submonoid.powers a) M) := ⟨fun x y ↦ by rw [h0 x, h0 y]⟩
  infer_instance

theorem isGenericallyFree_of_free [Nontrivial A] {M : Type*} [AddCommGroup M] [Module A M] [Module.Free A M] :
    IsGenericallyFree A M :=
  ⟨1, one_ne_zero, Module.free_of_isLocalizedModule (Submonoid.powers (1 : A))
    (LocalizedModule.mkLinearMap (Submonoid.powers (1 : A)) M)⟩

theorem IsGenericallyFree.of_injective [IsDomain A] {N M : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M]
    [Module A M] (i : N →ₗ[A] M) (hi : Function.Injective i) (a : A) (ha : a ≠ 0)
    (hsat : ∀ m : M, ∃ k : ℕ, a ^ k • m ∈ LinearMap.range i) (hN : IsGenericallyFree A N) :
    IsGenericallyFree A M := by
  obtain ⟨f, hf, hfree⟩ := hN
  have hfree' := free_away_mul a hfree
  set F := f * a with hF
  refine ⟨F, mul_ne_zero hf ha, ?_⟩
  haveI : IsLocalizedModule (Submonoid.powers F) (LocalizedModule.mkLinearMap (Submonoid.powers F) M ∘ₗ i) := by
    constructor
    · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers F) M)
    · intro y
      obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj (Submonoid.powers F)
        (LocalizedModule.mkLinearMap (Submonoid.powers F) M) y
      obtain ⟨k, n, hn⟩ := hsat m
      refine ⟨⟨f ^ k • n, ⟨F ^ k, k, rfl⟩ * s⟩, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, LinearMap.coe_comp, Function.comp_apply,
        map_smul, hn] at hms ⊢
      rw [mul_smul, hms, ← map_smul, smul_smul, hF, mul_pow]
      exact map_smul _ _ _
    · intro n₁ n₂ e
      obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers F)
        (f := LocalizedModule.mkLinearMap (Submonoid.powers F) M) e
      refine ⟨c, hi ?_⟩
      simpa only [Submonoid.smul_def, map_smul] using hc
  exact (free_iff_of_isLocalizedModule F
    (LocalizedModule.mkLinearMap (Submonoid.powers F) M ∘ₗ i) (Localization.Away F)).2 hfree'

theorem IsGenericallyFree.of_exact [IsDomain A] {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃] (i : N₁ →ₗ[A] N₂) (p : N₂ →ₗ[A] N₃)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (h₁ : IsGenericallyFree A N₁) (h₃ : IsGenericallyFree A N₃) : IsGenericallyFree A N₂ := by
  obtain ⟨f₁, hf₁, hfree₁⟩ := h₁
  obtain ⟨f₃, hf₃, hfree₃⟩ := h₃
  have free₁ := free_away_mul f₃ hfree₁
  have free₃ := free_away_mul f₁ hfree₃
  rw [mul_comm f₃ f₁] at free₃
  set f := f₁ * f₃
  refine ⟨f, mul_ne_zero hf₁ hf₃, ?_⟩
  let S := Submonoid.powers f
  let iL : LocalizedModule S N₁ →ₗ[Localization.Away f] LocalizedModule S N₂ :=
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N₁) (LocalizedModule.mkLinearMap S N₂) i).extendScalarsOfIsLocalization S (Localization.Away f)
  let pL : LocalizedModule S N₂ →ₗ[Localization.Away f] LocalizedModule S N₃ :=
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N₂) (LocalizedModule.mkLinearMap S N₃) p).extendScalarsOfIsLocalization S (Localization.Away f)
  have ex : Function.Exact iL pL := LocalizedModule.map_exact S i p hex
  have hiL : Function.Injective iL := IsLocalizedModule.map_injective S _ _ i hi
  have hpL : Function.Surjective pL := IsLocalizedModule.map_surjective S _ _ p hp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property pL LinearMap.id hpL
  exact Module.Free.of_equiv (ex.splitSurjectiveEquiv hiL ⟨s, hs⟩).1.symm

end GenericFreeness

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

universe u v w

namespace GenericFreeness

theorem isGenericallyFree_of_primes {A : Type u} [CommRing A] [IsDomain A] {R : Type u} [CommRing R]
    [IsNoetherianRing R] [Algebra A R] (hq : ∀ p : PrimeSpectrum R, IsGenericallyFree A (R ⧸ p.asIdeal))
    (M : Type w) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] [Module.Finite R M] :
    IsGenericallyFree A M := by
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R (M := M) inferInstance
    (motive := fun N _ _ _ ↦ ∀ (_ : Module A N) (_ : IsScalarTower A R N), IsGenericallyFree A N)
    ?_ ?_ ?_ ‹Module A M› ‹IsScalarTower A R M›
  · intro N _ _ _ _ _ _
    exact ⟨1, one_ne_zero, inferInstance⟩
  · intro N _ _ _ p e _ _
    exact (hq p).of_linearEquiv (e.restrictScalars A).symm
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ _ _
    letI : Module A N₁ := Module.compHom N₁ (algebraMap A R)
    letI : Module A N₃ := Module.compHom N₃ (algebraMap A R)
    have t₁ : IsScalarTower A R N₁ := ⟨fun a r n ↦ by
      show (a • r) • n = algebraMap A R a • r • n
      rw [Algebra.smul_def, mul_smul]⟩
    have t₃ : IsScalarTower A R N₃ := ⟨fun a r n ↦ by
      show (a • r) • n = algebraMap A R a • r • n
      rw [Algebra.smul_def, mul_smul]⟩
    exact IsGenericallyFree.of_exact (f.restrictScalars A) (g.restrictScalars A) hf hg hfg
      (h₁ inferInstance t₁) (h₃ inferInstance t₃)

theorem isGenericallyFree_of_comap_ne_bot {A : Type u} [CommRing A] {σ : Type*} (q : Ideal (MvPolynomial σ A))
    (h : q.comap (C : A →+* MvPolynomial σ A) ≠ ⊥) : IsGenericallyFree A (MvPolynomial σ A ⧸ q) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine isGenericallyFree_of_smul_eq_zero a ha0 fun d ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  have e : a • Ideal.Quotient.mk q x = Ideal.Quotient.mk q (a • x) :=
    (map_smul (Ideal.Quotient.mkₐ A q) a x).symm
  rw [e, Ideal.Quotient.eq_zero_iff_mem, smul_eq_C_mul]
  exact q.mul_mem_right x ha

theorem isGenericallyFree_quotient_bot {A : Type u} [CommRing A] [IsDomain A] (σ : Type*) :
    IsGenericallyFree A (MvPolynomial σ A ⧸ (⊥ : Ideal (MvPolynomial σ A))) :=
  (isGenericallyFree_of_free (M := MvPolynomial σ A)).of_linearEquiv
    (AlgEquiv.quotientBot A (MvPolynomial σ A)).toLinearEquiv.symm

theorem isGenericallyFree_quotient (hNN : GenericNoetherNormalisation.Statement.{u}) (n : ℕ) :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (q : Ideal (MvPolynomial (Fin n) A)),
      q.IsPrime → IsGenericallyFree A (MvPolynomial (Fin n) A ⧸ q) := by
  induction n with
  | zero =>
    intro A _ _ _ q _
    by_cases hc : q.comap (C : A →+* MvPolynomial (Fin 0) A) = ⊥
    · have hq : q = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' : C (coeff 0 x) ∈ q := by rwa [← eq_C_of_isEmpty x]
        have : coeff 0 x ∈ q.comap (C : A →+* MvPolynomial (Fin 0) A) := hx'
        rw [hc, Ideal.mem_bot] at this
        rw [Ideal.mem_bot, eq_C_of_isEmpty x, this, map_zero]
      subst hq
      exact isGenericallyFree_quotient_bot _
    · exact isGenericallyFree_of_comap_ne_bot q hc
  | succ n ih =>
    intro A _ _ _ q hqp
    by_cases hc : q.comap (C : A →+* MvPolynomial (Fin (n + 1)) A) = ⊥
    · by_cases hq : q = ⊥
      · subst hq
        exact isGenericallyFree_quotient_bot _
      obtain ⟨a, ha, z, s, hspan⟩ := hNN A n q hqp hq hc
      let D := MvPolynomial (Fin (n + 1)) A ⧸ q
      let Rn := MvPolynomial (Fin n) A
      letI : Algebra Rn D := (aeval z : Rn →ₐ[A] D).toRingHom.toAlgebra
      have : IsScalarTower A Rn D := IsScalarTower.of_algebraMap_eq fun x ↦ ((aeval z).commutes x).symm
      let N : Submodule Rn D := Submodule.span Rn (s : Set D)
      have hN : IsGenericallyFree A N :=
        isGenericallyFree_of_primes (R := Rn) (fun p ↦ ih A p.asIdeal p.isPrime) N
      refine hN.of_injective (N.subtype.restrictScalars A) Subtype.val_injective a ha fun d ↦ ?_
      obtain ⟨k, c, hk⟩ := hspan d
      refine ⟨k, ⟨⟨a ^ k • d, ?_⟩, rfl⟩⟩
      rw [hk]
      exact Submodule.sum_mem _ fun t ht ↦ Submodule.smul_mem _ (c t) (Submodule.subset_span ht)
    · exact isGenericallyFree_of_comap_ne_bot q hc

end GenericFreeness

theorem GenericFreeness.proof (hNN : GenericNoetherNormalisation.Statement.{u}) :
    GenericFreeness.Statement.{u, v, w} := by
  intro A _ _ _ B _ _ _ M _ _ _ _ _
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType A B›
  letI : Algebra (MvPolynomial (Fin n) A) B := g.toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin n) A) M := Module.compHom M (algebraMap (MvPolynomial (Fin n) A) B)
  have : IsScalarTower (MvPolynomial (Fin n) A) B M := ⟨fun x b m ↦ by
    show (g x * b) • m = g x • b • m
    rw [mul_smul]⟩
  have : IsScalarTower A (MvPolynomial (Fin n) A) M := ⟨fun a x m ↦ by
    show g (a • x) • m = a • g x • m
    rw [map_smul, smul_assoc]⟩
  have : Module.Finite (MvPolynomial (Fin n) A) B := RingHom.Finite.of_surjective g.toRingHom hg
  have : Module.Finite (MvPolynomial (Fin n) A) M := Module.Finite.trans B M
  exact GenericFreeness.isGenericallyFree_of_primes (R := MvPolynomial (Fin n) A)
    (fun p ↦ GenericFreeness.isGenericallyFree_quotient hNN n A p.asIdeal p.isPrime) M

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Polynomial MvPolynomial Ideal Nat RingHom List

namespace GenericNoetherNormalisation

section Nagata

variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) A)
variable (v w : Fin (n + 1) →₀ ℕ)

local notation3 "up" => 2 + f.totalDegree

local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

noncomputable abbrev nagata (c : A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

omit [IsDomain A] in
theorem nagata_comp_neg (c : A) : (nagata f c).comp (nagata f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

noncomputable abbrev nagataEquiv := AlgEquiv.ofAlgHom (nagata f 1) (nagata f (-1))
  (nagata_comp_neg f 1) (by simpa using nagata_comp_neg f (-1))

omit [IsDomain A] in
variable {f v} in
theorem lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

theorem sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x :=
  by apply _root_.UpperTheory.Reformulated.B.Qn10.sum_r_mul_ne <;> assumption





end Nagata

section Combination

variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {m : ℕ}

def CombAfterPower (c : A) (z : Fin m → D) (s : Finset D) (d : D) : Prop :=
  ∃ (k : ℕ) (cf : D → MvPolynomial (Fin m) A), c ^ k • d = ∑ t ∈ s, aeval z (cf t) * t

variable {c : A} {z : Fin m → D} {s : Finset D}

theorem smul_sum_aeval (b : A) (cf : D → MvPolynomial (Fin m) A) :
    b • ∑ t ∈ s, aeval z (cf t) * t = ∑ t ∈ s, aeval z (MvPolynomial.C b * cf t) * t := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_mul, MvPolynomial.aeval_C, Algebra.smul_def, mul_assoc]

theorem CombAfterPower.zero : CombAfterPower c z s 0 :=
  ⟨0, fun _ ↦ 0, by simp⟩

theorem CombAfterPower.add {d e : D} (hd : CombAfterPower c z s d) (he : CombAfterPower c z s e) :
    CombAfterPower c z s (d + e) := by
  obtain ⟨k, f, hf⟩ := hd
  obtain ⟨l, g, hg⟩ := he
  refine ⟨k + l, fun t ↦ MvPolynomial.C (c ^ l) * f t + MvPolynomial.C (c ^ k) * g t, ?_⟩
  have h1 : c ^ (k + l) • d = c ^ l • (c ^ k • d) := by rw [smul_smul, ← pow_add, add_comm]
  have h2 : c ^ (k + l) • e = c ^ k • (c ^ l • e) := by rw [smul_smul, ← pow_add]
  rw [smul_add, h1, h2, hf, hg, smul_sum_aeval, smul_sum_aeval, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_add, add_mul]

theorem CombAfterPower.mul_left (P : MvPolynomial (Fin m) A) {d : D} (hd : CombAfterPower c z s d) :
    CombAfterPower c z s (aeval z P * d) := by
  obtain ⟨k, f, hf⟩ := hd
  refine ⟨k, fun t ↦ P * f t, ?_⟩
  rw [← mul_smul_comm, hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [map_mul, mul_assoc]

theorem CombAfterPower.sum {ι : Type*} (u : Finset ι) (F : ι → D)
    (h : ∀ i ∈ u, CombAfterPower c z s (F i)) : CombAfterPower c z s (∑ i ∈ u, F i) :=
  Finset.sum_induction _ _ (fun _ _ ↦ CombAfterPower.add) CombAfterPower.zero h

theorem CombAfterPower.of_smul {d : D} (h : CombAfterPower c z s (c • d)) :
    CombAfterPower c z s d := by
  obtain ⟨k, f, hf⟩ := h
  exact ⟨k + 1, f, by rw [pow_succ, mul_smul, hf]⟩

theorem CombAfterPower.of_mem {t : D} (ht : t ∈ s) : CombAfterPower c z s t := by
  classical
  refine ⟨0, fun u ↦ if u = t then 1 else 0, ?_⟩
  rw [pow_zero, one_smul, Finset.sum_eq_single t (fun b _ hb ↦ by simp [hb]) (fun h ↦ absurd ht h)]
  simp


end Combination

theorem algHom_eq_eval₂_finSuccEquiv {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {n : ℕ}
    (ψ : MvPolynomial (Fin (n + 1)) A →ₐ[A] D) (P : MvPolynomial (Fin (n + 1)) A) :
    ψ P = (finSuccEquiv A n P).eval₂
      (MvPolynomial.aeval (R := A) (fun i : Fin n ↦ ψ (X i.succ))).toRingHom (ψ (X 0)) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add P Q hP hQ => rw [map_add, map_add, Polynomial.eval₂_add, hP, hQ]
  | mul_X P i ih =>
    rw [map_mul, map_mul, Polynomial.eval₂_mul, ih]
    congr 1
    cases i using Fin.cases <;> simp [finSuccEquiv_X_zero, finSuccEquiv_X_succ]

universe u

theorem proof : GenericNoetherNormalisation.Statement.{u} :=
  _root_.UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof

end GenericNoetherNormalisation

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v w

theorem GenericFreeness.full : GenericFreeness.Statement.{u, v, w} :=
  GenericFreeness.proof GenericNoetherNormalisation.proof

end GroundTheory.Heights₂.Heights
end
