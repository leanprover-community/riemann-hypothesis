import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCAtState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeReadingEigenvaluePlaceStatement

section
namespace GlobalTheory.SmulMemSpanIntegers

theorem exists_smul_mem_span_integers {Ks : Type} [Field Ks] [NumberField Ks] {WL : Type}
    [AddCommGroup WL] [Module Ks WL] [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {T : Set WL} {g : WL}
    (hg : g ∈ Submodule.span Ks T) :
    ∃ d : NumberField.RingOfIntegers Ks, d ≠ 0 ∧
      d • g ∈ Submodule.span (NumberField.RingOfIntegers Ks) T := by

  induction hg using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨d₁, hd₁, h₁⟩ := ihx
    obtain ⟨d₂, hd₂, h₂⟩ := ihy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (x + y) = d₂ • (d₁ • x) + d₁ • (d₂ • y) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm d₁ d₂ x]
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  | smul c x _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers Ks) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap (NumberField.RingOfIntegers Ks) Ks b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ Ks)).2 hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have e : b • ((algebraMap (NumberField.RingOfIntegers Ks) Ks a /
        algebraMap (NumberField.RingOfIntegers Ks) Ks b) • x) = a • x := by
      rw [← smul_assoc, Algebra.smul_def, mul_div_cancel₀ _ hbK, algebraMap_smul]
    rw [mul_comm, mul_smul, e, smul_comm]
    exact Submodule.smul_mem _ _ h

end GlobalTheory.SmulMemSpanIntegers
end

section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SupPowNorm

open Formalism.IndefR.Arith

section Clear

variable {Ks : Type} [Field Ks] [NumberField Ks] {WL : Type} [AddCommGroup WL] [Module Ks WL] [Module (𝓞 Ks) WL]
  [IsScalarTower (𝓞 Ks) Ks WL]

theorem exists_smul_mem_span_int {T : Set WL} {g : WL} (hg : g ∈ Submodule.span Ks T) :
    ∃ d : 𝓞 Ks, d ≠ 0 ∧ d • g ∈ Submodule.span (𝓞 Ks) T := by
  first
  | exact @_root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers
  | exact _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers
  | (apply _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers ..)

end Clear

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] (A : FormsL LL Ks WL W G)

theorem exists_pow_smul_mem_MK (hL : WL →ₗ[LL] WL) (T : Finset WL) (hT : ∀ x ∈ T, x ∈ A.MK)
    (hspan : ∀ x ∈ A.WK, x ∈ Submodule.span Ks (T : Set WL)) (hW : ∀ x ∈ A.WK, hL x ∈ A.WK)
    {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hsup : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∉ la.asIdeal → ∀ (f : WL) (hf : f ∈ A.WK),
      (∀ y, A.nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, A.nrm la y ⟨hL f, hW f hf⟩ ≤ 1)
    {t : WL} (ht : t ∈ A.MK) : ∃ n : ℕ, ∀ m, n ≤ m → N ^ m • hL t ∈ A.MK := by
  obtain ⟨htW, htb⟩ := ht
  have hg := hW t htW
  obtain ⟨d, hd, hdg⟩ := exists_smul_mem_span_int (hspan _ hg)
  have hdM : d • hL t ∈ A.MK := (Submodule.span_le.2 fun x hx => hT x hx) hdg
  have hb : ∀ la y, FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) * A.nrm la y ⟨hL t, hg⟩ ≤ 1 := by
    intro la y
    obtain ⟨h1, h2⟩ := hdM
    have := h2 la y
    have e : (⟨d • hL t, h1⟩ : A.WK) = (algebraMap (𝓞 Ks) Ks d) • ⟨hL t, hg⟩ :=
      Subtype.ext (algebraMap_smul Ks d (hL t)).symm
    rwa [e, A.nrm_smul] at this
  have hfin : {la : HeightOneSpectrum (𝓞 Ks) | la.asIdeal ∣ Ideal.span {(p : 𝓞 Ks)}}.Finite := by
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hex : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∈ la.asIdeal →
      ∃ n : ℕ, FinitePlace.mk la (N : Ks) ^ n ≤ FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) := by
    intro la hla
    have hNla : (N : 𝓞 Ks) ∈ la.asIdeal := by
      obtain ⟨k, rfl⟩ := hpN
      push_cast
      exact la.asIdeal.mul_mem_right _ hla
    have h1 : FinitePlace.mk la (N : Ks) < 1 := by
      rw [FinitePlace.mk_apply]
      have := (FinitePlace.norm_lt_one_iff_mem Ks la (N : 𝓞 Ks)).2 hNla
      simpa using this
    have h2 : 0 < FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) := FinitePlace.pos_iff.2 (by simpa using hd)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h2 h1
    exact ⟨n, hn.le⟩
  classical
  choose! nf hnf using hex
  refine ⟨hfin.toFinset.sup nf, fun m hm => ?_⟩
  have hmW : N ^ m • hL t ∈ A.WK := by
    rw [← Nat.cast_smul_eq_nsmul Ks]
    exact A.WK.smul_mem _ hg
  refine ⟨hmW, fun la y => ?_⟩
  have e : (⟨N ^ m • hL t, hmW⟩ : A.WK) = ((N : Ks) ^ m) • ⟨hL t, hg⟩ :=
    Subtype.ext (by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; rfl)
  rw [e, A.nrm_smul, map_pow]
  have hN1 : FinitePlace.mk la (N : Ks) ≤ 1 := by
    rw [FinitePlace.mk_apply]
    simpa using FinitePlace.norm_le_one Ks la (N : 𝓞 Ks)
  have hN0 : 0 ≤ FinitePlace.mk la (N : Ks) := by positivity
  have h0 := A.nrm_nonneg la y ⟨hL t, hg⟩
  by_cases hla : (p : 𝓞 Ks) ∈ la.asIdeal
  · have hmem : la ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hla
    have hle : nf la ≤ m := (Finset.le_sup hmem).trans hm
    calc FinitePlace.mk la (N : Ks) ^ m * A.nrm la y ⟨hL t, hg⟩
        ≤ FinitePlace.mk la (N : Ks) ^ nf la * A.nrm la y ⟨hL t, hg⟩ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hN0 hN1 hle) h0
      _ ≤ FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) * A.nrm la y ⟨hL t, hg⟩ :=
          mul_le_mul_of_nonneg_right (hnf la hla) h0
      _ ≤ 1 := hb la y
  · have := hsup la hla t htW (htb la) y
    calc FinitePlace.mk la (N : Ks) ^ m * A.nrm la y ⟨hL t, hg⟩ ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ hN0 hN1) this h0 zero_le_one
      _ = 1 := one_mul 1

end Forms

section Span

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] (A : FormsL LL Ks WL W G)

theorem exists_pow_smul_mem_span (hL : WL →ₗ[LL] WL) (T : Finset WL) (hT : ∀ x ∈ T, x ∈ A.MK)
    (hMK : ∀ x ∈ A.MK, x ∈ Submodule.span (𝓞 Ks) (T : Set WL))
    (hspan : ∀ x ∈ A.WK, x ∈ Submodule.span Ks (T : Set WL)) (hW : ∀ x ∈ A.WK, hL x ∈ A.WK)
    {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hsup : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∉ la.asIdeal → ∀ (f : WL) (hf : f ∈ A.WK),
      (∀ y, A.nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, A.nrm la y ⟨hL f, hW f hf⟩ ≤ 1) :
    ∃ n : ℕ, ∀ x ∈ Submodule.span (𝓞 LL) (A.MK : Set WL),
      N ^ n • hL x ∈ Submodule.span (𝓞 LL) (A.MK : Set WL) := by
  classical
  have hex : ∀ t ∈ T, ∃ n : ℕ, ∀ m, n ≤ m → N ^ m • hL t ∈ A.MK := fun t ht =>
    exists_pow_smul_mem_MK A hL T hT hspan hW hp hpN hsup (hT t ht)
  choose! nf hnf using hex
  set n := T.sup nf
  have hks : ∀ (a : Ks) (x : WL), hL (a • x) = a • hL x := fun a x => LinearMap.map_smul_of_tower hL a x
  have h0 : ∀ f ∈ Submodule.span (𝓞 Ks) (T : Set WL), N ^ n • hL f ∈ A.MK := by
    intro f hfs
    induction hfs using Submodule.span_induction with
    | mem t ht => exact hnf t ht n (Finset.le_sup ht)
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul Ks a x, hks, algebraMap_smul, smul_comm]
      exact A.MK.smul_mem a hx
  have h1 : ∀ f ∈ A.MK, N ^ n • hL f ∈ A.MK := fun f hf => h0 f (hMK f hf)
  refine ⟨n, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem f hf => exact Submodule.subset_span (h1 f hf)
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  | smul b x _ hx =>
    rw [LinearMap.map_smul_of_tower, smul_comm]
    exact Submodule.smul_mem _ b hx

end Span

section Prime

variable {E : Type} [Field E] [NumberField E]

theorem exists_mem_of_list_prod_mem (P : HeightOneSpectrum (𝓞 E)) :
    ∀ l : List (𝓞 E), l.prod ∈ P.asIdeal → ∃ x ∈ l, x ∈ P.asIdeal
  | [], h => absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) P.isPrime.ne_top
  | a :: l, h => by
    rw [List.prod_cons] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨x, hx, hxP⟩ := exists_mem_of_list_prod_mem P l h
      exact ⟨x, List.mem_cons_of_mem a hx, hxP⟩

theorem exists_prime_dvd_card (P : HeightOneSpectrum (𝓞 E)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ P.asIdeal ∧ p ∣ Nat.card (𝓞 E ⧸ P.asIdeal) := by
  have e : Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  rw [← Nat.prod_primeFactorsList hN, Nat.cast_list_prod] at hmem
  obtain ⟨x, hx, hxP⟩ := exists_mem_of_list_prod_mem P _ hmem
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, hxP, e ▸ Nat.dvd_of_mem_primeFactorsList hp⟩

theorem prime_eq_of_mem (P : HeightOneSpectrum (𝓞 E)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpP : (p : 𝓞 E) ∈ P.asIdeal) (hqP : (q : 𝓞 E) ∈ P.asIdeal) : p = q := by
  by_contra hne
  have hco : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := ((Nat.coprime_primes hp hq).2 hne).cast
  obtain ⟨u, v, huv⟩ := hco
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hpP) (P.asIdeal.mul_mem_left _ hqP)))

end Prime

end GlobalTheory.SupPowNorm
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.RatSide

set_option maxHeartbeats 1600000 in

theorem intC_at_state : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ) (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → IntC (SOf x) (SbD (Dof x)) θ hL' := by
  intro hL hDec hI hT hRT
  refine ((GlobalTheory.T.hecke_reading_eigenvalue_place hL hDec hI hT hRT).and (formsC_at_state hL)).trans
    (StepW.of_all fun K B f T w _ _ H P x hA θ hL' _ hstab hrd => ?_)
  obtain ⟨hB, hF⟩ := H
  intro j k Pl hj1 hj2 hsp hnot hk
  obtain ⟨-, -, Tf, hTf, hMK, hspan⟩ := hF P x hA j hj1 hj2
  obtain ⟨p, hp, hpP, hpN⟩ := GlobalTheory.SupPowNorm.exists_prime_dvd_card Pl
  have hW : ∀ y ∈ ((SOf x).A j).WK, hL' j k Pl y ∈ ((SOf x).A j).WK := fun y hy => hstab j hj1 hj2 k Pl y hy
  obtain ⟨n, hn⟩ := GlobalTheory.SupPowNorm.exists_pow_smul_mem_span ((SOf x).A j) (hL' j k Pl) Tf hTf
    (fun y hy => (hMK y hy).2) hspan hW hp hpN fun la hla g hg hb y =>
      hB P x hA hL' hstab hrd j k Pl hj1 hj2 hsp hnot hk la
        (fun q hq hqP => by rw [GlobalTheory.SupPowNorm.prime_eq_of_mem Pl hq hp hqP hpP]; exact hla) g hg (hW g hg) hb y
  exact ⟨n, fun y hy _ => hn y hy⟩

end GlobalTheory.HeightCounting.RatSide
end
