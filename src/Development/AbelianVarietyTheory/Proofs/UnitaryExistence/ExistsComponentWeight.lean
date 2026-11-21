import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralRatZetaOfCoeff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSectionsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetEqOneOfTrivialOnHalf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelAutomorphismPeriodFamilyStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexFrobeniusPointsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOneReductionOfDetOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetCharacterReductionInvariantStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.CharacterFunction

theorem exists_weight {ι A : Type} [Finite ι] [CommGroup A] (R : ι → ι → A → Prop)
    (tr : ∀ i j m a b, R i j a → R j m b → R i m (a * b)) (loop : ∀ i a, R i i a → a = 1)
    (hf : ∀ i j a, R i j a → ∃ f : ι → ι, Function.Surjective f ∧ f i = j ∧ ∀ x, R x (f x) a)
    (N : ℕ) (hN : ∀ i j a, R i j a → a ^ N = 1) :
    ∃ v : ι → A, (∀ i, v i ^ N = 1) ∧ ∀ i j a, R i j a → v j = a * v i := by
  have sy : ∀ i j a, R i j a → R j i a⁻¹ := by
    intro i j a h
    obtain ⟨f, hs, rfl, hx⟩ := hf i j a h
    have hi : Function.Injective f := Finite.injective_iff_surjective.2 hs
    obtain ⟨N, hN, hp⟩ := Function.mem_periodicPts.1 (hi.mem_periodicPts i)
    have it : ∀ m x, R x (f^[m + 1] x) (a ^ (m + 1)) := by
      intro m
      induction m with
      | zero => intro x; simpa using hx x
      | succ m ih =>
        intro x
        rw [Function.iterate_succ_apply', pow_succ]
        exact tr _ _ _ _ _ (ih x) (hx _)
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have h2 : f^[2 * M + 1] (f i) = i := by
      rw [← Function.iterate_succ_apply]
      have := (hp.mul_const 2).eq
      rwa [show (M + 1) * 2 = (2 * M + 1).succ by simp only [Nat.succ_eq_add_one]; ring] at this
    have h3 := it (2 * M) (f i)
    rw [h2] at h3
    rwa [← eq_inv_of_mul_eq_one_right (loop _ _ (tr _ _ _ _ _ h h3))]
  let R' : ι → ι → A → Prop := fun i j a => (i = j ∧ a = 1) ∨ R i j a
  have sy' : ∀ i j a, R' i j a → R' j i a⁻¹ := by
    rintro i j a (⟨rfl, rfl⟩ | h)
    · exact Or.inl ⟨rfl, inv_one⟩
    · exact Or.inr (sy _ _ _ h)
  have tr' : ∀ i j m a b, R' i j a → R' j m b → R' i m (a * b) := by
    rintro i j m a b (⟨rfl, rfl⟩ | h) h'
    · rwa [one_mul]
    · rcases h' with ⟨rfl, rfl⟩ | h'
      · rw [mul_one]; exact Or.inr h
      · exact Or.inr (tr _ _ _ _ _ h h')
  have loop' : ∀ i a, R' i i a → a = 1 := by
    rintro i a (⟨-, h⟩ | h)
    · exact h
    · exact loop _ _ h
  let s : Setoid ι := ⟨fun i j => ∃ a, R' i j a, fun i => ⟨1, Or.inl ⟨rfl, rfl⟩⟩,
    fun ⟨a, h⟩ => ⟨_, sy' _ _ _ h⟩, fun ⟨a, h⟩ ⟨b, h'⟩ => ⟨_, tr' _ _ _ _ _ h h'⟩⟩
  have hv : ∀ i, ∃ a, R' (Quotient.mk s i).out i a := fun i => Quotient.mk_out (s := s) i
  choose v hv using hv
  refine ⟨v, fun i => (hv i).elim (fun h => by rw [h.2, one_pow]) (hN _ _ _), fun i j a h => ?_⟩
  have e : Quotient.mk s i = Quotient.mk s j := Quotient.sound ⟨a, Or.inr h⟩
  have h1 := hv j
  rw [← e] at h1
  have h2 := loop' _ _ (tr' _ _ _ _ _ (tr' _ _ _ _ _ (hv i) (Or.inr h)) (sy' _ _ _ h1))
  rw [mul_inv_eq_one] at h2
  rw [← h2, mul_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


theorem natCast_mem_half {l l₂ : Level H} {pd : ℕ} {I : Ideal (𝓞 E)} (hM : l₂.M = l.M * pd)
    (hMb : l₂.Mb = l.Mb * I) : (pd : 𝓞 E) ∈ I := by
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(pd : 𝓞 E)} := by
    have h2 := l₂.prod
    rw [hMb, hM, Ideal.map_mul, mul_mul_mul_comm, l.prod, Nat.cast_mul,
      ← Ideal.span_singleton_mul_span_singleton] at h2
    refine mul_left_cancel₀ ?_ h2
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM0
  have : Ideal.span {(pd : 𝓞 E)} ≤ I := hp ▸ Ideal.mul_le_left
  exact this (Ideal.subset_span rfl)

theorem nsmul_mem_smul_top {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] {I : Ideal R} {N : ℕ}
    (h : (N : R) ∈ I) (x : L) : N • x ∈ (I • ⊤ : Submodule R L) := by
  rw [← Nat.cast_smul_eq_nsmul R]
  exact Submodule.smul_mem_smul h trivial

theorem four_le_card {R : Type} [CommRing R] [Finite R] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h : (p : R) = 0)
    (𝔪 : Ideal R) (hm : 𝔪.IsMaximal) : 4 ≤ Nat.card (R ⧸ 𝔪) := by
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Finite (R ⧸ 𝔪) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have h0 : (p : R ⧸ 𝔪) = 0 := by rw [← map_natCast (Ideal.Quotient.mk 𝔪), h, map_zero]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (R ⧸ 𝔪) p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  have := Nat.card_le_card_of_injective _ (ZMod.castHom (dvd_refl p) (R ⧸ 𝔪)).injective
  rw [Nat.card_zmod] at this
  omega

theorem char_eq_one {l l₂ : Level H} {pd : ℕ} {I : Ideal (𝓞 E)} (hp : pd.Prime) (h5 : 5 ≤ pd) (hM : l₂.M = l.M * pd)
    (hA : l₂.A = 1) (hMb : l₂.Mb = l.Mb * I) {A : Type} [CommGroup A]
    (ψ : ((Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)) ≃ₗ[𝓞 E] (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La))) →* A)
    (D' : Datum H) (t : Dw.La →ₗ[𝓞 E] D'.La) (tinj : ∀ a, (∃ b, t a = l₂.M' • b) → ∃ b, a = l₂.M' • b)
    (tsurj : ∀ b, ∃ a e, b = t a + l₂.M' • e) (g : Sim Dw)
    (hg : ∀ a, g.f l.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La))
    (k : (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)) ≃ₗ[𝓞 E] (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)))
    (hk : ∀ a, Submodule.Quotient.mk (g.f l₂.M a) = k (Submodule.Quotient.mk a))
    (γ : D'.La ≃ₗ[𝓞 E] D'.La) (hγ : ∀ a b, D'.EF (γ a) (γ b) = D'.EF a b)
    (h : ∀ a, γ (t (g.f l₂.M a)) - t a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D'.La)) : ψ k = 1 := by
  have hM' : l₂.M' = l.M * pd := by rw [Level.M', hA, Nat.lcm_one_right, hM]
  have hpI : (pd : 𝓞 E) ∈ I := natCast_mem_half hM hMb
  have hMI : ((l₂.M' : ℕ) : 𝓞 E) ∈ I := by rw [hM', Nat.cast_mul]; exact I.mul_mem_left _ hpI
  have hMl : (l.M : 𝓞 E) ∈ l.Mb := by
    have : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)
  have hMl' : ((l₂.M' : ℕ) : 𝓞 E) ∈ l.Mb := by rw [hM', Nat.cast_mul]; exact l.Mb.mul_mem_right _ hMl
  have hmap : ∀ (J : Ideal (𝓞 E)) {L L' : Type} [AddCommGroup L] [Module (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L']
      (f : L →ₗ[𝓞 E] L') (x : L), x ∈ (J • ⊤ : Submodule (𝓞 E) L) → f x ∈ (J • ⊤ : Submodule (𝓞 E) L') := by
    intro J L L' _ _ _ _ f x hx
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hlow : ∀ b, γ b - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D'.La) := by
    intro b
    obtain ⟨a, e, rfl⟩ := tsurj b
    obtain ⟨w, hw⟩ := g.tower l.M pd (by have := l.three_le; omega) hp.pos a
    rw [← hM] at hw
    have h1 : g.f l₂.M a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have := add_mem (hw ▸ nsmul_mem_smul_top hMl w) (hg a)
      rwa [sub_add_sub_cancel] at this
    have h2 := hmap _ (γ : D'.La →ₗ[𝓞 E] D'.La) _ (hmap _ t _ h1)
    have h3 : γ (t (g.f l₂.M a)) - t a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D'.La) :=
      Submodule.smul_mono (hMb ▸ Ideal.mul_le_left) le_rfl (h a)
    have h4 := add_mem (sub_mem h3 h2) (nsmul_mem_smul_top hMl' (γ e - e))
    convert h4 using 1
    simp only [map_add, map_sub, map_nsmul, LinearEquiv.coe_coe, smul_sub]
    abel
  have hdet := HalfLevelDet.det_eq_one_of_trivial_on_half E H D' l γ hγ (fun a ha => by
    have : γ a - a ∈ (Ideal.span {(l.M : 𝓞 E)} • ⊤ : Submodule (𝓞 E) D'.La) := by
      refine Submodule.smul_induction_on ha (fun c hc b _ => ?_) (fun u v hu hv => ?_)
      · rw [map_smul, ← smul_sub, ← l.prod, mul_comm, Submodule.mul_smul]
        exact Submodule.smul_mem_smul hc (hlow b)
      · rw [map_add, add_sub_add_comm]; exact add_mem hu hv
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at this
    obtain ⟨e, -, he⟩ := this
    exact ⟨e, by rw [← Nat.cast_smul_eq_nsmul (𝓞 E), he]; abel⟩)
  have hI0 : I ≠ ⊥ := fun e => hp.ne_zero (by rw [e, Ideal.mem_bot] at hpI; exact_mod_cast hpI)
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  haveI := D'.fin
  haveI := D'.proj
  have hsurj : ∀ b, ∃ a, b - t a ∈ (I • ⊤ : Submodule (𝓞 E) D'.La) := fun b => by
    obtain ⟨a, e, rfl⟩ := tsurj b
    exact ⟨a, by rw [add_sub_cancel_left]; exact nsmul_mem_smul_top hMI e⟩
  refine GlobalTheory.T.det_character_reduction_invariant (𝓞 E) Dw.La D'.La I A ψ t (γ : D'.La →ₗ[𝓞 E] D'.La) k
    (four_le_card hp h5 (by rw [← map_natCast (Ideal.Quotient.mk I)]; exact Ideal.Quotient.eq_zero_iff_mem.2 hpI))
    hsurj (fun a ha => ?_) (GlobalTheory.T.det_one_reduction_of_det_one (𝓞 E) E D'.La I _ hdet)
    (fun a => ⟨_, hk a, Submodule.smul_mono (hMb ▸ Ideal.mul_le_right) le_rfl (h a)⟩)
  have key : ∀ b ∈ (I • ⊤ : Submodule (𝓞 E) D'.La), ∃ a' ∈ (I • ⊤ : Submodule (𝓞 E) Dw.La), ∃ e,
      b = t a' + l₂.M' • e := by
    intro b hb
    refine Submodule.smul_induction_on hb (fun c hc b _ => ?_) ?_
    · obtain ⟨a, e, rfl⟩ := tsurj b
      exact ⟨c • a, Submodule.smul_mem_smul hc trivial, c • e, by rw [smul_add, map_smul, smul_comm c l₂.M']⟩
    · rintro _ _ ⟨u, hu, e, rfl⟩ ⟨v, hv, e', rfl⟩
      exact ⟨u + v, add_mem hu hv, e + e', by rw [map_add, smul_add]; abel⟩
  obtain ⟨a', ha', e, he⟩ := key _ ha
  obtain ⟨b, hb⟩ := tinj (a - a') ⟨e, by rw [map_sub, he, add_sub_cancel_left]⟩
  have := add_mem (hb ▸ nsmul_mem_smul_top hMI b) ha'
  rwa [sub_add_cancel] at this




end GlobalTheory.CharacterFunction
