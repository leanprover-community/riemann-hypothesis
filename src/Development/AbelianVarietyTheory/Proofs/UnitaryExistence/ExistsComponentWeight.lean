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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSections
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetEqOneOfTrivialOnHalf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelAutomorphismPeriodFamily
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexFrobeniusPoints
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetCharacterReductionInvariant

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_detect_frobenius_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), PtsDetect (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (ex Dw a n) := by
  first | exact @GlobalTheory.Frames.ptsDetect_framed | exact GlobalTheory.Frames.ptsDetect_framed | (intros; apply GlobalTheory.Frames.ptsDetect_framed <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_automorphism_period_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (KA l).val.toRingHom ty) (s : Sim Dw) (ρ : Xo.X ≅ Xo.X), IsTypeFn H Dw.p Dw.q ty → Xo.LevAut s ρ → (∀ i, ∃ i', ∀ P, IsPeriod (F.Di i) ty P → ∃ P', IsPeriod (F.Di i') ty P' ∧ F.u i P ≫ ρ.hom = F.u i' P') ∧ ∀ i P P', IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → F.u i P ≫ ρ.hom = F.u i P' → ∃ γ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La, (∀ a b, (F.Di i).EF (γ a) (γ b) = (F.Di i).EF a b) ∧ ∀ a, γ (F.t i (s.f l.M a)) - F.t i a ∈ l.Mb • (⊤ : Submodule (𝓞 E) (F.Di i).La) := by
  first | exact @GlobalTheory.LevStab.levAut_component | exact GlobalTheory.LevStab.levAut_component | (intros; apply GlobalTheory.LevStab.levAut_component <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_frobenius_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] [Algebra c.F k] (y y' : FrPt Xo c k), ∃ z z' : FrPt Xo c (CAt c.F.val.toRingHom), (∀ ρ : Xo.X ⟶ Xo.X, y'.x = y.x ≫ ρ → z'.x = z.x ≫ ρ) ∧ (∀ f ∈ sec Xo c 0 0, evR Xo c f y = 0 → evR Xo c f z = 0) ∧ ∀ f ∈ sec Xo c 0 0, ∀ a : c.F, evR Xo c f z' = algebraMap c.F (CAt c.F.val.toRingHom) a * evR Xo c f z → evR Xo c f y' = algebraMap c.F k a * evR Xo c f y := by
  first | exact @GlobalTheory.Frames.exists_complex_framed_pair | exact GlobalTheory.Frames.exists_complex_framed_pair | (intros; apply GlobalTheory.Frames.exists_complex_framed_pair <;> assumption)
end

section
section
set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.DetMod

theorem det_baseChange_of_rel {R S L : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup L] [Module R L]
    {r : ℕ} (x : Fin r → L) (b : Module.Basis (Fin r) S (S ⊗[R] L)) (hb : ∀ j, b j = 1 ⊗ₜ x j)
    (γ : L →ₗ[R] L) (s : R) (a : Matrix (Fin r) (Fin r) R) (ha : ∀ j, s • γ (x j) = ∑ i, a i j • x i) :
    algebraMap R S s ^ r * LinearMap.det (LinearMap.baseChange S γ) = algebraMap R S a.det := by
  have h : LinearMap.toMatrix b b (algebraMap R S s • LinearMap.baseChange S γ) = (algebraMap R S).mapMatrix a := by
    ext i j
    have h1 : (algebraMap R S s • LinearMap.baseChange S γ) (b j) = ∑ i, algebraMap R S (a i j) • b i := by
      rw [LinearMap.smul_apply, hb, LinearMap.baseChange_tmul, algebraMap_smul, ← TensorProduct.tmul_smul, ha,
        TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, algebraMap_smul, TensorProduct.tmul_smul]
    rw [LinearMap.toMatrix_apply, h1, b.repr_sum_self]
    rfl
  rw [RingHom.map_det, ← h, map_smul, Matrix.det_smul, LinearMap.det_toMatrix, Fintype.card_fin]

theorem det_baseChange_quot_eq_one : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (I : Ideal R) [Finite (R ⧸ I)] (γ : L →ₗ[R] L), LinearMap.det (LinearMap.baseChange K γ) = 1 → LinearMap.det (LinearMap.baseChange (R ⧸ I) γ) = 1 := by
  intro R K _ _ _ _ _ L _ _ _ _ I _ γ hγ
  by_cases hI : I = ⊤
  · haveI := Ideal.Quotient.subsingleton_iff.2 hI
    exact Subsingleton.elim _ _
  set r := Module.finrank R L with hr
  haveI : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] L) r (fun P => by
    haveI := P.isMaximal
    letI : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
      ((R ⧸ I) ⧸ P.asIdeal) L).finrank_eq]
    have h1 := Module.rankAtStalk_baseChange (R := R) (M := L) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
    rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
    exact h1)
  have hsurj : Function.Surjective (TensorProduct.mk R (R ⧸ I) L 1) :=
    TensorProduct.mk_surjective R L (R ⧸ I) Ideal.Quotient.mk_surjective
  choose x hx using fun j => hsurj (b j)
  have hb : ∀ j, b j = 1 ⊗ₜ x j := fun j => (hx j).symm
  have hsup : (⊤ : Submodule R L) ≤ Submodule.span R (Set.range x) ⊔ I • ⊤ := by
    intro l _
    choose c hc using fun i => Ideal.Quotient.mk_surjective (b.repr (1 ⊗ₜ l) i)
    have h0 : ((1 : R ⧸ I) ⊗ₜ[R] (l - ∑ i, c i • x i)) = 0 := by
      rw [TensorProduct.tmul_sub, TensorProduct.tmul_sum, sub_eq_zero, ← b.sum_repr (1 ⊗ₜ l)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hc, TensorProduct.tmul_smul, ← hb, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    have h1 := congrArg (TensorProduct.quotTensorEquivQuotSMul L I) h0
    rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h1
    have : l = ∑ i, c i • x i + (l - ∑ i, c i • x i) := by abel
    rw [this]
    exact Submodule.add_mem_sup
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) h1
  obtain ⟨s, hs1, hs⟩ : ∃ s : R, s - 1 ∈ I ∧ ∀ l : L, s • l ∈ Submodule.span R (Set.range x) := by
    obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
      (⊤ : Submodule R (L ⧸ Submodule.span R (Set.range x))) Module.Finite.fg_top (by
        intro q _
        obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (hsup (Submodule.mem_top : l ∈ ⊤))
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hu, zero_add]
        refine Submodule.smul_induction_on hv (fun a ha z _ => ?_) (fun u v hu hv => ?_)
        · rw [Submodule.Quotient.mk_smul]; exact Submodule.smul_mem_smul ha trivial
        · rw [Submodule.Quotient.mk_add]; exact add_mem hu hv)
    refine ⟨s, hs1, fun l => ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact hs _ trivial
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using hs1
  have hsK : algebraMap R K s ≠ 0 := fun h => hs0 (IsFractionRing.injective R K (by rw [h, map_zero]))
  choose a ha using fun j => (Submodule.mem_span_range_iff_exists_fun R).1 (hs (γ (x j)))
  have hspan : ⊤ ≤ Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[R] x j) := by
    intro t ht
    clear ht
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add u v hu hv => exact add_mem hu hv
    | tmul k l =>
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hs l)
      have : k ⊗ₜ[R] l = (k * (algebraMap R K s)⁻¹) • ∑ i, algebraMap R K (c i) • ((1 : K) ⊗ₜ[R] x i) := by
        simp only [algebraMap_smul, ← TensorProduct.tmul_smul]
        rw [← TensorProduct.tmul_sum, hc, TensorProduct.tmul_smul, ← algebraMap_smul K s, smul_smul,
          inv_mul_cancel_right₀ hsK, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hrk : Fintype.card (Fin r) = Module.finrank K (K ⊗[R] L) := by
    rw [Fintype.card_fin, hr, (IsLocalizedModule.isBaseChange (nonZeroDivisors R) K (TensorProduct.mk R K L 1)).finrank_eq]
  have hK := det_baseChange_of_rel x (basisOfTopLeSpanOfCardEqFinrank _ hspan hrk) (fun j => by simp) γ s
    (Matrix.of fun i j => a j i) (fun j => (ha j).symm)
  have hQ := det_baseChange_of_rel x b hb γ s (Matrix.of fun i j => a j i) (fun j => (ha j).symm)
  rw [hγ, mul_one, ← map_pow] at hK
  have hs' : algebraMap R (R ⧸ I) s = 1 := by
    rw [Ideal.Quotient.algebraMap_eq, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    exact hs1
  rw [← IsFractionRing.injective R K hK, map_pow, hs', one_pow, one_mul] at hQ
  exact hQ

end GlobalTheory.DetMod
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_one_reduction_of_det_one : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (I : Ideal R) [Finite (R ⧸ I)] (γ : L →ₗ[R] L), LinearMap.det (LinearMap.baseChange K γ) = 1 → LinearMap.det (LinearMap.baseChange (R ⧸ I) γ) = 1 := by
  atlas_forward_decl GlobalTheory.DetMod.det_baseChange_quot_eq_one
end

section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_character_reduction_invariant : ∀ (R : Type) [CommRing R] [IsDomain R] (L L' : Type) [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L'] [Module.Finite R L'] [Module.Projective R L'] (I : Ideal R) [Finite (R ⧸ I)] (A : Type) [CommGroup A] (ψ : ((L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (L ⧸ (I • ⊤ : Submodule R L))) →* A) (t : L →ₗ[R] L') (γ : L' →ₗ[R] L') (k : (L ⧸ (I • ⊤ : Submodule R L)) ≃ₗ[R] (L ⧸ (I • ⊤ : Submodule R L))), (∀ 𝔪 : Ideal (R ⧸ I), 𝔪.IsMaximal → 4 ≤ Nat.card ((R ⧸ I) ⧸ 𝔪)) → (∀ b, ∃ a, b - t a ∈ (I • ⊤ : Submodule R L')) → (∀ a, t a ∈ (I • ⊤ : Submodule R L') → a ∈ (I • ⊤ : Submodule R L)) → LinearMap.det (LinearMap.baseChange (R ⧸ I) γ) = 1 → (∀ a, ∃ a', (Submodule.Quotient.mk a' : L ⧸ (I • ⊤ : Submodule R L)) = k (Submodule.Quotient.mk a) ∧ γ (t a') - t a ∈ (I • ⊤ : Submodule R L')) → ψ k = 1 := by
  first | exact @GlobalTheory.char_eq_one_of_inverse_reduction_det_one | exact GlobalTheory.char_eq_one_of_inverse_reduction_det_one | (intros; apply GlobalTheory.char_eq_one_of_inverse_reduction_det_one <;> assumption)
end

section
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
end
