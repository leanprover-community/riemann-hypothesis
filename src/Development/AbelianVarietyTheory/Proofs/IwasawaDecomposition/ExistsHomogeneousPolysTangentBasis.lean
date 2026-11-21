import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuccessiveMinimaPositiveNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteExtensionSplittingTorsionStatement

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.successive_minima_positive_norms : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (g : ℕ) (J : Type) [Fintype J] (h : J → Fin g → C), (∀ c : Fin g → C, (∀ j, ∑ i, h j i * c i = 0) → c = 0) → ∀ (m : ℕ) (a : Fin m → Fin g → C), LinearIndependent C a → ∀ (N : Fin m → ℝ), (∀ l, N l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧ (∀ j, ‖∑ i, h j i * ∑ l', cf l' * a l' i‖ ≤ 1) ∧ r = ‖cf l‖⁻¹}) → (∀ l, 0 < N l) ∧ ∀ (k : ℕ) (hk : k ≤ m), ∏ l : Fin k, N (Fin.castLE hk l) = ⨆ σ : Fin k → J, ‖∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s‖ := by
  first | exact @GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor | exact GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor | (intros; apply GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NormFam

theorem exists_lift_of_isIntegral (A R C : Type) [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] (hinj : Function.Injective (algebraMap A R))
    [Field C] [IsAlgClosed C] (x : A →+* C) :
    ∃ y : R →+* C, y.comp (algebraMap A R) = x := by
  classical
  have : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
  obtain ⟨𝔮, -, h𝔮, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker x)
    (⊥ : Ideal R) (by
      intro a ha
      simp only [Ideal.mem_comap, Ideal.mem_bot] at ha
      have : a = 0 := hinj (by simpa using ha)
      simp [this])
  let 𝔭 : Ideal A := Ideal.comap (algebraMap A R) 𝔮
  have : 𝔮.IsPrime := h𝔮
  have : 𝔭.IsPrime := Ideal.IsPrime.comap _
  let g : A ⧸ 𝔭 →+* C := Ideal.Quotient.lift 𝔭 x (fun a ha => by
    change a ∈ 𝔭 at ha
    rw [show 𝔭 = RingHom.ker x from hc] at ha
    exact ha)
  have hg : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [RingHom.mem_ker] at hq
    change x a = 0 at hq
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    change a ∈ 𝔭
    rw [show 𝔭 = RingHom.ker x from hc]
    exact hq
  let : Algebra (A ⧸ 𝔭) C := g.toAlgebra
  have : Module.IsTorsionFree (A ⧸ 𝔭) C := Module.isTorsionFree_iff_algebraMap_injective.mpr hg
  have : Module.IsTorsionFree (A ⧸ 𝔭) (R ⧸ 𝔮) := by
    apply Module.isTorsionFree_iff_algebraMap_injective.mpr
    exact Ideal.quotientMap_injective' le_rfl
  have : Algebra.IsAlgebraic (A ⧸ 𝔭) (R ⧸ 𝔮) := Algebra.IsIntegral.isAlgebraic
  let y₀ : (R ⧸ 𝔮) →ₐ[A ⧸ 𝔭] C := IsAlgClosed.lift
  refine ⟨y₀.toRingHom.comp (Ideal.Quotient.mk 𝔮), ?_⟩
  ext a
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have h1 : (Ideal.Quotient.mk 𝔮) (algebraMap A R a) =
      algebraMap (A ⧸ 𝔭) (R ⧸ 𝔮) (Ideal.Quotient.mk 𝔭 a) := rfl
  rw [h1, y₀.commutes]
  rfl

theorem finite_algHom (A A' E : Type) [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A']
    [Algebra A A'] [Module.Finite A A'] [Field E] [Algebra A E] [Module.IsTorsionFree A A']
    [Module.IsTorsionFree A E] :
    Finite (A' →ₐ[A] E) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := A')
  have : Algebra.IsIntegral A A' := Algebra.IsIntegral.of_finite A A'
  let Ψ : (A' →ₐ[A] E) → (∀ a : s, (minpoly A (a : A')).rootSet E) := fun σ a =>
    ⟨σ a, by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral _), ?_⟩
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]⟩
  refine Finite.of_injective Ψ ?_
  intro σ σ' h
  apply AlgHom.toLinearMap_injective
  apply LinearMap.ext_on hs
  intro a ha
  have := congrArg (fun f => (f ⟨a, ha⟩ : E)) h
  simpa [Ψ] using this

end GlobalTheory.NormFam

namespace GlobalTheory.NormFam

open MvPolynomial Polynomial in

theorem exists_eq_algebraMap_of_fixed (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CharZero A] (c : AlgebraicClosure (FractionRing A))
    (hfix : ∀ ρ : AlgebraicClosure (FractionRing A) ≃ₐ[FractionRing A]
      AlgebraicClosure (FractionRing A), ρ c = c)
    (hint : IsIntegral A c) : ∃ a : A, algebraMap A (AlgebraicClosure (FractionRing A)) a = c := by
  have hmem : c ∈ (⊥ : IntermediateField (FractionRing A) (AlgebraicClosure (FractionRing A))) := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup
      (⊥ : IntermediateField (FractionRing A) (AlgebraicClosure (FractionRing A))),
      IntermediateField.mem_fixedField_iff]
    intro ρ _
    exact hfix ρ
  rw [IntermediateField.mem_bot] at hmem
  obtain ⟨k, rfl⟩ := hmem
  have hk : IsIntegral A k :=
    (isIntegral_algebraMap_iff (algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))).injective).mp hint
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hk
  exact ⟨a, (IsScalarTower.algebraMap_apply A (FractionRing A) _ a).symm⟩

section Gauss

variable {C : Type} [NormedField C]

theorem gaussNorm_prod [IsUltrametricDist C] {κ : Type} (s : Finset κ) (p : κ → Polynomial C) :
    Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1 (∏ i ∈ s, p i) =
      ∏ i ∈ s, Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1 (p i) := by
  classical
  have hna : IsNonarchimedean (NormedField.toAbsoluteValue C) :=
    IsUltrametricDist.isNonarchimedean_norm
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [← Polynomial.C_1, Polynomial.gaussNorm_C]
    simp [NormedField.toAbsoluteValue]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Polynomial.gaussNorm_mul hna one_pos, ih]

theorem gaussNorm_eq_iSup_fin (p : Polynomial C) (n : ℕ) (hn : p.natDegree < n) :
    Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1 p = ⨆ i : Fin n, ‖p.coeff i‖ := by
  have hv : ∀ c : C, NormedField.toAbsoluteValue C c = ‖c‖ := fun c => rfl
  have hbdd : BddAbove (Set.range fun i : Fin n => ‖p.coeff i‖) := (Set.finite_range _).bddAbove
  apply le_antisymm
  · obtain ⟨i, hi⟩ := Polynomial.exists_eq_gaussNorm (NormedField.toAbsoluteValue C) 1 p
    rw [hi, hv, one_pow, _root_.mul_one]
    by_cases hin : i < n
    · exact le_ciSup hbdd ⟨i, hin⟩
    · have : p.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [this, norm_zero]
      exact Real.iSup_nonneg (fun _ => norm_nonneg _)
  · refine Real.iSup_le (fun i => ?_) (Polynomial.gaussNorm_nonneg _ _ zero_le_one)
    have := Polynomial.le_gaussNorm (NormedField.toAbsoluteValue C) p zero_le_one i
    rwa [hv, one_pow, _root_.mul_one] at this

theorem gaussNorm_sum_monomial {J : Type} [Fintype J] (e : J → ℕ) (he : Function.Injective e)
    (c : J → C) :
    Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1
      (∑ j, Polynomial.monomial (e j) (c j)) = ⨆ j, ‖c j‖ := by
  classical
  have hv : ∀ c : C, NormedField.toAbsoluteValue C c = ‖c‖ := fun c => rfl
  have hcoeff : ∀ i, (∑ j, Polynomial.monomial (e j) (c j)).coeff i =
      if h : ∃ j, e j = i then c h.choose else 0 := by
    intro i
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    split_ifs with h
    · rw [Finset.sum_eq_single h.choose]
      · simp [h.choose_spec]
      · intro j _ hj
        rw [if_neg]
        intro hij
        exact hj (he (hij.trans h.choose_spec.symm))
      · simp
    · apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      exact fun hij => h ⟨j, hij⟩
  have hbdd : BddAbove (Set.range fun j : J => ‖c j‖) := (Set.finite_range _).bddAbove
  apply le_antisymm
  · obtain ⟨i, hi⟩ := Polynomial.exists_eq_gaussNorm (NormedField.toAbsoluteValue C) 1 _
    rw [hi, hv, one_pow, _root_.mul_one, hcoeff]
    split_ifs with h
    · exact le_ciSup hbdd _
    · rw [norm_zero]
      exact Real.iSup_nonneg (fun _ => norm_nonneg _)
  · refine Real.iSup_le (fun j => ?_) (Polynomial.gaussNorm_nonneg _ _ zero_le_one)
    have := Polynomial.le_gaussNorm (NormedField.toAbsoluteValue C) (∑ j, Polynomial.monomial (e j) (c j))
      zero_le_one (e j)
    rw [hv, one_pow, _root_.mul_one, hcoeff] at this
    have h : ∃ j', e j' = e j := ⟨j, rfl⟩
    rw [dif_pos h] at this
    rwa [he h.choose_spec] at this

end Gauss

end GlobalTheory.NormFam

namespace GlobalTheory.NormFam

section Hom

variable {σ R S : Type} [CommRing R] [CommRing S]

def CoeffsHom (a : ℕ) (p : Polynomial (MvPolynomial σ R)) : Prop :=
  ∀ i, (p.coeff i).IsHomogeneous a

theorem CoeffsHom.mul {a b : ℕ} {p q : Polynomial (MvPolynomial σ R)} (hp : CoeffsHom a p)
    (hq : CoeffsHom b q) : CoeffsHom (a + b) (p * q) := by
  intro i
  rw [Polynomial.coeff_mul]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun x _ => (hp x.1).mul (hq x.2))

theorem CoeffsHom.one : CoeffsHom (σ := σ) (R := R) 0 1 := by
  intro i
  rw [Polynomial.coeff_one]
  split_ifs
  · exact MvPolynomial.isHomogeneous_one _ _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

theorem CoeffsHom.prod {κ : Type} (s : Finset κ) (a : ℕ) (p : κ → Polynomial (MvPolynomial σ R))
    (hp : ∀ i ∈ s, CoeffsHom a (p i)) : CoeffsHom (s.card * a) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CoeffsHom.one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi,
      show (s.card + 1) * a = a + s.card * a by ring]
    exact (hp i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem isHomogeneous_of_map_injective {f : R →+* S} (hf : Function.Injective f)
    {p : MvPolynomial σ R} {n : ℕ} (h : (MvPolynomial.map f p).IsHomogeneous n) :
    p.IsHomogeneous n := by
  intro d hd
  apply h
  rw [MvPolynomial.coeff_map]
  exact (map_ne_zero_iff f hf).mpr hd

theorem CoeffsHom.of_map_injective {f : R →+* S} (hf : Function.Injective f)
    {p : Polynomial (MvPolynomial σ R)} {a : ℕ}
    (h : CoeffsHom a (Polynomial.map (MvPolynomial.map f) p)) : CoeffsHom a p := by
  intro i
  have := h i
  rw [Polynomial.coeff_map] at this
  exact isHomogeneous_of_map_injective hf this

theorem exists_map_eq_of_coeff_mem_range (f : R →+* S) (q : MvPolynomial σ S)
    (h : ∀ m, ∃ r, f r = q.coeff m) : ∃ q₀ : MvPolynomial σ R, MvPolynomial.map f q₀ = q := by
  classical
  refine ⟨∑ m ∈ q.support, MvPolynomial.monomial m (h m).choose, ?_⟩
  rw [map_sum]
  simp only [MvPolynomial.map_monomial, (h _).choose_spec]
  exact MvPolynomial.support_sum_monomial_coeff q

theorem exists_map_eq_of_coeff_mem_range' (f : R →+* S) (P : Polynomial (MvPolynomial σ S))
    (h : ∀ i m, ∃ r, f r = (P.coeff i).coeff m) :
    ∃ P₀ : Polynomial (MvPolynomial σ R), Polynomial.map (MvPolynomial.map f) P₀ = P := by
  have : P ∈ (Polynomial.mapRingHom (MvPolynomial.map f)).range := by
    rw [Polynomial.mem_map_range]
    intro i
    obtain ⟨q₀, hq₀⟩ := exists_map_eq_of_coeff_mem_range f (P.coeff i) (h i)
    exact ⟨q₀, hq₀⟩
  obtain ⟨P₀, hP₀⟩ := this
  exact ⟨P₀, hP₀⟩

end Hom

end GlobalTheory.NormFam

namespace GlobalTheory.NormFam

section Pack

variable {A' R C σ J : Type} [CommRing A'] [CommRing R] [CommRing C] [Fintype σ] [Fintype J]

noncomputable def pack (e : J → ℕ) (ℓ : J → σ → A') : Polynomial (MvPolynomial σ A') :=
  ∑ j, Polynomial.monomial (e j) (∑ s, MvPolynomial.C (ℓ j s) * MvPolynomial.X s)

theorem map_pack (e : J → ℕ) (ℓ : J → σ → A') (f : A' →+* R) :
    Polynomial.map (MvPolynomial.map f) (pack e ℓ) = pack e (fun j s => f (ℓ j s)) := by
  simp [pack, Polynomial.map_sum, Polynomial.map_monomial, map_sum, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X]

theorem map_eval_pack (e : J → ℕ) (ℓ : J → σ → A') (f : A' →+* C) (T : σ → C) :
    Polynomial.map (MvPolynomial.eval₂Hom f T) (pack e ℓ) =
      ∑ j, Polynomial.monomial (e j) (∑ s, f (ℓ j s) * T s) := by
  simp [pack, Polynomial.map_sum, Polynomial.map_monomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]

theorem coeffsHom_pack (e : J → ℕ) (ℓ : J → σ → A') : CoeffsHom 1 (pack e ℓ) := by
  classical
  intro i
  rw [pack, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  split_ifs
  · apply MvPolynomial.IsHomogeneous.sum
    intro s _
    exact (MvPolynomial.isHomogeneous_X _ _).C_mul _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

omit [Fintype σ] in
theorem map_map_mv {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂)
    (g : R₂ →+* R₃) (p : Polynomial (MvPolynomial σ R₁)) :
    Polynomial.map (MvPolynomial.map g) (Polynomial.map (MvPolynomial.map f) p) =
      Polynomial.map (MvPolynomial.map (g.comp f)) p := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext fun q => MvPolynomial.map_map f g q

omit [Fintype σ] in
theorem map_evalHom_map (f : A' →+* R) (y : R →+* C) (T : σ → C)
    (p : Polynomial (MvPolynomial σ A')) :
    Polynomial.map (MvPolynomial.eval₂Hom y T) (Polynomial.map (MvPolynomial.map f) p) =
      Polynomial.map (MvPolynomial.eval₂Hom (y.comp f) T) p := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext fun q => by simp [MvPolynomial.eval₂_map]

end Pack

end GlobalTheory.NormFam

namespace GlobalTheory.NormFam

theorem norm_of_family : ∀ (A A' : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CharZero A] [CommRing A'] [IsDomain A'] [Algebra A A'] [Module.Finite A A'],
    Function.Injective (algebraMap A A') → ∀ (σ J : Type) [Fintype σ] [Fintype J]
    (ℓ : J → σ → A'), ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial σ A),
    (∀ i, (B i).IsHomogeneous d) ∧ ∀ (C : Type) [NormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] (x : A →+* C) (T : σ → C) (N : ℝ),
    (∀ x' : A' →+* C, x'.comp (algebraMap A A') = x →
      (⨆ j, ‖∑ s, x' (ℓ j s) * T s‖) = N) →
    N ^ (d : ℕ) = ⨆ i, ‖MvPolynomial.eval₂ x T (B i)‖ := by
  intro A A' _ _ _ _ _ _ _ _ hinj σ J _ _ ℓ
  classical

  let K := FractionRing A
  let E := AlgebraicClosure K
  let R : Subalgebra A E := integralClosure A E
  have hAE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  have hAR : Function.Injective (algebraMap A R) := by
    intro a b h
    apply hAE
    have := congrArg (fun r : R => (r : E)) h
    simpa using this
  have : Module.IsTorsionFree A A' := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Module.IsTorsionFree A E := Module.isTorsionFree_iff_algebraMap_injective.mpr hAE
  have : Algebra.IsIntegral A A' := Algebra.IsIntegral.of_finite A A'
  have : Finite (A' →ₐ[A] E) := finite_algHom A A' E
  let _ : Fintype (A' →ₐ[A] E) := Fintype.ofFinite _
  have : Nonempty (A' →ₐ[A] E) := ⟨IsAlgClosed.lift⟩

  let res : (A' →ₐ[A] E) → (A' →+* R) := fun τ =>
    τ.toRingHom.codRestrict R (fun a =>
      (mem_integralClosure_iff A E).mpr ((Algebra.IsIntegral.isIntegral (R := A) a).map τ))
  have hres : ∀ τ, (algebraMap R E).comp (res τ) = τ.toRingHom := fun τ => RingHom.ext fun a => rfl
  have hresA : ∀ τ, (res τ).comp (algebraMap A A') = algebraMap A R := by
    intro τ
    ext a
    simp [res]

  let e := Fintype.equivFin J
  let α := pack (fun j => (e j : ℕ)) ℓ
  let P : Polynomial (MvPolynomial σ R) := ∏ τ, Polynomial.map (MvPolynomial.map (res τ)) α
  let PE : Polynomial (MvPolynomial σ E) := Polynomial.map (MvPolynomial.map (algebraMap R E)) P
  have hPE : PE = ∏ τ : A' →ₐ[A] E, Polynomial.map (MvPolynomial.map τ.toRingHom) α := by
    simp only [PE, P, Polynomial.map_prod, map_map_mv, hres]

  have hinv : ∀ ρ : E ≃ₐ[K] E, Polynomial.map (MvPolynomial.map ρ.toRingHom) PE = PE := by
    intro ρ
    rw [hPE, Polynomial.map_prod]
    simp only [map_map_mv]
    let φ : (A' →ₐ[A] E) ≃ (A' →ₐ[A] E) :=
      { toFun := fun τ => (ρ.restrictScalars A).toAlgHom.comp τ
        invFun := fun τ => (ρ.symm.restrictScalars A).toAlgHom.comp τ
        left_inv := fun τ => by ext a; simp
        right_inv := fun τ => by ext a; simp }
    exact Fintype.prod_equiv φ _ _ (fun τ => rfl)

  have hfix : ∀ i m (ρ : E ≃ₐ[K] E), ρ (((P.coeff i).coeff m : R) : E) = (((P.coeff i).coeff m : R) : E) := by
    intro i m ρ
    have h1 : (PE.coeff i).coeff m = (((P.coeff i).coeff m : R) : E) := by
      simp only [PE, Polynomial.coeff_map, MvPolynomial.coeff_map]
      rfl
    have h2 := congrArg (fun Q : Polynomial (MvPolynomial σ E) => (Q.coeff i).coeff m) (hinv ρ)
    simp only [Polynomial.coeff_map, MvPolynomial.coeff_map] at h2
    rw [h1] at h2
    exact h2
  have hcoef : ∀ i m, ∃ a : A, algebraMap A R a = (P.coeff i).coeff m := by
    intro i m
    obtain ⟨a, ha⟩ := exists_eq_algebraMap_of_fixed A (((P.coeff i).coeff m : R) : E) (hfix i m)
      ((mem_integralClosure_iff A E).mp ((P.coeff i).coeff m).2)
    exact ⟨a, Subtype.ext (by simpa using ha)⟩
  obtain ⟨P₀, hP₀⟩ := exists_map_eq_of_coeff_mem_range' (algebraMap A R) P hcoef

  let d : ℕ+ := ⟨Fintype.card (A' →ₐ[A] E), Fintype.card_pos⟩
  have hPhom : CoeffsHom (d : ℕ) P := by
    have := CoeffsHom.prod Finset.univ 1 (fun τ => Polynomial.map (MvPolynomial.map (res τ)) α)
      (fun τ _ => by rw [map_pack]; exact coeffsHom_pack _ _)
    rw [Finset.card_univ, _root_.mul_one] at this
    exact this
  have hP₀hom : CoeffsHom (d : ℕ) P₀ := CoeffsHom.of_map_injective hAR (hP₀ ▸ hPhom)
  refine ⟨d, P₀.natDegree + 1, fun i => P₀.coeff i, fun i => hP₀hom i, ?_⟩
  intro C _ _ _ x T N hN

  obtain ⟨y, hy⟩ := exists_lift_of_isIntegral A R C hAR x
  have hlift : ∀ τ, (y.comp (res τ)).comp (algebraMap A A') = x := by
    intro τ
    rw [RingHom.comp_assoc, hresA, hy]

  let ev : Polynomial (MvPolynomial σ R) →+* Polynomial C :=
    Polynomial.mapRingHom (MvPolynomial.eval₂Hom y T)
  have hev1 : ev P = ∏ τ, ∑ j, Polynomial.monomial (e j : ℕ)
      (∑ s, (y.comp (res τ)) (ℓ j s) * T s) := by
    simp only [ev, P, Polynomial.coe_mapRingHom, Polynomial.map_prod]
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    rw [map_evalHom_map, map_eval_pack]
  have hev2 : ev P = Polynomial.map (MvPolynomial.eval₂Hom x T) P₀ := by
    rw [← hP₀]
    simp only [ev, Polynomial.coe_mapRingHom]
    rw [map_evalHom_map, hy]
  have he : Function.Injective (fun j => (e j : ℕ)) := fun a b h => e.injective (Fin.ext h)
  have hG1 : Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1 (ev P) = N ^ (d : ℕ) := by
    have : ∀ τ ∈ (Finset.univ : Finset (A' →ₐ[A] E)),
        Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1
          (∑ j, Polynomial.monomial (e j : ℕ) (∑ s, (y.comp (res τ)) (ℓ j s) * T s)) = N := by
      intro τ _
      rw [gaussNorm_sum_monomial _ he]
      exact hN _ (hlift τ)
    rw [hev1, gaussNorm_prod, Finset.prod_congr rfl this, Finset.prod_const, Finset.card_univ]
    rfl
  have hG2 : Polynomial.gaussNorm (NormedField.toAbsoluteValue C) 1 (ev P) =
      ⨆ i : Fin (P₀.natDegree + 1), ‖MvPolynomial.eval₂ x T (P₀.coeff i)‖ := by
    rw [hev2, gaussNorm_eq_iSup_fin _ (P₀.natDegree + 1)
      (Nat.lt_succ_of_le (Polynomial.natDegree_map_le))]
    simp only [Polynomial.coeff_map, MvPolynomial.coe_eval₂Hom]
  rw [← hG1, hG2]

end GlobalTheory.NormFam
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_invariants_norms : ∀ (A A' : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [CommRing A'] [IsDomain A'] [Algebra A A'] [Module.Finite A A'], Function.Injective (algebraMap A A') → ∀ (σ J : Type) [Fintype σ] [Fintype J] (ℓ : J → σ → A'), ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial σ A), (∀ i, (B i).IsHomogeneous d) ∧ ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] (x : A →+* C) (T : σ → C) (N : ℝ), (∀ x' : A' →+* C, x'.comp (algebraMap A A') = x → (⨆ j, ‖∑ s, x' (ℓ j s) * T s‖) = N) → N ^ (d : ℕ) = ⨆ i, ‖MvPolynomial.eval₂ x T (B i)‖ := by
  atlas_forward_decl GlobalTheory.NormFam.norm_of_family
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.LineNorm.WedgeMax

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_poly (A A' : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [CommRing A']
    [IsDomain A'] [Algebra A A'] [Module.Finite A A'] (hinj : Function.Injective (algebraMap A A')) (g k : ℕ)
    (J : Type) [Fintype J] (h : J → Fin g → A') (c : ℕ) (hc : c ≠ 0) (hh : ∀ i, ∃ j, h j = Pi.single i (c : A')) :
    ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial (Fin k → Fin g) A), (∀ i, (B i).IsHomogeneous d) ∧
      (∀ s, ∃ (i : Fin n) (c : ℕ), c ≠ 0 ∧
        B i = MvPolynomial.C (c : A) * (MvPolynomial.X s : MvPolynomial (Fin k → Fin g) A) ^ (d : ℕ)) ∧
      ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : A →+* C)
        (m : ℕ) (hk : k ≤ m) (a : Fin m → Fin g → C), LinearIndependent C a → ∀ N : Fin m → ℝ,
        (∀ x' : A' →+* C, x'.comp (algebraMap A A') = x → ∀ l, N l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧
          (∀ l', l < l' → cf l' = 0) ∧ (∀ j, ‖∑ i, x' (h j i) * ∑ l', cf l' * a l' i‖ ≤ 1) ∧ r = ‖cf l‖⁻¹}) →
        ((d : ℕ) : ℝ) * ∑ l : Fin k, Real.log (N (Fin.castLE hk l)) =
          Real.log (⨆ i, ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) := by
  classical
  obtain ⟨d, n, B, hB, hN⟩ := GlobalTheory.T.exists_homogeneous_invariants_norms A A' hinj (Fin k → Fin g) (Fin k → J) fun σ s => ∏ i, h (σ i) (s i)
  let e := Fintype.equivFin (Fin n ⊕ (Fin k → Fin g))
  let B' : Fin n ⊕ (Fin k → Fin g) → MvPolynomial (Fin k → Fin g) A :=
    Sum.elim B fun s => MvPolynomial.C (((c ^ k) ^ (d : ℕ) : ℕ) : A) * MvPolynomial.X s ^ (d : ℕ)
  refine ⟨d, _, fun i => B' (e.symm i), fun i => ?_,
    fun s => ⟨e (Sum.inr s), (c ^ k) ^ (d : ℕ), pow_ne_zero _ (pow_ne_zero _ hc), by simp [B']⟩, ?_⟩
  · show (B' (e.symm i)).IsHomogeneous d
    rcases e.symm i with i | s
    · exact hB i
    · exact (MvPolynomial.isHomogeneous_X_pow s _).C_mul _
  intro C _ _ _ _ x m hk a ha N hx
  obtain ⟨x', hx'⟩ : ∃ x' : A' →+* C, x'.comp (algebraMap A A') = x := by
    by_contra h0
    have h1 := (hN C x (minor a hk) 0 fun y hy => absurd ⟨y, hy⟩ h0).trans
      (hN C x (minor a hk) 1 fun y hy => absurd ⟨y, hy⟩ h0).symm
    simp at h1
  have cov := fun (y : A' →+* C) (hy : y.comp (algebraMap A A') = x) =>
    GlobalTheory.T.successive_minima_positive_norms C g J (fun j i => y (h j i)) (fun b hb => funext fun i => by
      obtain ⟨j, hj⟩ := hh i
      have := hb j
      rw [Finset.sum_eq_single i (fun i' _ hi => by simp [hj, Pi.single_eq_of_ne hi]) (by simp)] at this
      simpa [hj, hc] using this) m a ha N (hx y hy)
  have hP := hN C x (minor a hk) (∏ l : Fin k, N (Fin.castLE hk l)) fun y hy => by
    simp only [map_prod]
    exact ((cov y hy).2 k hk).symm
  have hpos := (cov x' hx').1
  have hP0 : 0 ≤ ∏ l : Fin k, N (Fin.castLE hk l) := Finset.prod_nonneg fun l _ => (hpos _).le
  rw [← Real.log_prod fun l _ => (hpos _).ne', ← Real.log_pow,
    e.symm.iSup_comp (g := fun i => ‖MvPolynomial.eval₂ x (minor a hk) (B' i)‖)]
  congr 1
  refine le_antisymm ?_ (Real.iSup_le ?_ (pow_nonneg hP0 _))
  · rw [hP]
    exact Real.iSup_le (fun i => le_ciSup (f := fun i => ‖MvPolynomial.eval₂ x (minor a hk) (B' i)‖)
      (Finite.bddAbove_range _) (Sum.inl i)) (Real.iSup_nonneg fun _ => norm_nonneg _)
  · rintro (i | s)
    · rw [hP]
      exact le_ciSup (f := fun i => ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) (Finite.bddAbove_range _) i
    · have e1 : ‖MvPolynomial.eval₂ x (minor a hk) (B' (Sum.inr s))‖ = ‖(c : C) ^ k * minor a hk s‖ ^ (d : ℕ) := by
        simp [B', mul_pow]
      rw [e1]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      choose j hj using hh
      rw [(cov x' hx').2 k hk]
      refine le_trans (le_of_eq ?_) (le_ciSup (Finite.bddAbove_range _) fun i => j (s i))
      rw [Finset.sum_eq_single s (fun s' _ hs => ?_) (by simp)]
      · simp [hj]
      · obtain ⟨i, hi⟩ := Function.ne_iff.1 hs
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hj, Pi.single_eq_of_ne hi]), zero_mul]

theorem spMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_dual_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (dualMap (ψ.comp φ)) = spMap (dualMap ψ) ≫ spMap (dualMap φ) := by
  rw [← spMap_comp]
  congr 1
  exact RingHom.ext fun x => by ext <;> simp [dualMap]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem isTanBasis_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {x : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : IsTanBasis t x e) :
    IsTanBasis t (spMap φ ≫ x) fun i => spMap (dualMap φ) ≫ e i := by
  refine ⟨fun i => GlobalTheory.LieMet.isTan_map φ rfl (he.1 i), fun T _ ψ w => ?_⟩
  have := he.2 T (ψ.comp φ) w
  simpa only [spMap_comp, spMap_dual_comp, Category.assoc] using this

theorem exists_comb {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hu : ∀ l, IsTanAtG t x (u l)) (cf : Fin m → S) : ∃ w, IsTanAtG t x w ∧ IsCombAtG t x u cf w :=
  ⟨_, GlobalTheory.LieMet.isTan_tv (∑ l, cf l • GlobalTheory.LieMet.tanOf (hu l)),
    (GlobalTheory.LieMet.isComb_iff (fun l => GlobalTheory.LieMet.tanOf (hu l)) cf _).2 rfl⟩

theorem comb_unique {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hu : ∀ l, IsTanAtG t x (u l)) {cf : Fin m → S} {w w' : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x u cf w) (h' : IsCombAtG t x u cf w') : w = w' :=
  ((isCombAtG_iff t _ (fun j => ovT (hu j)) _ _).1 h).symm.trans ((isCombAtG_iff t _ (fun j => ovT (hu j)) _ _).1 h')

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

omit [IsUltrametricDist C] in

theorem grNorm_eq {x : Sp C ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber C) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)} {P : (Fin g → C) → Prop}
    (hΛ : ∀ b w, IsCombAtG t x e b w → (w ∈ Λ ↔ P b)) {u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}
    {a : Fin m → Fin g → C} (hu : ∀ l, IsCombAtG t x e (a l) (u l)) (l : Fin m) :
    GlobalTheory.ShFam.Pad.grNorm t x Λ u l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧
      P (fun i => ∑ l', cf l' * a l' i) ∧ r = ‖cf l‖⁻¹} := by
  have hut : ∀ l, IsTanAtG t x (u l) := fun l => by
    obtain ⟨w, hw, hw'⟩ := exists_comb t he (a l)
    exact comb_unique t he hw' (hu l) ▸ hw
  have key : ∀ cf w, IsCombAtG t x u cf w → (w ∈ Λ ↔ P fun i => ∑ l', cf l' * a l' i) := fun cf w hw => by
    refine hΛ _ w ?_
    have := tanLinG e he u (Matrix.of fun i l => a l i) cf w hu hw
    convert this using 2 with i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  unfold GlobalTheory.ShFam.Pad.grNorm
  congr 1
  ext r
  refine exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ => ?_
  refine ⟨fun ⟨w, h1, h2⟩ => (key cf w h2).1 h1, fun hP => ?_⟩
  obtain ⟨w, -, hw⟩ := exists_comb t hut cf
  exact ⟨w, (key cf w hw).2 hP, hw⟩

theorem ext_intO (hX : X.IsSeparated) (x x' : Sp ↥(intO C) ⟶ X)
    (h : spMap (intO C).subtype ≫ x' = spMap (intO C).subtype ≫ x) : x' = x := by
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro z hz
    have : z = 0 := Subtype.ext hz
    simp [this])⟩
  exact ext_of_isDominant (spMap (intO C).subtype) h

theorem mem_latDR (hX : X.IsSeparated) {x : Sp ↥(intO C) ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber ↥(intO C)) ⟶ t.G.left)} (he : IsTanBasis t x e) (b : Fin g → C)
    (w : Sp (DualNumber C) ⟶ t.G.left)
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ x) (fun i => spMap (dualMap (intO C).subtype) ≫ e i) b w) :
    w ∈ latDR t (spMap (intO C).subtype ≫ x) ↔ ∀ i, ‖b i‖ ≤ 1 := by
  have h1 : spMap (RingHom.id ↥(intO C)) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id ↥(intO C)) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id ↥(intO C))) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have hD0 := he.2 _ (RingHom.id ↥(intO C))
  simp only [h1, h3, Category.id_comp] at hD0
  have hDk := (isTanBasis_map t (intO C).subtype he).1
  refine ⟨?_, fun hc => ?_⟩
  · rintro ⟨xO', hx, vO, hv, rfl⟩
    obtain rfl := ext_intO hX _ xO' hx
    obtain ⟨a, ha, -⟩ := hD0 vO hv
    have e := (he.2 C _ _ (GlobalTheory.LieMet.isTan_map (intO C).subtype rfl hv)).unique hw
      (GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha)
    intro i
    rw [e]
    exact (a i).2
  · obtain ⟨v, hv, ha⟩ := exists_comb t he.1 fun i => (⟨b i, hc i⟩ : ↥(intO C))
    exact ⟨x, rfl, v, hv, comb_unique t hDk (GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha) hw⟩

theorem norm_le_one {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] [Module.Finite A A'] (x' : A' →+* C)
    (hx : ∀ a, ‖x' (algebraMap A A' a)‖ ≤ 1) (b : A') : ‖x' b‖ ≤ 1 := by
  have hi : ∀ z : C, z ∈ (NormedField.valuation (K := C)).integer ↔ ‖z‖ ≤ 1 := fun z => by
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast Iff.rfl
  let y : A →+* (NormedField.valuation (K := C)).integer :=
    (x'.comp (algebraMap A A')).codRestrict _ fun a => (hi _).2 (hx a)
  exact (hi _).1 ((Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral
    (IsIntegral.map_of_comp_eq y x' rfl (Algebra.IsIntegral.isIntegral (R := A) b)))

theorem of_covectors {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] (x₀ : Sp A ⟶ X) {g : ℕ}
    {e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)} (he : IsTanBasis t x₀ e) (q k : ℕ) (A' : Type) [CommRing A']
    [IsDomain A'] [Algebra A A'] [Module.Finite A A'] (hinj : Function.Injective (algebraMap A A'))
    (J : Type) [Fintype J] (h : J → Fin g → A') (c : ℕ) (hc : c ≠ 0) (hh : ∀ i, ∃ j, h j = Pi.single i (c : A'))
    (hΛ : ∀ (p : ℕ) [Fact p.Prime] (y : A' →+* ↥(intO ℂ_[p])) (b : Fin g → ℂ_[p])
      (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
      IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ spMap y ≫ spMap (algebraMap A A') ≫ x₀)
        (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ spMap (dualMap y) ≫ spMap (dualMap (algebraMap A A')) ≫ e i)
        b w →
      (w ∈ lat t p (spMap (intO ℂ_[p]).subtype ≫ spMap y ≫ spMap (algebraMap A A') ≫ x₀) (decide (p = q)) ↔
        ∀ j, ‖∑ i, (y (h j i) : ℂ_[p]) * b i‖ ≤ 1)) :
    ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial (Fin k → Fin g) A), (∀ i, (B i).IsHomogeneous d) ∧ (∀ s, ∃ (i : Fin n) (c : ℕ), c ≠ 0 ∧ B i = MvPolynomial.C (c : A) * (MvPolynomial.X s : MvPolynomial (Fin k → Fin g) A) ^ (d : ℕ)) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : A →+* ℂ_[p]), (∀ a, ‖x a‖ ≤ 1) → ∀ (m : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap x ≫ x₀) (fun i => spMap (dualMap x) ≫ e i) (a l) (u l)) → ((d : ℕ) : ℝ) * ∑ l : Fin k, Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap x ≫ x₀) (lat t p (spMap x ≫ x₀) (decide (p = q))) u (Fin.castLE hk l)) = Real.log (⨆ i, ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) := by
  obtain ⟨d, n, B, h1, h2, h3⟩ := exists_poly A A' hinj g k J h c hc hh
  refine ⟨d, n, B, h1, h2, fun p _ x hx m hk u a ha hu => h3 ℂ_[p] x m hk a ha _ fun x' hx' l => ?_⟩
  subst hx'
  let y : A' →+* ↥(intO ℂ_[p]) := x'.codRestrict _ fun b => norm_le_one x' hx b
  have e1 : x' = (intO ℂ_[p]).subtype.comp y := rfl
  refine grNorm_eq t (isTanBasis_map t _ he).1 (P := fun b => ∀ j, ‖∑ i, x' (h j i) * b i‖ ≤ 1) ?_ hu l
  have := hΛ p y
  rw [e1]
  simpa only [spMap_comp, spMap_dual_comp, Category.assoc, RingHom.comp_apply, Subring.coe_subtype] using this

theorem norm_sum_single {g : ℕ} {A' : Type} [CommRing A'] (y : A' →+* ↥(intO C)) (c : ℕ) (b : Fin g → C) (i : Fin g) :
    ∑ i', (y ((Pi.single i (c : A') : Fin g → A') i') : C) * b i' = c * b i := by
  rw [Finset.sum_eq_single i (fun i' _ hi => by simp [Pi.single_eq_of_ne hi]) (by simp)]
  simp

theorem wedge_norm_max : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (x₀ : Sp A ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ t.G.left)), IsTanBasis t x₀ e → ∀ q k : ℕ, ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial (Fin k → Fin g) A), (∀ i, (B i).IsHomogeneous d) ∧ (∀ s, ∃ (i : Fin n) (c : ℕ), c ≠ 0 ∧ B i = MvPolynomial.C (c : A) * (MvPolynomial.X s : MvPolynomial (Fin k → Fin g) A) ^ (d : ℕ)) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : A →+* ℂ_[p]), (∀ a, ‖x a‖ ≤ 1) → ∀ (m : ℕ) (hk : k ≤ m) (u : Fin m → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (a : Fin m → Fin g → ℂ_[p]), LinearIndependent ℂ_[p] a → (∀ l, IsCombAtG t (spMap x ≫ x₀) (fun i => spMap (dualMap x) ≫ e i) (a l) (u l)) → ((d : ℕ) : ℝ) * ∑ l : Fin k, Real.log (GlobalTheory.ShFam.Pad.grNorm t (spMap x ≫ x₀) (lat t p (spMap x ≫ x₀) (decide (p = q))) u (Fin.castLE hk l)) = Real.log (⨆ i, ‖MvPolynomial.eval₂ x (minor a hk) (B i)‖) := by
  intro hHT E _ _ _ H X _ t hX A _ _ _ _ _ x₀ g e he q k
  by_cases hq : q.Prime
  · obtain ⟨A', _, _, _, _, hinj, _, hζ, hsp⟩ := GlobalTheory.T.exists_finite_extension_splitting_torsion E H X t A x₀ q hq.ne_zero
    have : CharZero A' := charZero_of_injective_algebraMap hinj
    have he' := isTanBasis_map t (algebraMap A A') he
    obtain ⟨n, h, hh⟩ := GlobalTheory.T.exists_tangent_presentation_prime E H X t A' _ g _ he' q hq hζ hsp
    refine of_covectors t x₀ he q k A' hinj (Fin n ⊕ Fin g) (Sum.elim h fun i => Pi.single i (q : A')) q hq.ne_zero
      (fun i => ⟨Sum.inr i, rfl⟩) fun p _ y b w hw => ?_
    simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, norm_sum_single]
    have hn : ∀ r : ℕ, ‖(r : ℂ_[p])‖ = ‖(r : ℚ_[p])‖ := fun r => by
      rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    by_cases hp : p = q
    · subst hp
      rw [decide_eq_true rfl]
      exact GlobalTheory.T.unique_integral_lift_norm_p_inverse hHT E H X t p ℂ_[p] (by rw [hn, Padic.norm_p]) _ (ext_intO hX _) g _
        (isTanBasis_map t y he') n (fun j i => y (h j i)) (hh ℂ_[p] y).1 (hh ℂ_[p] y).2 b w hw
    · rw [decide_eq_false hp]
      have h1 : ‖(q : ℂ_[p])‖ = 1 := by
        rw [hn, Padic.norm_natCast_eq_one_iff]
        exact (Nat.coprime_primes Fact.out hq).2 hp
      refine (mem_latDR t hX (isTanBasis_map t y he') b w hw).trans ?_
      simp only [norm_mul, h1, _root_.one_mul]
      refine ⟨fun hb => ⟨fun j => ?_, hb⟩, fun hb => hb.2⟩
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
      rw [norm_mul]
      exact mul_le_one₀ (y (h j i)).2 (norm_nonneg _) (hb i)
  · have he' := isTanBasis_map t (algebraMap A A) he
    refine of_covectors t x₀ he q k A (fun _ _ h => h) (Fin g) (fun i => Pi.single i ((1 : ℕ) : A)) 1 one_ne_zero
      (fun i => ⟨i, rfl⟩) fun p hp y b w hw => ?_
    simp only [norm_sum_single]
    rw [decide_eq_false fun h : p = q => hq (h ▸ hp.out)]
    simp only [Nat.cast_one, _root_.one_mul]
    exact mem_latDR t hX (isTanBasis_map t y he') b w hw

end GlobalTheory.LineNorm.WedgeMax
end
