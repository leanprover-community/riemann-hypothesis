import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem exists_integral_basis_linear_coordinates :
    ∀ (V K C : Type) [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field C] [Algebra K C] (R : Subring C), (∀ x : V, algebraMap K C (algebraMap V K x) ∈ R) → ∀ s : Finset C, (∀ x ∈ s, x ∈ R) → ∃ (r : ℕ) (c : Fin r → C) (φ : Fin r → (C →ₗ[K] K)), (∀ j, c j ∈ R) ∧ ∀ x ∈ s, (∀ j, φ j x ∈ (algebraMap V K).range) ∧ x = ∑ j, algebraMap K C (φ j x) * c j := by
  intro V K C _ _ _ _ _ _ _ _ R hR s hs
  classical
  letI : Algebra V C := ((algebraMap K C).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap V C) :=
    (algebraMap K C).injective.comp (IsFractionRing.injective V K)
  haveI : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hinj
  let M : Submodule V C := Submodule.span V (s : Set C)
  haveI : Module.Finite V M := Module.Finite.span_of_finite V s.finite_toSet
  haveI : Module.Free V M := inferInstance
  have hMR : ∀ x ∈ M, x ∈ R := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hs x hx
    | zero => exact R.zero_mem
    | add x y _ _ hx hy => exact R.add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def]
      exact R.mul_mem (hR a) hx
  let b := Module.finBasis V M
  let c : Fin (Module.finrank V M) → C := fun j => (b j : C)
  have hcV : LinearIndependent V c :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hcK : LinearIndependent K c := (LinearIndependent.iff_fractionRing V K).1 hcV
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K c).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (by
      exact hcK.fintypeLinearCombination_injective))
  refine ⟨_, c, fun j => (LinearMap.proj j).comp g, fun j => hMR _ (b j).2, ?_⟩
  intro x hx
  have hxM : x ∈ M := Submodule.subset_span hx
  have h1 : x = Fintype.linearCombination K c (fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j)) := by
    have := congrArg Subtype.val (b.sum_repr ⟨x, hxM⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at this
    rw [Fintype.linearCombination_apply]
    simp only [algebraMap_smul]
    exact this.symm
  have h2 : g x = fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j) := by
    have := LinearMap.congr_fun hg (fun j => algebraMap V K (b.repr ⟨x, hxM⟩ j))
    rw [LinearMap.comp_apply, ← h1] at this
    exact this
  refine ⟨fun j => ⟨b.repr ⟨x, hxM⟩ j, ?_⟩, ?_⟩
  · simp [h2]
  · simp only [LinearMap.comp_apply, LinearMap.proj_apply, h2, ← Algebra.smul_def]
    rw [Fintype.linearCombination_apply] at h1
    exact h1

end GlobalTheory
end

section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoeffFunctional

open MvPolynomial

variable {σ K L : Type} [Field K] [Field L] [Algebra K L]

def coeffMap (φ : L →ₗ[K] K) (P : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ μ ∈ P.support, monomial μ (φ (P.coeff μ))

theorem coeff_coeffMap (φ : L →ₗ[K] K) (P : MvPolynomial σ L) (μ : σ →₀ ℕ) :
    (coeffMap φ P).coeff μ = φ (P.coeff μ) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

theorem coeffMap_add (φ : L →ₗ[K] K) (P Q : MvPolynomial σ L) :
    coeffMap φ (P + Q) = coeffMap φ P + coeffMap φ Q := by
  ext μ
  simp [coeff_coeffMap]

theorem coeffMap_zero (φ : L →ₗ[K] K) : coeffMap φ (0 : MvPolynomial σ L) = 0 := by
  ext μ
  simp [coeff_coeffMap]

theorem coeffMap_map_mul_C (φ : L →ₗ[K] K) (A : MvPolynomial σ K) (c : L) :
    coeffMap φ (MvPolynomial.C c * MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.C (φ c) * A := by
  ext μ
  rw [coeff_coeffMap, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm c, ← Algebra.smul_def,
    map_smul, smul_eq_mul, mul_comm]

theorem coeffMap_comm (φ : L →ₗ[K] K) (f : MvPolynomial σ L →ₗ[L] MvPolynomial σ L)
    (g : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (h : ∀ A, f (MvPolynomial.map (algebraMap K L) A) = MvPolynomial.map (algebraMap K L) (g A))
    (P : MvPolynomial σ L) : coeffMap φ (f P) = g (coeffMap φ P) := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, coeffMap_add, coeffMap_add, map_add, hp, hq]
  | monomial μ c =>
    have e : (monomial μ c : MvPolynomial σ L) =
        MvPolynomial.C c * MvPolynomial.map (algebraMap K L) (monomial μ 1) := by
      rw [map_monomial, map_one, C_mul_monomial, mul_one]
    rw [e, coeffMap_map_mul_C, C_mul', map_smul, h, ← C_mul', coeffMap_map_mul_C, C_mul', C_mul',
      map_smul]

variable {T : Type} (r : T → ℕ) (n : ℕ)

theorem lap_one_map (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ'))
    (A : MvPolynomial (Letter T r n) K) :
    lap r n L 1 τ τ' a a' (MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.map (algebraMap K L) (lap r n K 1 τ τ' a a' A) := by
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  by_cases hb : b = b'
  · subst hb
    simp [pderiv_map]
  · simp [Matrix.one_apply_ne hb]

theorem rowShift_map (s : T) (i i' : Fin (r s)) (t : K) (A : MvPolynomial (Letter T r n) K) :
    rowShift r n L s i i' (algebraMap K L t) (MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.map (algebraMap K L) (rowShift r n K s i i' t A) := by
  induction A using MvPolynomial.induction_on with
  | C c => simp [rowShift]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p l hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [rowShift, aeval_X]
    split_ifs <;> simp

theorem mem_HHa_of_coeff_functional :
    ∀ (T : Type) (r : T → ℕ) (n : ℕ) (K C : Type) [Field K] [Field C] [Algebra K C] (φ : C →ₗ[K] K) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) C) (Q : MvPolynomial (Letter T r n) K), (∀ μ, Q.coeff μ = φ (P.coeff μ)) → P ∈ HHa r n C cc isX a → Q ∈ HHa r n K cc isX a := by
  intro T r n K L _ _ _ φ cc isX a P Q hQ hP
  have hQ' : Q = coeffMap φ P := by
    ext μ
    rw [hQ, coeff_coeffMap]
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ b b'
    rw [hQ', ← coeffMap_comm φ _ _ (lap_one_map r n τ (cc τ) b b') P, h1 τ hτ b b', coeffMap_zero]
  · intro s i i' hi t
    have := coeffMap_comm φ (rowShift r n L s i i' (algebraMap K L t)).toLinearMap
      (rowShift r n K s i i' t).toLinearMap (rowShift_map r n s i i' t) P
    simp only [AlgHom.toLinearMap_apply] at this
    rw [hQ', ← this, h2 s i i' hi]
  · intro m hm
    refine h3 m ?_
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [hQ, h0, map_zero])

end GlobalTheory.CoeffFunctional
end
end

section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem exists_integral_combination_of_mem_HaO :
    ∀ (T : Type) (r : T → ℕ) (n : ℕ) (V K C : Type) [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field C] (e : K →+* C) (R : Subring C), (∀ x : V, e (algebraMap V K x) ∈ R) → ∀ (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) C), P ∈ HaO r n C R cc isX a → ∃ (s : ℕ) (c : Fin s → C) (Q : Fin s → MvPolynomial (Letter T r n) K), (∀ j, c j ∈ R) ∧ (∀ j, Q j ∈ HaO r n K (algebraMap V K).range cc isX a) ∧ P = ∑ j, MvPolynomial.C (c j) * MvPolynomial.map e (Q j) := by
  intro T r n V K C _ _ _ _ _ _ _ e R hR cc isX a P hP
  classical
  let _ : Algebra K C := e.toAlgebra
  obtain ⟨hH, hO⟩ := hP
  obtain ⟨s, c, φ, hc, hφ⟩ := GlobalTheory.exists_integral_basis_linear_coordinates V K C R hR (P.support.image fun μ => P.coeff μ) (by
    intro x hx
    obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hx
    exact hO μ)
  let Q : Fin s → MvPolynomial (Letter T r n) K := fun j =>
    ∑ μ ∈ P.support, MvPolynomial.monomial μ (φ j (P.coeff μ))
  have hQ : ∀ j μ, (Q j).coeff μ = φ j (P.coeff μ) := by
    intro j μ
    simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
  refine ⟨s, c, Q, hc, fun j => ⟨GlobalTheory.CoeffFunctional.mem_HHa_of_coeff_functional T r n K C (φ j) cc isX a P (Q j) (hQ j) hH, ?_⟩, ?_⟩
  · intro μ
    rw [hQ]
    by_cases h : μ ∈ P.support
    · exact (hφ _ (Finset.mem_image_of_mem _ h)).1 j
    · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]
      exact zero_mem _
  · ext μ
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, hQ]
    by_cases h : μ ∈ P.support
    · refine (hφ _ (Finset.mem_image_of_mem _ h)).2.trans ?_
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · rw [MvPolynomial.notMem_support_iff.mp h]
      simp

end GlobalTheory
end
