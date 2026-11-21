import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier

section
namespace GlobalTheory.EvaluationSpanTopToricGeometry

theorem span_eval_eq_top {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V] :
    Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype))
      = ⊤ := by

  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set v : V := (Module.evalEquiv ℂ V).symm f with hv
  have hfv : Module.evalEquiv ℂ V v = f := by rw [hv, LinearEquiv.apply_symm_apply]
  have hv0 : v = 0 := by
    apply Subtype.ext
    funext x
    have hx : (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype ∈ LinearMap.ker f :=
      hle (Submodule.subset_span ⟨x, rfl⟩)
    rw [LinearMap.mem_ker, ← hfv] at hx
    exact hx
  apply hf0
  rw [← hfv, hv0, map_zero]

theorem exists_sum_mul {X Y : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (L : Submodule ℂ (Y → ℂ)) (F : X → Y → ℂ) (hV : ∀ y : Y, (fun x : X => F x y) ∈ V)
    (hL : ∀ x : X, F x ∈ L) :
    ∃ (n : ℕ) (h : Fin n → X → ℂ) (k : Fin n → Y → ℂ),
      (∀ i : Fin n, h i ∈ V ∧ k i ∈ L) ∧
        ∀ (x : X) (y : Y), F x y = ∑ i : Fin n, h i x * k i y := by

  let Φ : Module.Dual ℂ V →ₗ[ℂ] (Y → ℂ) :=
    { toFun := fun φ y => φ ⟨fun x => F x y, hV y⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

  have hΦ : ∀ φ, Φ φ ∈ L := by
    have hle : Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype))
        ≤ L.comap Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hL x
    intro φ
    exact hle (by rw [span_eval_eq_top V]; trivial)
  let b := Module.finBasis ℂ V
  refine ⟨Module.finrank ℂ V, fun i => (b i : X → ℂ), fun i => Φ (b.coord i), fun i => ⟨(b i).2, hΦ _⟩, ?_⟩
  intro x y
  have hs := congrArg (fun w : V => (w : X → ℂ) x) (b.sum_repr ⟨fun x' => F x' y, hV y⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
  rw [← hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.EvaluationSpanTopToricGeometry
end

section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ThetaAddition

theorem exists_sum_mul {X Y : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (L : Submodule ℂ (Y → ℂ)) (F : X → Y → ℂ) (h1 : ∀ y, (fun x => F x y) ∈ V)
    (h2 : ∀ x, F x ∈ L) :
    ∃ (n : ℕ) (h : Fin n → X → ℂ) (k : Fin n → Y → ℂ), (∀ i, h i ∈ V ∧ k i ∈ L) ∧
      ∀ x y, F x y = ∑ i, h i x * k i y := by
  first
  | exact @_root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul
  | exact _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul
  | (apply _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvaluationSpanTopToricGeometry.exists_sum_mul ..)

theorem left_mem {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) {f f' : (Fin g → ℂ) → ℂ}
    (hf : f ∈ thetaLevel N τ) (hf' : f' ∈ thetaLevel N τ) (w : Fin g → ℂ) :
    (fun z => f (z + w) * f' (z - w)) ∈ thetaLevel (2 * N) τ := by
  refine ⟨(hf.1.comp (by fun_prop)).mul (hf'.1.comp (by fun_prop)), fun n n' z => ?_⟩
  have e1 : z + τ *ᵥ ofIntVec n + ofIntVec n' + w = (z + w) + τ *ᵥ ofIntVec n + ofIntVec n' := by
    abel
  have e2 : z + τ *ᵥ ofIntVec n + ofIntVec n' - w = (z - w) + τ *ᵥ ofIntVec n + ofIntVec n' := by
    abel
  show f _ * f' _ = _ * (f _ * f' _)
  rw [e1, e2, hf.2, hf'.2, mul_mul_mul_comm, ← eC_add]
  congr 2
  rw [dotProduct_add, dotProduct_sub]; push_cast; ring

theorem right_mem {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) {f f' : (Fin g → ℂ) → ℂ}
    (hf : f ∈ thetaLevel N τ) (hf' : f' ∈ thetaLevel N τ) (z : Fin g → ℂ) :
    (fun w => f (z + w) * f' (z - w)) ∈ thetaLevel (2 * N) τ := by
  refine ⟨(hf.1.comp (by fun_prop)).mul (hf'.1.comp (by fun_prop)), fun n n' w => ?_⟩
  have e1 : z + (w + τ *ᵥ ofIntVec n + ofIntVec n') = (z + w) + τ *ᵥ ofIntVec n + ofIntVec n' := by
    abel
  have e2 : z - (w + τ *ᵥ ofIntVec n + ofIntVec n')
      = (z - w) + τ *ᵥ ofIntVec (-n) + ofIntVec (-n') := by
    rw [ofIntVec_neg, ofIntVec_neg, mulVec_neg]; abel
  show f _ * f' _ = _ * (f _ * f' _)
  rw [e1, e2, hf.2, hf'.2, mul_mul_mul_comm, ← eC_add]
  congr 2
  rw [ofIntVec_neg, mulVec_neg, neg_dotProduct_neg, neg_dotProduct, dotProduct_add, dotProduct_sub]
  push_cast; ring

theorem addition_level_two_mul :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f f' : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → (Differentiable ℂ f' ∧ ∀ (n n' : Fin g → ℤ) z, f' (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f' z) → ∃ (n : ℕ) (h k : Fin n → (Fin g → ℂ) → ℂ), (∀ i, (Differentiable ℂ (h i) ∧ ∀ (n n' : Fin g → ℤ) z, (h i) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (h i) z) ∧ (Differentiable ℂ (k i) ∧ ∀ (n n' : Fin g → ℤ) z, (k i) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (k i) z)) ∧ ∀ z w, f (z + w) * f' (z - w) = ∑ i, h i z * k i w) := by
  intro H1 H2 g τ hτ N hN f f' hf hf'
  have hN2 : 1 ≤ 2 * N := by omega
  have hle : thetaLevel (2 * N) τ ≤ _ := fun φ hφ => H2 g τ hτ (2 * N) hN2 φ hφ
  haveI : FiniteDimensional ℂ (thetaLevel (2 * N) τ) := by
    haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range
      (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / (2 * N : ℕ)) 0 (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ)))
    exact Submodule.finiteDimensional_of_le hle
  exact exists_sum_mul (thetaLevel (2 * N) τ) (thetaLevel (2 * N) τ)
    (fun z w => f (z + w) * f' (z - w)) (left_mem τ N hf hf') (right_mem τ N hf hf')

end GlobalTheory.ThetaAddition
end
