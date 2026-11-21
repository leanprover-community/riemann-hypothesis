import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.IntegralModuleBases.NormGsoSqLeTwoPowMulOfValEqAdd
import ReciprocityTheory.ReducedBases.ExistsRedOf
import ReciprocityTheory.ReducedBases.PrefixProdGeOne

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

open Module Matrix
open scoped NumberField

def gramConst (d : ℕ) : ℝ := 2 ^ (d * (d - 1))

def endConst (d : ℕ) : ℝ := 4 ^ (d * d)

def ShortBasisStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (R : ℝ)
    (v : Fin (finrank ℝ E) → E), LinearIndependent ℝ v → (∀ i, v i ∈ L) → (∀ i, ‖v i‖ ≤ R) →
    ∃ b : Module.Basis (Fin (finrank ℝ E)) ℤ L, ∀ j, ‖(b j : E)‖ ≤ (finrank ℝ E : ℝ) * R

def ModuleBasisStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (J κ : Type) [Finite J] [Finite κ]
    (A : J → E →ₗ[ℝ] E) (x : κ → E) (α R : ℝ), 0 ≤ α → (∀ j y, ‖A j y‖ ≤ α * ‖y‖) →
    (∀ k, ‖x k‖ ≤ R) → (∀ j k, A j (x k) ∈ L) →
    Submodule.span ℝ (Set.range fun p : J × κ => A p.1 (x p.2)) = ⊤ →
    ∃ b : Module.Basis (Fin (finrank ℝ E)) ℤ L, ∀ i, ‖(b i : E)‖ ≤ (finrank ℝ E : ℝ) * (α * R)

def LatticeRedStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (μ V : ℝ)
    (c : Module.Basis (Fin (finrank ℝ E)) ℤ L), 0 < μ → 0 ≤ V →
    (∀ x ∈ L, x ≠ 0 → μ ≤ ‖x‖) → (Matrix.gram ℝ fun i => (c i : E)).det ≤ V ^ 2 →
    ∃ b : Module.Basis (Fin (finrank ℝ E)) ℤ L,
      (∀ i, ‖(b i : E)‖ ≤ 2 ^ (finrank ℝ E * finrank ℝ E) * V / μ ^ (finrank ℝ E - 1)) ∧
      ∀ (x : L) (i : Fin (finrank ℝ E)),
        |((b.repr x i : ℤ) : ℝ)| ≤ 3 ^ finrank ℝ E * ‖(x : E)‖ / μ

def IntegerBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    ∃ ω : Module.Basis (Fin (finrank ℚ K)) ℤ (𝓞 K), ∀ (i : Fin (finrank ℚ K)) (φ : K →+* ℂ),
      ‖φ (ω i : K)‖ ≤ 2 ^ (finrank ℚ K * finrank ℚ K) * Real.sqrt |(NumberField.discr K : ℝ)|

def IntegralModuleBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : 𝓞 K →+* Module.End ℝ E) (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (κ : Type) [Finite κ] (x : κ → E) (R : ℝ),
    (∀ (a : 𝓞 K) (B : ℝ), (∀ φ : K →+* ℂ, ‖φ (a : K)‖ ≤ B) → ∀ y, ‖ρ a y‖ ≤ B * ‖y‖) →
    (∀ k, ‖x k‖ ≤ R) → (∀ (a : 𝓞 K) k, ρ a (x k) ∈ L) →
    Submodule.span ℝ (Set.range fun p : 𝓞 K × κ => ρ p.1 (x p.2)) = ⊤ →
    ∃ b : Module.Basis (Fin (finrank ℝ E)) ℤ L, ∀ i, ‖(b i : E)‖ ≤
      (finrank ℝ E : ℝ) * (2 ^ (finrank ℚ K * finrank ℚ K) *
        Real.sqrt |(NumberField.discr K : ℝ)| * R)

def RedGramStatement : Prop :=
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (m D : ℝ), A.PosDef → 0 < m →
    (∀ x : Fin d → ℤ, x ≠ 0 → m ≤ (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ))) →
    A.det ≤ D →
    ∃ e : Module.Basis (Fin d) ℤ (Fin d → ℤ),
      (∀ i, (fun l => (e i l : ℝ)) ⬝ᵥ (A *ᵥ fun l => (e i l : ℝ)) ≤
        2 ^ (d * (d - 1)) * D / m ^ (d - 1)) ∧
      ∀ (x : Fin d → ℤ) (i : Fin d), ((e.repr x i : ℤ) : ℝ) ^ 2 ≤
        9 ^ d * ((fun l => (x l : ℝ)) ⬝ᵥ (A *ᵥ fun l => (x l : ℝ))) / m

def GramReduceStatement : Prop :=
  ∀ (d : ℕ) (G : Matrix (Fin d) (Fin d) ℤ), Gᵀ = G → (G.map ((↑) : ℤ → ℝ)).PosDef →
    ∃ P : Matrix (Fin d) (Fin d) ℤ, IsUnit P.det ∧
      ∀ i j, |((Pᵀ * G * P) i j : ℝ)| ≤ gramConst d * (G.det : ℝ)

def DecoratedReduceStatement : Prop :=
  ∀ (d k : ℕ) (G : Matrix (Fin d) (Fin d) ℤ) (T : Fin k → Matrix (Fin d) (Fin d) ℤ) (α : ℝ),
    Gᵀ = G → (G.map ((↑) : ℤ → ℝ)).PosDef → 0 ≤ α →
    (∀ (a : Fin k) (x : Fin d → ℝ),
      ((T a).map ((↑) : ℤ → ℝ) *ᵥ x) ⬝ᵥ (G.map ((↑) : ℤ → ℝ) *ᵥ ((T a).map ((↑) : ℤ → ℝ) *ᵥ x)) ≤
        α ^ 2 * (x ⬝ᵥ (G.map ((↑) : ℤ → ℝ) *ᵥ x))) →
    ∃ P : Matrix (Fin d) (Fin d) ℤ, IsUnit P.det ∧
      (∀ i j, |((Pᵀ * G * P) i j : ℝ)| ≤ gramConst d * (G.det : ℝ)) ∧
      ∀ a i j, |((P⁻¹ * T a * P) i j : ℝ)| ≤ endConst d * α * Real.sqrt (G.det : ℝ)

def BoxCountStatement : Prop :=
  ∀ (k d : ℕ) (B : ℝ), 0 ≤ B →
    ({T : Fin k → Matrix (Fin d) (Fin d) ℤ | ∀ a i j, |((T a i j : ℤ) : ℝ)| ≤ B}.ncard : ℝ) ≤
      (2 * B + 1) ^ (k * (d * d))

def GramCountStatement : Prop :=
  ∀ (d : ℕ) (D : ℝ), 1 ≤ D →
    ∃ S : Finset (Matrix (Fin d) (Fin d) ℤ),
      (S.card : ℝ) ≤ (2 * gramConst d * D + 1) ^ (d * d) ∧
      ∀ G : Matrix (Fin d) (Fin d) ℤ, Gᵀ = G → (G.map ((↑) : ℤ → ℝ)).PosDef → (G.det : ℝ) ≤ D →
        ∃ P : Matrix (Fin d) (Fin d) ℤ, IsUnit P.det ∧ Pᵀ * G * P ∈ S

def DecoratedCountStatement : Prop :=
  ∀ (d k : ℕ) (α D : ℝ), 0 ≤ α → 1 ≤ D →
    ∃ S : Finset (Matrix (Fin d) (Fin d) ℤ × (Fin k → Matrix (Fin d) (Fin d) ℤ)),
      (S.card : ℝ) ≤ (2 * gramConst d * D + 1) ^ (d * d) *
        (2 * endConst d * α * Real.sqrt D + 1) ^ (k * (d * d)) ∧
      ∀ (G : Matrix (Fin d) (Fin d) ℤ) (T : Fin k → Matrix (Fin d) (Fin d) ℤ),
        Gᵀ = G → (G.map ((↑) : ℤ → ℝ)).PosDef → (G.det : ℝ) ≤ D →
        (∀ (a : Fin k) (x : Fin d → ℝ),
          ((T a).map ((↑) : ℤ → ℝ) *ᵥ x) ⬝ᵥ (G.map ((↑) : ℤ → ℝ) *ᵥ ((T a).map ((↑) : ℤ → ℝ) *ᵥ x)) ≤
            α ^ 2 * (x ⬝ᵥ (G.map ((↑) : ℤ → ℝ) *ᵥ x))) →
        ∃ P : Matrix (Fin d) (Fin d) ℤ, IsUnit P.det ∧ (Pᵀ * G * P, fun a => P⁻¹ * T a * P) ∈ S

end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

open Finset InnerProductSpace Matrix ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open scoped MatrixOrder ComplexOrder

variable {d : ℕ}

lemma norm_fB_sq (A B : Matrix (Fin d) (Fin d) ℝ) (hAB : A = Bᴴ * B) (x : Fin d → ℤ) :
    ‖fB B x‖ ^ 2 = (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ)) := by
  have h := Q_eq A B hAB x
  simp only [Q, polar] at h
  have h2 : ‖fB B x‖ ^ 2 = toReal x ⬝ᵥ (A *ᵥ toReal x) := by linarith
  exact h2

lemma det_toMatrix_sq (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    (((Pi.basisFun ℤ (Fin d)).toMatrix e).det : ℝ) ^ 2 = 1 := by
  have h := (Pi.basisFun ℤ (Fin d)).toMatrix_mul_toMatrix_flip e
  have hu : IsUnit ((Pi.basisFun ℤ (Fin d)).toMatrix e).det :=
    isUnit_iff_exists_inv.mpr ⟨(e.toMatrix (Pi.basisFun ℤ (Fin d))).det,
      by rw [← Matrix.det_mul, h, Matrix.det_one]⟩
  rcases Int.isUnit_iff.mp hu with h1 | h1 <;> rw [h1] <;> norm_num

lemma det_gram_fB (A B : Matrix (Fin d) (Fin d) ℝ) (hAB : A = Bᴴ * B)
    (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    (Matrix.gram ℝ fun i => fB B (e i)).det = A.det := by
  have hG : Matrix.gram ℝ (fun i => fB B (e i)) =
      (Matrix.of fun k j => ((e j k : ℤ) : ℝ))ᵀ * A * (Matrix.of fun k j => ((e j k : ℤ) : ℝ)) := by
    ext i j
    rw [Matrix.gram_apply, ← polar_eq A B hAB]
    simp only [polar, toReal, dotProduct, mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  have hE : (Matrix.of fun k j => ((e j k : ℤ) : ℝ)) =
      ((Pi.basisFun ℤ (Fin d)).toMatrix e).map (Int.cast : ℤ → ℝ) := by
    ext k j
    simp [Module.Basis.toMatrix_apply]
  have hsq := det_toMatrix_sq e
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hE, ← Int.cast_det]
  linear_combination A.det * hsq

theorem redGram_holds : RedGramStatement := by
  intro d A m D hA hm hmin hD
  obtain ⟨B, hAB⟩ : ∃ B : Matrix (Fin d) (Fin d) ℝ, A = Bᴴ * B := by
    refine ⟨CFC.sqrt A, ?_⟩
    have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
    have hsa : IsSelfAdjoint (CFC.sqrt A) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
    rw [← Matrix.star_eq_conjTranspose, hsa.star_eq, CFC.sqrt_mul_sqrt_self A h0]
  obtain ⟨e, hre⟩ := exists_red_of (fB B) (fun e => (li_basis A B hA hAB e).2) (hlow_of A B hA hAB)
  have hm' : ∀ i, m ≤ ‖fB B (e i)‖ ^ 2 := by
    intro i
    rw [norm_fB_sq A B hAB]
    exact hmin _ (e.ne_zero i)
  refine ⟨e, fun i => ?_, fun x i => ?_⟩
  · have h1 := red_norm_sq_le _ hre m D hm hm' (by rw [det_gram_fB A B hAB e]; exact hD) i
    rw [norm_fB_sq A B hAB] at h1
    exact h1
  · have h1 := red_coeff_sq_le _ hre m hm hm' (fun l => ((e.repr x l : ℤ) : ℝ)) i
    rw [← fB_expand B e x, norm_fB_sq A B hAB] at h1
    exact h1

end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

end
end
